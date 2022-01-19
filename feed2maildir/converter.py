import datetime
import json
import os
import random
import sys
import time
import hashlib

if sys.version[0] == '2':
    from HTMLParser import HTMLParser
else:
    from html.parser import HTMLParser

import dateutil.parser
import email.utils

from subprocess import Popen, PIPE, CalledProcessError

# Python 2.x compabitlity
if sys.version[0] == '2':
    FileNotFoundError = IOError

class HTMLStripper(HTMLParser):
    """Strips HTML off an string"""
    def __init__(self):
        self.reset()
        self.strict = False
        self.fed = []
        self.convert_charrefs = True
        self.numlinks = 0
        self.links = {}

    def handle_data(self, d):
        self.fed.append(d)

    def handle_starttag(self, tag, attrs):
        if tag == 'img':
            for attr in attrs:
                if attr[0] == 'src':
                    link = attr[1]
                    break;
            self.fed.append('[Image]: {}\n'.format(link))
        elif tag == 'a':
            for attr in attrs:
                if attr[0] == 'href':
                    self.links[self.numlinks] = attr[1]
        elif tag == 'li':
            self.fed.append('- ')

    def handle_endtag(self, tag):
        if tag == 'a':
            self.fed.append(' [{}]'.format(self.numlinks))
            self.numlinks += 1

    def get_data(self):
        out = ''.join(self.fed)
        if self.numlinks:
            out += '\n'
            for l in range(self.numlinks):
                out += '  [{}]: {}\n'.format(l, self.links[l])
        return out

class ExternalHTMLStripper:
    def __init__(self, strip_program):
        self.strip_program = strip_program
        self.reset()

    def feed(self, data):
        self.raw_data.append(data)

    def close(self):
        input_ = u''.join(self.raw_data).encode('utf-8')
        p = Popen(self.strip_program, stdin=PIPE, stdout=PIPE, shell=True)
        output, err = p.communicate(input_)
        if p.returncode != 0:
           # Note: feed2maildir supports Python 2.7+ and 3.2+ so we have to
           # print the stderr here. In Python 3.5+ we could add it as part
           # of the CalledProcessError exception.
           print(err)
           raise CalledProcessError(p.returncode, self.strip_program)

        self.stripped = output.decode('utf-8')

    def reset(self):
        self.raw_data = []
        self.stripped = u''

    def get_data(self):
        return self.stripped

class Converter:
    """Compares the already parsed feeds and converts new ones to maildir"""

    DB_SCHEME = 1
    TEMPLATE = u"""MIME-Version: 1.0
Date: {}
Subject: {}
From: {}
Content-Type: text/plain

[Feed2Maildir] Read the update here:
{}

{}
"""

    def __init__(self, db='~/.f2mdb', maildir='~/mail/feeds', strip=False,
                 strip_program=None, links=False, silent=False,
                 filter_duplicated=False):
        self.silent = silent
        self.maildir = os.path.expanduser(maildir)
        self.dbfile = os.path.expanduser(db)
        self.links = links
        self.strip = strip
        if self.strip and strip_program is None:
            self.stripper = HTMLStripper()
        elif self.strip:
            self.stripper = ExternalHTMLStripper(strip_program)

        self.load_database()
        self._filter_duplicated = filter_duplicated

    def load_database(self, dbfile=None):
        if not dbfile: # use own dbfile as default
            dbfile = self.dbfile
        try: # to read the database
            with open(self.dbfile, 'r') as f:
                dbdata = json.loads(f.read())
        except FileNotFoundError:
            dbdata = {}
        except ValueError:
            self.output('WARNING: database is malformed and will be ignored')
            dbdata = {}

        # latest database scheme:
        #   {
        #       'posts_seen': { hash : when seen },
        #       'feeds_checked' : { feedname : when updated },
        #       'feed2maildir_db_scheme': version
        #   }
        #
        # database scheme 0:
        #   { feedname : when updated }
        if 'feed2maildir_db_scheme' not in dbdata:
            db_scheme = 0
            posts_seen = {}
            feeds_last_time_checked = dbdata
        else:
            db_scheme = dbdata['feed2maildir_db_scheme']
            posts_seen = dbdata.pop('posts_seen', {})
            feeds_last_time_checked = dbdata.pop('feeds_last_time_checked', {})

        if db_scheme > Converter.DB_SCHEME:
            self.output('WARNING: database has a newer and unsupported scheme. Please upgrade feed2maildir. Abort.')
            sys.exit(1)
        elif db_scheme < Converter.DB_SCHEME:
            self.output('Note: database scheme (%i) will be upgraded to the latest scheme (%i)' % (db_scheme, Converter.DB_SCHEME))

        # We will upgrade the scheme if needed
        self.db_scheme = Converter.DB_SCHEME

        self.feeds_last_time_checked = feeds_last_time_checked

        # load a post hash and when the post was seen. Filter out
        # the posts that are too old (to maintain the database size under
        # control)
        # we use "naive" (local) datetime.
        now = datetime.datetime.now()
        expiration_days = 120   # quite arbitrary
        self.posts_seen = {post_hash:when for post_hash, when in posts_seen.items() if (now-self.mktime(when).replace(tzinfo=None)).days < expiration_days}

    def run(self):
        """Do a full run"""
        if self.feeds:
            self.check_maildir(self.maildir)
            old_feeds = self.feeds_last_time_checked
            self.news, self.newtimes = self.find_new(self.feeds, old_feeds)
            try:
                self.compose_emails()
            finally:
                self.update_database()

    def compose_emails(self):
        """Compose an email for each new post, optionally ignoring
        duplicated posts."""
        for newfeed, posts in self.news.items():
            for newpost in posts:
                updated = self.normalize_updated_date(newfeed, newpost)
                desc = self.normalize_description(newpost)

                if self.filter_duplicated(newfeed, newpost, updated, desc):
                    continue

                self.write(self.compose(newfeed, newpost, updated, desc))

    def load(self, feeds):
        """Load a list of feeds in feedparser-dict form"""
        self.feeds = feeds

    def find_new(self, feeds, db):
        """Find the new posts by comparing them to the db, return
        the new posts and the new update time for the feeds read."""
        new = {}
        newtimes = {}
        for feed in feeds:
            feedname = feed.feed.title
            feedaliasname = feed.feed_alias_name
            feedup = self.feed_update_time(feed)
            try: # to localize the timezone
                feedup = feedup.astimezone(dateutil.tz.tzutc())
            except: # it is naive, force UTC
                feedup = feedup.replace(tzinfo=dateutil.tz.tzutc())
            try: # to find the old update time in the db
                oldtime = self.mktime(db[feedname]).astimezone(
                            dateutil.tz.tzutc())
            except KeyError: # it is not there
                oldtime = None
            if oldtime and not oldtime.tzinfo: # force UTC
                oldtime = oldtime.replace(tzinfo=dateutil.tz.tzutc())
            # print(feedname, feedup.tzinfo)
            if not oldtime or oldtime < feedup:
                for post in feed.entries:
                    feedtime = self.post_update_time(post)
                    try: # to localize the timezone
                        feedtime = feedtime.astimezone(dateutil.tz.tzutc())
                    except: # it is naive
                        feedtime = feedtime.replace(tzinfo=dateutil.tz.tzutc())
                    if not oldtime or oldtime < feedtime:
                        try: # to append the post the the feed-list
                            new[feedaliasname].append(post)
                        except: # it is the first one, make a new list
                            new[feedaliasname] = [post, ]

            newtimes[feedname] = feedup.strftime('%Y-%m-%d %H:%M:%S %Z')

        return new, newtimes

    def update_database(self, dbfile=None):
        """Update the database, optionally saving it in an
        alternative file."""
        assert self.db_scheme == Converter.DB_SCHEME

        if not dbfile: # use own dbfile as default
            dbfile = self.dbfile

        db = {
                'posts_seen': {h:w for h, w in self.posts_seen.items()},
                'feeds_last_time_checked': self.newtimes,
                'feed2maildir_db_scheme': Converter.DB_SCHEME
                }

        try: # to write the new database
            with open(dbfile, 'w') as f:
                f.write(json.dumps(db))
        except:
            self.output('WARNING: failed to write the new database')

    def post_update_time(self, post):
        """Try to get the post time"""
        try:
            return self.mktime(post.updated)
        except AttributeError:
            try:
                return self.mktime(post.published)
            except AttributeError: # last resort
                return datetime.datetime.now()

    def find_update_time(self, feed):
        """Find the last updated post in a feed"""
        times = []
        for post in feed.entries:
            times.append(self.post_update_time(post))
        return sorted(times)[-1]

    def feed_update_time(self, feed):
        # find the newest post and get its time
        newest_post_time = self.find_update_time(feed)
        try: # to get the update time from the feed itself
            feed_time = self.mktime(feed.feed.updated)
        except:
            return newest_post_time
        # Some feeds like Youtube do not update the feed's update time.
        # The value 'feed_time' is a valid date, but outdated so
        # we have to compare it with the posts' times and get the latest.
        return max(newest_post_time, feed_time)

    def check_maildir(self, maildir):
        """Check access to the maildir and try to create it if not present"""
        mdirs = ('', '/tmp', '/new', '/cur')
        for mdir in mdirs:
            fullname = maildir + mdir
            if not os.access(fullname, os.W_OK):
                try: # to make the maildirs
                    os.mkdir(fullname)
                except:
                    sys.exit('ERROR: accessing "{}" failed'.format(fullname))

    def post_description(self, post):
        try:
            return post.content[0].value
        except:
            return post.description

    def normalize_updated_date(self, feed, post):
        """Return when the post was updated as RFC 2822 format.
        If the post has not this date specified, assume "now"
        as the updated date."""
        try: # to get the update/publish time from the post
            updated = post.updated
            updated = dateutil.parser.parse(updated)
        except: # the property is not set, use now()
            updated = datetime.datetime.now()


        # XXX TODO
        # This is a hack to *delay* the emails from LWN that are paid
        # to be shown only when the full article is available. Typically
        # 3 weeks later.
        if feed == 'LWN' and post.title.startswith('[$]'):
            _3weeks = datetime.timedelta(days=21)
            updated += _3weeks

        # convert the time to RFC 2822 format, expected by MUA programs
        d = time.mktime(updated.timetuple())
        updated = email.utils.formatdate(d, usegmt=True)

        return updated

    def normalize_description(self, post):
        """Return the description of the post after the stripping process."""
        desc = ''
        if not self.links:
            desc = self.post_description(post)
            if self.strip:
                self.stripper.feed(desc)
                self.stripper.close()
                desc = self.stripper.get_data()
                self.stripper.reset()
            else:
                desc = post.description

        return desc

    def compose(self, feed, post, updated, desc):
        """Compose the mail using the tempate"""
        return self.TEMPLATE.format(updated, post.title.replace('\n', ' - '), feed, post.link,
                                    desc)

    def hash_post(self, feed, post, desc):
        """Return a MD5 sum of the feed and post's link
        to have a single identifier."""
        h = hashlib.md5()

        h.update(feed.encode('utf8'))
        h.update(post.link.encode('utf8'))

        return h.hexdigest()

    def filter_duplicated(self, feed, post, updated, desc):
        """Filter duplicated posts based on their links even
        if their updated date say that their are fresh posts.
        Return if the post was filtered or not.
        If this feature is not enabled, return False always."""
        if feed not in self._filter_duplicated:
            return False

        h = self.hash_post(feed, post, desc)
        is_duplicated = h in self.posts_seen

        assert isinstance(updated, str) # it is already serialized

        # probably not needed but to be consistent: we use the same
        # format for the date serialization than the used for the date
        # of the feeds
        self.posts_seen[h] = self.mktime(updated).strftime('%Y-%m-%d %H:%M:%S %Z')

        return is_duplicated

    def write(self, message):
        """Take a message and write it to a mail"""
        rand = str(random.randint(10000, 99999))
        dt = str(datetime.datetime.now())
        pid = str(os.getpid())
        host = os.uname()[1]
        name = u'{}/new/{}{}{}{}'.format(self.maildir, rand, dt, pid, host)
        try: # to write out the message
            with open(name, 'w') as f:
                # We can thank the P2/P3 unicode madness for this...
                if sys.version[0] == '2':
                    f.write(str(message.encode('utf8')))
                else:
                    f.write(message)
        except:
            self.output('WARNING: failed to write message to file')

    def mktime(self, arg):
        """Make a datetime object from a time string"""
        return dateutil.parser.parse(arg)

    def output(self, arg):
        if not self.silent:
            print(arg)

