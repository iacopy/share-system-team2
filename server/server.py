#!/usr/bin/env python
# -*- coding: utf-8 -*-
import ConfigParser
import os
import json
import shutil
import logging
import datetime
import argparse
import hashlib
import time
import string
import re

join = os.path.join
normpath = os.path.normpath
abspath = os.path.abspath

from flask import Flask, make_response, request, abort, jsonify
from flask.ext.httpauth import HTTPBasicAuth
from flask.ext.restful import Resource, Api
from flask.ext.mail import Mail, Message
from werkzeug import secure_filename
from passlib.hash import sha256_crypt
import passwordmeter
import peewee


__title__ = 'PyBOX'

# HTTP STATUS CODES
HTTP_OK = 200
HTTP_CREATED = 201
HTTP_ACCEPTED = 202
HTTP_BAD_REQUEST = 400
HTTP_UNAUTHORIZED = 401
HTTP_FORBIDDEN = 403
HTTP_NOT_FOUND = 404
HTTP_CONFLICT = 409

FILE_ROOT = 'filestorage'

URL_PREFIX = '/API/V1'
SERVER_DIRECTORY = os.path.dirname(__file__)

USERDATA_FILENAME = 'userdata.json'
DATABASE_FILENAME = 'users_data.db'
PG_DATABASE = 'postgres'
PG_HOST = 'localhost'
PG_PORT = '5433'
PG_USR = 'postgres'

PASSWORD_RECOVERY_EMAIL_TEMPLATE_FILE_PATH = os.path.join(SERVER_DIRECTORY,
                                                          'password_recovery_email_template.txt')
SIGNUP_EMAIL_TEMPLATE_FILE_PATH = os.path.join(SERVER_DIRECTORY,
                                               'signup_email_template.txt')

USER_ACTIVATION_TIMEOUT = 60 * 60 * 24 * 3 * 10000 # expires after 3 days
USER_RECOVERPASS_TIMEOUT = 60 * 60 * 24 * 2 * 10000  # expires after 2 days (arbitrarily)

# json/dict key to access to the user directory snapshot:
SNAPSHOT = 'files'
LAST_SERVER_TIMESTAMP = 'server_timestamp'
PWD = 'password'
USER_CREATION_TIME = 'creation_timestamp'
DEFAULT_USER_DIRS = ('Misc', 'Music', 'Photos', 'Projects', 'Work')
USER_IS_ACTIVE = 'active'
USER_CREATION_DATA = 'activation_data'

UNWANTED_PASS = 'words'


class ServerError(Exception):
    pass


class ServerConfigurationError(ServerError):
    pass


class ServerInternalError(ServerError):
    """
    Custom exception to raise programming errors
    (i.e. when unexpected conditions are found).
    """
    pass


# Logging configuration
# =====================
LOG_FILENAME = 'log/server.log'
if not os.path.isdir('log'):
    os.mkdir('log')

logger = logging.getLogger('Server log')

# It's useful to log all messages of all severities to a text file while simultaneously
# logging errors or above to the console. You set this up simply configuring the appropriate handlers.
# Create file handler which logs even debug messages:
file_handler = logging.FileHandler(LOG_FILENAME)
file_handler.setLevel(logging.DEBUG)
# Create console handler with a higher log level:
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.WARNING)  # changeable from command line passing verbosity option or --verbose or --debug
logger.addHandler(file_handler)
logger.addHandler(console_handler)

# First log message
launched_or_imported = {True: 'launched', False: 'imported'}[__name__ == '__main__']
logger.info('-' * 79)
logger.info('Server {} at {}'.format(launched_or_imported, datetime.datetime.now().isoformat(' ')))

# Server initialization
# =====================
app = Flask(__name__)
app.testing = __name__ != '__main__'  # Reasonable assumption?

userdata = {}

if app.testing:
    logger.debug('Using SqliteDatabase:memory:')
    database = peewee.SqliteDatabase(':memory:')
else:
    logger.debug('Using postgres database \'{}\''.format(PG_DATABASE))
    # http://peewee.readthedocs.org/en/latest/peewee/database.html#multi-threaded-applications
    database = peewee.PostgresqlDatabase(PG_DATABASE, host=PG_HOST, user=PG_USR, port=PG_PORT)
database.connect()

# if True, you can see the exception traceback, suppress the sending of emails, etc.
EMAIL_SETTINGS_FILEPATH = join(os.path.dirname(__file__),
                               ('email_settings.ini', 'email_settings.ini.example')[app.testing])


# A regular expression to check if an email address is valid or not.
# WARNING: it seems a not 100%-exhaustive email address validation.
# source: http://www.regular-expressions.info/email.html (modified)

EMAIL_REG_OBJ = re.compile(r'^[A-Z0-9]'  # the first char must be alphanumeric (no dots etc...)
                           r'[A-Z0-9._%+-]+'  # allowed characters in the "local part"
                           # NB: many email providers allow letters, numbers, and '.', '-' and '_' only.
                           # GMail even allows letters, numbers and dots only (no '-' nor underscores).
                           r'[A-Z0-9_-]'  # no dots before the '@'
                           r'@'
                           r'[A-Z0-9.-]+'  # domain part before the last dot ('.' and '-' allowed too)
                           r'\.[A-Z]{2,4}$',  # domain extension: 2, 3 or 4 letters
                           re.IGNORECASE | re.VERBOSE)

api = Api(app)
auth = HTTPBasicAuth()


def validate_email(address):
    """
    Validate an email address according to http://www.regular-expressions.info/email.html.
    In addition, at most one '.' before the '@' and no '..' in the domain part are allowed.
    :param address: str
    :return: bool
    """
    if not re.search(EMAIL_REG_OBJ, address) or '..' in address:
        return False
    else:
        return True


def update_passwordmeter_terms(terms_file):
    """
    Added costume terms list into passwordmeter from words file
    :return:
    """
    costume_password = set()
    try:
        with open(terms_file, 'rb') as terms_file:
            for term in terms_file:
                costume_password.add(term)
    except IOError:
        logging.info('Impossible to load file ! loaded default setting.')
    else:
        passwordmeter.common10k = passwordmeter.common10k.union(costume_password)
    finally:
        del costume_password


def _read_file(filename):
    """
    This function reads and returns the content of the file.
    """
    with open(filename, 'rb') as f:
        content = f.read()
    return content


def check_path(path, username):
    """
    Check that a path don't fall in other user directories or upper.
    Examples:

    >>> check_path('Photos/myphoto.jpg', 'pippo')
    True
    >>> check_path('Photos/../../ciao.txt', 'paperino')
    False
    """
    path = os.path.abspath(join(FILE_ROOT, username, path))
    root = os.path.abspath(join(FILE_ROOT, username))
    if root in path:
        return True
    return False


def userpath2serverpath(username, path=''):
    """
    Given an username and its relative path, return the
    corresponding path in the server. If the path is empty,
    return the user path directory in the server.
    :param username: str
    :param path: str
    :return: str
    """
    return os.path.realpath(os.path.join(FILE_ROOT, username, path))


def now_timestamp():
    """
    Return the current server timestamp as an int.
    :return: long
    """
    return long(time.time()*10000)


def file_timestamp(filepath):
    """
    Return the long of last modification timestamp of <filepath> (i.e. long(os.path.getmtime(filepath))).

    :param filepath: str
    :return: long
    """

    return long(os.path.getmtime(filepath)*10000)


def _encrypt_password(password):
    """
    Return the password encrypted as a string.
    :rtype : str
    """
    return sha256_crypt.encrypt(password)


def init_root_structure():
    """
    Create the file root directory if needed.
    :return: int
    """
    if not os.path.isdir(FILE_ROOT):
        os.mkdir(FILE_ROOT)
        return 1
    else:
        return 0


def init_user_directory(username, default_dirs=DEFAULT_USER_DIRS):
    """
    Create the default user directory.
    :param username: str
    :param default_dirs: dict
    """
    dirpath = join(FILE_ROOT, username)
    if os.path.isdir(dirpath):
        shutil.rmtree(dirpath)
        logger.info('"{}" directory removed'.format(dirpath))
    os.makedirs(dirpath)

    welcome_file = join(dirpath, 'WELCOME')
    with open(welcome_file, 'wb') as fp:
        fp.write('Welcome to %s, %s!\n' % (__title__, username))

    for dirname in default_dirs:
        subdirpath = join(dirpath, dirname)
        filepath = join(subdirpath, '{}.txt'.format(dirname))
        os.mkdir(subdirpath)
        # Create a default file for each default directory
        # beacuse wee need files to see the directories.
        with open(filepath, 'wb') as fp:
            fp.write('{} {}\n'.format(username, dirname))
    logger.info('{} created'.format(dirpath))
    return compute_dir_state(dirpath)


def load_userdata():
    data = {}
    try:
        with open(USERDATA_FILENAME, 'rb') as fp:
            data = json.load(fp, 'utf-8')
    except IOError:
        # If the user data file does not exists, don't raise an exception.
        # (the file will be created with the first user creation)
        pass
    logger.debug('Registered user(s): {}'.format(', '.join(data.keys())))
    logger.info('{:,} registered user(s) found'.format(len(data)))
    return data


def save_userdata():
    """
    Save module level <userdata> dict to disk as json.
    :return: None
    """
    with open(USERDATA_FILENAME, 'wb') as fp:
        json.dump(userdata, fp, 'utf-8', indent=4)
    logger.info('Saved {:,} users'.format(len(userdata)))


def reset_userdata():
    """
    Clear userdata dictionary.
    """
    try:
        File.drop_table()
    except peewee.OperationalError:
        pass
    try:
        User.drop_table()
    except peewee.OperationalError:
        pass

    database.create_tables([User, File])



@auth.verify_password
def verify_password(username, password):
    """
    We redefine this function to check password with the encrypted one.
    """
    if not username:
        # Warning/info?
        return False

    try:
        user = User.get(User.username == username)
    except peewee.DoesNotExist:
        logger.info('User \'{}\' does not exist!'.format(username))
        res = False
    else:
        stored_pw = user.encrypted_password
        assert stored_pw is not None, 'Server error: user data must contain a password!'
        res = sha256_crypt.verify(password, stored_pw)
    return res


def activate_user(username):
    """
    Handle the activation of an existing user(with flag active: True).
    """
    logger.debug('Activating user...')

    temp = init_user_directory(username)
    last_server_timestamp, dir_snapshot = temp[LAST_SERVER_TIMESTAMP], temp[SNAPSHOT]

    # TODO: use with
    user = User.get(User.username == username)
    user.active = True
    user.activation_code = ''
    user.activation_code_timestamp = 0
    user.server_timestamp = last_server_timestamp
    user.save()

    for file_path, values in dir_snapshot.items():
        File.create(owner=user,
                    path=file_path,
                    timestamp=values[0],
                    md5=values[1])


    response = 'User "{}" activated.\n'.format(username), HTTP_OK

    logger.debug(response)
    return response


def create_user(username, password, activation_code):
    """
    Handle the creation of a new user(with flag active: False).
    User's password is encrypted here.
    """
    logger.debug('Creating user...')
    if username and password:
        enc_pass = _encrypt_password(password)
        creation_timestamp = now_timestamp()

        User.create(username=username,
                    creation_timestamp=creation_timestamp,
                    active=False,
                    encrypted_password=enc_pass,
                    server_timestamp=creation_timestamp,  # ?
                    activation_code=activation_code,
                    activation_code_timestamp=creation_timestamp,
                    )

        response = 'User activation email sent to {}'.format(username), HTTP_CREATED
    else:
        raise ServerInternalError('Unexpected error: username and password must not be empty here!!!\n'
                                  'username: "%"" - password: "%"' % (username, password))

    logger.debug(response)
    return response


def configure_email():
    """
    Configure Flask Mail from the email_settings.ini in place. Return a flask.ext.mail.Mail instance.
    """
    # Relations between Flask configuration keys and settings file fields.
    keys_tuples = [
        ('MAIL_SERVER', 'smtp_address'),  # the address of the smtp server
        ('MAIL_PORT', 'smtp_port'),  # the port of the smtp server
        ('MAIL_USERNAME', 'smtp_username'),  # the username of the smtp server (if required)
        ('MAIL_PASSWORD', 'smtp_password'),  # the password of the smtp server (if required)
    ]

    cfg = ConfigParser.ConfigParser()
    cfg.read(EMAIL_SETTINGS_FILEPATH)
    for flask_key, file_key in keys_tuples:
        value = cfg.get('email', file_key)
        if flask_key == 'MAIL_PORT':
            value = int(value)
        app.config[flask_key] = value

    return Mail(app)


def send_email(subject, sender, recipients, text_body):
    """
    Sent an email and return the Message instance of sent email.

    :param subject: str
    :param sender: str
    :param recipients: list
    :param text_body: str
    :return: Message
    """
    msg = Message(subject, sender=sender, recipients=recipients)
    msg.body = text_body
    mail.send(msg)
    return msg


database_proxy = peewee.Proxy()


class BaseModel(peewee.Model):
    class Meta:
        database = database_proxy


class User(BaseModel):
    username = peewee.CharField(unique=True)  # username == email
    creation_timestamp = peewee.BigIntegerField()
    active = peewee.BooleanField(default=False)
    encrypted_password = peewee.CharField()

    # TODO: to reduce the number of columns and disk space, just use 2 fields instead of 4
    # for the current token (activation_code or recoverpass_code, inferred by the user's status)
    activation_code = peewee.CharField(max_length=32)  # e.g. bfce9ec2d61e397cabce646bbe617fb5
    activation_code_timestamp = peewee.BigIntegerField()
    recoverpass_code = peewee.CharField(max_length=32, default='')
    recoverpass_code_timestamp = peewee.BigIntegerField(default=0)
    server_timestamp = peewee.BigIntegerField(default=0)

    def __repr__(self):
        return self.username


class File(BaseModel):
    owner = peewee.ForeignKeyField(User, related_name='files')

    path = peewee.CharField()
    md5 = peewee.CharField()
    timestamp = peewee.BigIntegerField()


database_proxy.initialize(database)

try:
    database_proxy.create_tables([User, File])
except peewee.ProgrammingError:
    logger.debug('Tables already exist')
    database_proxy.rollback()  # needed in PostgreSQL


class Users(Resource):
    @staticmethod
    def _clean_inactive_users():
        """
        Remove expired inactive users (users whose activation time is expired)
        and return a list of them.
        :return: list
        """
        now_ts = now_timestamp()

        # Use select query instead of delete query in order to return the deleted usernames.
        users_to_be_deleted = User.select().where(
            (User.active == False),
            (now_ts - User.activation_code_timestamp > USER_ACTIVATION_TIMEOUT)
        )

        # Delete users one by one
        for user in users_to_be_deleted:
            user.delete_instance()

        return [user.username for user in users_to_be_deleted]

    @auth.login_required
    def get(self, username):
        """
        Show logged user details.
        """
        logged = auth.username()
        if username == logged:
            # The user exists since he's authenticated.
            user = User.get(User.username == username)
            creation_timestamp = user.creation_timestamp
            if creation_timestamp:
                time_str = time.strftime('%Y-%m-%d at %H:%M:%S', time.localtime(creation_timestamp/10000.0))
            else:
                time_str = '<unknown time>'
            # TODO: return json?
            response = 'You joined on {}.'.format(time_str), HTTP_OK
            return response
        else:
            if app.debug:
                if username == '__all__':
                    # Easter egg to see a list of active and pending (inactive) users.
                    logger.warn('WARNING: showing the list of all users (debug mode)!!!')

                    users_select = User.select()
                    if users_select.count():
                        active_users, inactive_users = [], []
                        for user in users_select:
                            if user.active:
                                active_users.append(user)
                            else:
                                inactive_users.append(user)

                        active_users_str = ', '.join(active_users)
                        inactive_users_str = ', '.join(inactive_users)
                        resp_str = 'Activated users: {}. Inactive users: {}'.format(active_users_str, inactive_users_str)
                    else:
                        resp_str = 'neither registered nor pending users'
                    return resp_str, HTTP_OK
                else:
                    logger.warn('WARNING: showing {}\'s info (debug mode)!!!'.format(username))
                    try:
                        user = User.get(User.username == username)
                    except peewee.DoesNotExist:
                        response = 'The user {} does not exist.'.format(username), HTTP_NOT_FOUND
                    else:
                        creation_timestamp = user.creation_timestamp
                        if creation_timestamp:
                            time_str = time.strftime('%Y-%m-%d at %H:%M:%S', time.localtime(creation_timestamp))
                        else:
                            time_str = '<unknown time>'
                        response = 'User {} joined on {}.'.format(username, time_str), HTTP_OK
                return response

            abort(HTTP_FORBIDDEN)

    def post(self, username):
        """
        A not-logged user is asking to register himself.
        NB: username must be a valid email address.
        """
        if not validate_email(username):
            return 'Error: username must be a valid email address!', HTTP_BAD_REQUEST

        password = request.form['password']
        if not password:
            return 'Error: the password mustn\'t be empty', HTTP_BAD_REQUEST

        strength, improvements = passwordmeter.test(password)
        if strength <= 0.5:
            return improvements, HTTP_FORBIDDEN
        activation_code = os.urandom(16).encode('hex')

        # Composing email
        subject = '[{}] Confirm your email address'.format(__title__)
        sender = 'donotreply@{}.com'.format(__title__)
        recipients = [username]
        text_body_template = string.Template(_read_file(SIGNUP_EMAIL_TEMPLATE_FILE_PATH))
        values = dict(code=activation_code,
                      email=username,
                      appname=__title__,
                      )
        text_body = text_body_template.substitute(values)

        send_email(subject, sender, recipients, text_body)

        try:
            User.get(User.username == username)
        except peewee.DoesNotExist:
            return create_user(username, password, activation_code)
        else:
            # If an user is pending for activation, it can't be another one with the same name
            # asking for registration.
            return 'Error: username \'{}\' already exists!'.format(username), HTTP_CONFLICT

    def put(self, username):
        """
        Activate user using activation code sent by email, or reset its password.
        """
        # Pending users cleanup
        expired_pending_users = self._clean_inactive_users()
        logging.info('Expired pending users: {}'.format(expired_pending_users))

        users = User.select().where(User.username == username)
        n_of_username = users.count()
        if n_of_username:
            assert n_of_username == 1, 'Duplicated username: found {} \'{}\'!!!'.format(n_of_username, username)
            user = users[0]
            if user.active:
                # User active -> Password recovery/reset
                try:
                    new_password = request.form[PWD]
                except KeyError:
                    logger.info('password parameter missing! {}'.format(request.form))
                    abort(HTTP_BAD_REQUEST)

                strength, improvements = passwordmeter.test(new_password)
                if strength <= 0.5:
                    return improvements, HTTP_FORBIDDEN

                request_recoverpass_code = request.form['recoverpass_code']
                recoverpass_code = user.recoverpass_code
                recoverpass_timestamp = user.recoverpass_code_timestamp

                if recoverpass_code:  # The user is actually changing its password
                    if request_recoverpass_code == recoverpass_code and \
                            (now_timestamp() - recoverpass_timestamp < USER_RECOVERPASS_TIMEOUT):
                        user.recoverpass_code = ''
                        user.encrypted_password = _encrypt_password(new_password)

                        user.save()
                        return 'Password changed succesfully', HTTP_OK
                # NB: old generated tokens are refused, but, currently, they are not removed from userdata.
                return 'Invalid code', HTTP_NOT_FOUND
            else:
                # User inactive -> activation
                activation_code = request.form['activation_code']
                logger.debug('Got activation code: {}'.format(activation_code))
                logger.debug('Activating user \'{}\''.format(username))
                #if activation_code == user_data[USER_CREATION_DATA]['activation_code']:
                if activation_code == user.activation_code:
                    # Actually activate user
                    return activate_user(username)
                else:
                    logger.info('Wrong activation code: {} vs {}'.format(activation_code,
                                                                          user.activation_code))
                    abort(HTTP_NOT_FOUND)
        else:
            # Not-existing user --> 404 (OR create it in debug mode with a backdoor)
            #### DEBUG-MODE BACKDOOR ####
            # Shortcut to create an user skipping the email confirmation (valid in debug mode only!).
            activation_code = request.form['activation_code']
            if app.debug and activation_code == 'BACKDOOR':
                password = 'debug-password'
                logger.warn('WARNING: Creating user "{}" (password="{}") '
                            'without email confirmation via backdoor!!!'.format(username, password))
                return create_user(username, password, activation_code)
            #### DEBUG-MODE BACKDOOR ####

            return 'Error: username not found!\n', HTTP_NOT_FOUND

    @auth.login_required
    def delete(self, username):
        """
        Delete all logged user's files and data. Remove also inactive users.
        The same user won't more log in, but it can be recreated with the signup procedure.
        """
        logged = auth.username()

        if username != logged:
            # I mustn't delete other users!
            abort(HTTP_FORBIDDEN)

        user = User.get(User.username == username)

        if user.active:
            # Remove also the user's folder
            shutil.rmtree(userpath2serverpath(username))

        # Remove user row and dependent rows on File table
        # (recursive = True set cascade on delete)
        user.delete_instance(recursive=True)
        return 'User "{}" removed.\n'.format(username), HTTP_OK


class UsersRecoverPassword(Resource):
    """
    This class handles the recovering of a lost user's password by changing it.

    Use case: the user has forgotten its password and wants to recover it.
    NB: recover the old password is not even possible since it's stored encrypted.
    """
    def post(self, username):
        """
        Handle the request for change the user's password
        by sending a 'recoverpass' token to its email address.
        """
        recoverpass_code = os.urandom(16).encode('hex')

        # The password reset must be called from an active or inactive user
        try:
            user = User.get(User.username == username)
        except peewee.DoesNotExist:
            abort(HTTP_NOT_FOUND)

        # Composing email
        subject = '[{}] Password recovery'.format(__title__)
        sender = 'donotreply@{}.com'.format(__title__)
        recipients = [username]
        text_body_template = string.Template(_read_file(PASSWORD_RECOVERY_EMAIL_TEMPLATE_FILE_PATH))
        values = dict(code=recoverpass_code,
                      email=username,
                      appname=__title__,
                      )
        text_body = text_body_template.substitute(values)

        send_email(subject, sender, recipients, text_body)

        # create or update 'recoverpass_data' key.
        user.recoverpass_code = recoverpass_code
        user.recoverpass_code_timestamp = now_timestamp()
        user.save()

        return 'Reset email sent to {}'.format(username), HTTP_ACCEPTED


class Actions(Resource):
    @auth.login_required
    def post(self, cmd):
        username = auth.username()
        methods = {'delete': self._delete,
                   'copy': self._copy,
                   'move': self._move,
                   }
        try:
            resp = methods[cmd](username)
        except KeyError:
            abort(HTTP_NOT_FOUND)
        else:
            save_userdata()
            return resp

    def _delete(self, username):
        """
        Delete a file for a given <filepath>, and return the current server timestamp in a json.
        json format: {LAST_SERVER_TIMESTAMP: int}
        """
        filepath = request.form['filepath']

        if not check_path(filepath, username):
            abort(HTTP_FORBIDDEN)

        abspath = os.path.abspath(join(FILE_ROOT, username, filepath))

        try:
            os.remove(abspath)
        except OSError:
            # This error raises when the file is missing
            abort(HTTP_NOT_FOUND)
        self._clear_dirs(os.path.dirname(abspath), username)

        # file deleted, last_server_timestamp is set to current timestamp
        last_server_timestamp = now_timestamp()
        user = User.get(User.username == username)

        # server_timestamp is set to current timestamp
        upd_user_query = User.update(server_timestamp=last_server_timestamp).where(User.username == username)
        upd_user_query.execute()

        # delete record from File table
        del_file_query = File.delete().where((File.owner == user.id) & (File.path == filepath))
        del_file_query.execute()

        return jsonify({LAST_SERVER_TIMESTAMP: last_server_timestamp, 'filepath': filepath})

    def _copy(self, username):
        """
        Copy a file from a given source path to a destination path and return the current server timestamp
        in a json file.jso
        userdata[username]n format: {LAST_SERVER_TIMESTAMP: int}
        """

        src = request.form['src']
        dst = request.form['dst']
        server_src = userpath2serverpath(username, src)
        server_dst = userpath2serverpath(username, dst)

        if not (check_path(src, username) or check_path(dst, username)):
            abort(HTTP_FORBIDDEN)

        if os.path.isfile(server_src):
            if not os.path.exists(os.path.dirname(server_dst)):
                os.makedirs(os.path.dirname(server_dst))
            shutil.copy(server_src, server_dst)
        else:
            abort(HTTP_NOT_FOUND)

        last_server_timestamp = file_timestamp(server_dst)
        user = User.get(User.username == username)
        # update server timestamp
        upd_user_query = User.update(server_timestamp=last_server_timestamp).where(User.username == username)
        upd_user_query.execute()
        # update path timestamp
        upd_file_query = File.update(timestamp=last_server_timestamp).where(File.path == dst)
        upd_file_query.execute()

        _, md5 = userdata[username]['files'][normpath(src)]
        userdata[username][LAST_SERVER_TIMESTAMP] = last_server_timestamp
        userdata[username]['files'][normpath(dst)] = [last_server_timestamp, md5]
        save_userdata()
        return jsonify({LAST_SERVER_TIMESTAMP: last_server_timestamp})

    def _move(self, username):
        """
        Move a file from a given source path to a destination path, and return the current server timestamp in a json.
        json format: {LAST_SERVER_TIMESTAMP: int}
        """
        src = request.form['src']
        dst = request.form['dst']
        server_src = userpath2serverpath(username, src)
        server_dst = userpath2serverpath(username, dst)

        if not (check_path(src, username) or check_path(dst, username)):
            abort(HTTP_FORBIDDEN)

        if os.path.isfile(server_src):
            if not os.path.exists(os.path.dirname(server_dst)):
                os.makedirs(os.path.dirname(server_dst))
            shutil.move(server_src, server_dst)
        else:
            abort(HTTP_NOT_FOUND)
        self._clear_dirs(os.path.dirname(server_src), username)

        last_server_timestamp = now_timestamp()

        _, md5 = userdata[username]['files'][normpath(src)]
        userdata[username][LAST_SERVER_TIMESTAMP] = last_server_timestamp
        userdata[username]['files'].pop(normpath(src))
        userdata[username]['files'][normpath(dst)] = [last_server_timestamp, md5]
        save_userdata()
        return jsonify({LAST_SERVER_TIMESTAMP: last_server_timestamp})

    def _clear_dirs(self, path, root):
        """
        Recursively removes all the empty directories that exists after the remotion of a file
        """

        path_to_clear, clean = os.path.split(path)
        path_to_storage, storage = os.path.split(path_to_clear)
        if clean == root and storage == FILE_ROOT:
            return
        try:
            os.rmdir(path)
        except OSError:
            return
        self._clear_dirs(path_to_clear, root)


def calculate_file_md5(fp, chunk_len=2 ** 16):
    """
    Return the md5 digest of the file content of file_path as a string
    with only hexadecimal digits.
    :fp: file (an open file object)
    :chunk_len: int (number of file bytes read per cycle - default = 2^16)
    """
    h = hashlib.md5()
    while True:
        chunk = fp.read(chunk_len)
        if chunk:
            h.update(chunk)
        else:
            break
    res = h.hexdigest()
    fp.seek(0)
    return res


def compute_dir_state(root_path):  # TODO: make function accepting just an username instead of an user root_path.
    """
    Walk on root_path returning the directory snapshot in a dict (dict keys are identified by this 2 constants:
    LAST_SERVER_TIMESTAMP and SNAPSHOT)

    :param root_path: str
    :return: dict.
    """
    snapshot = {}
    last_timestamp = now_timestamp()
    for dirpath, dirs, files in os.walk(root_path):
        for filename in files:
            filepath = join(dirpath, filename)

            # Open file and calculate md5.
            try:
                with open(filepath, 'rb') as fp:
                    md5 = calculate_file_md5(fp)
            except OSError as err:
                logging.warn('calculate_file_md5("{}") --> {}'.format(filepath, err))
            else:
                snapshot[filepath[len(root_path) + 1:]] = [last_timestamp, md5]
    state = {LAST_SERVER_TIMESTAMP: last_timestamp,
             SNAPSHOT: snapshot}
    return state


class Files(Resource):
    """
    Class that handle files as web resources.
    """

    @auth.login_required
    def get(self, path=''):
        """
        Download an authenticated user file from server, if <path> is not empty,
        otherwise get a server snapshot of user directory.
        <path> is the path relative to the user local directory.
        :param path: str
        """
        logger.debug('Files.get({})'.format(repr(path)))
        username = auth.username()
        user_rootpath = join(FILE_ROOT, username)

        if path:
            # Download the file specified by <path>.
            dirname = join(user_rootpath, os.path.dirname(path))

            if not check_path(path, username):
                abort(HTTP_FORBIDDEN)

            if not os.path.exists(dirname):
                abort(HTTP_NOT_FOUND)
            s_filename = secure_filename(os.path.split(path)[-1])

            try:
                response = make_response(_read_file(join(FILE_ROOT, username, path)))
            except IOError:
                response = 'Error: file {} not found.\n'.format(path), HTTP_NOT_FOUND
            else:
                response.headers['Content-Disposition'] = 'attachment; filename=%s' % s_filename
        else:
            # If path is not given, return the snapshot of user directory.
            logger.debug('launch snapshot of {}...'.format(repr(user_rootpath)))
            snapshot = userdata[username][SNAPSHOT]
            logger.info('snapshot returned {:,} files'.format(len(snapshot)))
            last_server_timestamp = userdata[username][LAST_SERVER_TIMESTAMP]
            response = jsonify({LAST_SERVER_TIMESTAMP: last_server_timestamp,
                                SNAPSHOT: snapshot})
        logging.debug(response)
        return response

    def _get_dirname_filename(self, path):
        """
        Return dirname(directory name) and filename(file name) for a given path to complete
        post and put methods
        """
        username = auth.username()
        dirname = os.path.dirname(path)
        dirname = (join(FILE_ROOT, username, dirname))
        filename = os.path.split(path)[-1]

        if not check_path(dirname, username):
            abort(HTTP_FORBIDDEN)

        return dirname, filename

    def _update_user_path(self, username, path, md5):
        """
        Make all needed updates to <userdata> (dict and disk) after a post or a put.
        Return the last modification int timestamp of written file.
        :param username: str
        :param path: str
        :return: int
        """
        filepath = userpath2serverpath(username, path)
        last_server_timestamp = file_timestamp(filepath)

        # update Postgres database
        user = User.get(User.username == username)
        User.update(server_timestamp=last_server_timestamp).where(User.username == username).execute()
        # if the path already exists then only timestamp and md5 will be updated
        # otherwise a new row will be inserted
        try:
            f = File.get(File.path == path, File.owner == user.id)
            f.timestamp = last_server_timestamp
            f.md5 = md5
            f.save()
        except peewee.DoesNotExist:
            File.insert(owner=user.id, path=path, timestamp=last_server_timestamp, md5=md5).execute()

        return last_server_timestamp

    @auth.login_required
    def post(self, path):
        """
        Upload an authenticated user file to the server, given the path relative to the user directory.
        Return the file timestamp of the file created in the server.
        The file must not exist in the server, otherwise only return an http forbidden code.
        :param path: str
        """
        username = auth.username()

        upload_file = request.files['file']
        md5 = request.form['md5']
        md5 = calculate_file_md5(upload_file)
        dirname, filename = self._get_dirname_filename(path)

        if calculate_file_md5(upload_file) != md5:
            abort(HTTP_CONFLICT)

        if not os.path.exists(dirname):
            os.makedirs(dirname)
        else:
            if os.path.isfile(join(dirname, filename)):
                abort(HTTP_FORBIDDEN)

        filepath = join(dirname, filename)
        upload_file.save(filepath)

        # Update and save <userdata>, and return the last server timestamp.
        last_server_timestamp = self._update_user_path(username, path, md5)

        resp = jsonify({LAST_SERVER_TIMESTAMP: last_server_timestamp})
        resp.status_code = HTTP_CREATED
        return resp

    @auth.login_required
    def put(self, path):
        """
        Modify an authenticated user file in the server (uploading and overwriting it)
        given the path relative to the user directory. The file must exist in the server.
        Return the file timestamp of the file updated in the server.
        :param path: str
        """
        username = auth.username()
        upload_file = request.files['file']
        md5 = request.form['md5']
        md5 = calculate_file_md5(upload_file)
        dirname, filename = self._get_dirname_filename(path)

        if calculate_file_md5(upload_file) != md5:
            abort(HTTP_CONFLICT)

        filepath = join(dirname, filename)
        if os.path.isfile(filepath):
            upload_file.save(filepath)
        else:
            abort(HTTP_NOT_FOUND)

        # Update and save <userdata>, and return the last server timestamp.
        last_server_timestamp = self._update_user_path(username, path, md5)

        resp = jsonify({LAST_SERVER_TIMESTAMP: last_server_timestamp})
        resp.status_code = HTTP_CREATED
        return resp


api.add_resource(Files, '{}/files/<path:path>'.format(URL_PREFIX), '{}/files/'.format(URL_PREFIX))
api.add_resource(Actions, '{}/actions/<string:cmd>'.format(URL_PREFIX))
api.add_resource(Users, '{}/users/<string:username>'.format(URL_PREFIX))
api.add_resource(UsersRecoverPassword, '{}/users/<string:username>/reset'.format(URL_PREFIX))

# Set the flask.ext.mail.Mail instance
mail = configure_email()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--debug', default=False, action='store_true',
                        help='set console verbosity level to DEBUG (4) [default: %(default)s]')
    parser.add_argument('--verbose', default=False, action='store_true',
                        help='set console verbosity level to INFO (3) [default: %(default)s]. \
                        Ignored if --debug option is set.')
    parser.add_argument('-v', '--verbosity', const=1, default=1, type=int, choices=range(5), nargs='?',
                        help='set console verbosity: 0=CRITICAL, 1=ERROR, 2=WARN, 3=INFO, 4=DEBUG. \
                        [default: %(default)s]. Ignored if --verbose or --debug option is set.')
    parser.add_argument('-H', '--host', default='0.0.0.0',
                        help='set host address to run the server. [default: %(default)s].')
    args = parser.parse_args()

    if args.debug:
        # If set to True, win against verbosity and verbose parameter
        console_handler.setLevel(logging.DEBUG)
    elif args.verbose:
        # If set to True, win against verbosity parameter
        console_handler.setLevel(logging.INFO)
    else:
        levels = [logging.CRITICAL, logging.ERROR, logging.WARNING, logging.INFO, logging.DEBUG]
        console_handler.setLevel(levels[args.verbosity])

    logger.debug('File logging level: {}'.format(file_handler.level))

    if not os.path.exists(EMAIL_SETTINGS_FILEPATH):
        # ConfigParser.ConfigParser.read doesn't tell anything if the email configuration file is not found.
        raise ServerConfigurationError('Email configuration file "{}" not found!'.format(EMAIL_SETTINGS_FILEPATH))

    update_passwordmeter_terms(UNWANTED_PASS)

    userdata.update(load_userdata())

    init_root_structure()
    app.run(host=args.host, debug=args.debug)

if __name__ == '__main__':
    main()
