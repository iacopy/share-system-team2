__author__ = 'milly'

import unittest
import os
import shutil
import json

import httpretty

import client_daemon

TEST_DIR = 'daemon_test'
LAST_TIMESTAMP = 'last_timestamp'
GLOBAL_MD5 = 'global_md5'

server_timestamp = 1
files = {'ciao.txt': (3, 'md5md6'),
         'carlo.txt': (2, 'md6md6')}


start_dir = os.getcwd()


def setup_test_dir():
    """
    Create (if needed) <TEST_DIR> directory starting from current directory and change current directory to the new one.
    """
    try:
        os.mkdir(TEST_DIR)
    except OSError:
        pass

    os.chdir(TEST_DIR)


def tear_down_test_dir():
    """
    Return to initial directory and remove the <TEST_DIR> one.
    """
    os.chdir(start_dir)
    shutil.rmtree(TEST_DIR)


def create_file(file_path, content=''):
    print 'Creating "{}"'.format(file_path)
    dirname = os.path.dirname(file_path)
    if not os.path.exists(dirname):
        os.makedirs(dirname)

    assert os.path.isdir(dirname), '{} must be a directory'.format(dirname)

    with open(file_path, 'w') as fp:
        fp.write(content)
    return os.path.getmtime(file_path)


class FileFakeEvent(object):
    """
    Class that simulates a file related event sent from watchdog.
    Actually create 'src_path' attribute and the file in disk.
    """
    def __init__(self, src_path, content=''):
        self.src_path = src_path
        create_file(self.src_path, content=content)


class TestClientDaemon(unittest.TestCase):
    def setUp(self):
        self.client_daemon = client_daemon.Daemon()
        self.client_daemon.dir_state = {'timestamp': 0}
        self.client_daemon.client_snapshot = {'ciao.txt': (2, 'md5md5')}

    def _test_sync_process(self):
        self.assertEqual(sorted(self.client_daemon._sync_process(server_timestamp, files)),
                         sorted([('download', 'ciao.txt'), ('download', 'carlo.txt')]))


class TestClientDaemonOnEvents(unittest.TestCase):
    CONFIG_DIR = os.path.join(os.environ['HOME'], '.PyBox')
    CONFIG_FILEPATH = os.path.join(CONFIG_DIR, 'daemon_config')
    LOCAL_DIR_STATE_PATH = os.path.join(CONFIG_DIR, 'dir_state')

    def setUp(self):
        setup_test_dir()
        httpretty.enable()

        #self.cm = ConnectionManager()
        with open(self.CONFIG_FILEPATH) as fo:
            self.cfg = json.load(fo)

        self.auth = self.cfg['user'], self.cfg['pass']
        self.cfg['server_address'] = "http://localhost:5000"

        # create this auth testing
        self.authServerAddress = "http://" + self.cfg['user'] + ":" + self.cfg['pass']
        self.base_url = self.cfg['server_address'] + self.cfg['api_suffix']
        self.files_url = self.base_url + 'files/'

        # Instantiate the daemon
        self.client_daemon = client_daemon.Daemon()

        # Injecting a fake client snapshot
        md5 = '50abe822532a06fb733ea3bc089527af'
        ts = 1403878699

        self.client_daemon.client_snapshot = {'dir/file.txt': [ts, md5]}
        self.client_daemon.local_dir_state = {LAST_TIMESTAMP: ts, GLOBAL_MD5: md5}

    def tearDown(self):
        httpretty.disable()
        httpretty.reset()
        tear_down_test_dir()

    @httpretty.activate
    def test_on_created(self):
        """
        Test on_created method of daemon when a new file is created.
        """
        start_state = self.client_daemon.local_dir_state.copy()
        ts1 = start_state[LAST_TIMESTAMP]
        ts2 = ts1 + 60  # arbitrary value

        # new file I'm going to create in client sharing folder
        new_path = 'created_file.txt'

        url = self.files_url + new_path
        httpretty.register_uri(httpretty.POST, url, status=201,
                               body='{"server_timestamp":%d}' % ts2,
                               content_type="application/json")

        abs_path = os.path.join(self.client_daemon.cfg['sharing_path'], new_path)
        event = FileFakeEvent(abs_path)

        self.client_daemon.on_created(event)
        # test that the new path is in the client_snapshot
        self.assertIn(new_path, self.client_daemon.client_snapshot)
        # simply check that local_dir_state is changed
        self.assertNotEqual(start_state, self.client_daemon.local_dir_state)

        # # daemon.local_dir_state should be a dict
        self.assertIsInstance(self.client_daemon.local_dir_state, dict)
        # last_timestamp should be an int
        self.assertIsInstance(self.client_daemon.local_dir_state[LAST_TIMESTAMP], int)
        # test exact value of timestamp
        self.assertEqual(self.client_daemon.local_dir_state[LAST_TIMESTAMP], ts2)


if __name__ == '__main__':
    unittest.main(verbosity=3)
