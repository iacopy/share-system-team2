#!/usr/bin/env python
# -*- coding: utf-8 -*-

import json
import socket
import struct
import select
import os
import hashlib
import re
import time

from sys import exit as exit
from collections import OrderedDict
from shutil import copy2


# we import PollingObserver instead of Observer because the deleted event
# is not capturing https://github.com/gorakhargosh/watchdog/issues/46
from watchdog.observers.polling import PollingObserver as Observer
from watchdog.events import RegexMatchingEventHandler
from connection_manager import ConnectionManager

    # SNAPSHOT STRUCTURE
    # {
    #     "last_timestamp":"",
    #     "files":{
    #             "<file_path>":('<md5>','<timestamp>')

    #             }

    # }

class Daemon(RegexMatchingEventHandler):
    # Default configuration for Daemon, loaded if fail to load from file in PATH_CONFIG
    DEFAULT_CONFIG = OrderedDict()
    DEFAULT_CONFIG['sharing_path'] = './sharing_folder'
    DEFAULT_CONFIG['cmd_address'] = 'localhost'
    DEFAULT_CONFIG['cmd_port'] = 50001
    DEFAULT_CONFIG['api_suffix'] = '/API/V1/'
    DEFAULT_CONFIG['server_address'] = 'http://localhost:5000'
    DEFAULT_CONFIG['user'] = 'pasquale'
    DEFAULT_CONFIG['pass'] = 'secretpass'
    DEFAULT_CONFIG['timeout_listener_sock'] = 0.5
    DEFAULT_CONFIG['backlog_listener_sock'] = 1

    IGNORED_REGEX = ['.*\.[a-zA-z]+?#',  # Libreoffice suite temporary file ignored
                     '.*\.[a-zA-Z]+?~',  # gedit issue solved ignoring this pattern:
                     # gedit first delete file, create, and move to dest_path *.txt~
                     '.*\/(\..*)',  # hidden files TODO: improve
                     ]

    PATH_CONFIG = 'config.json'
    INT_SIZE = struct.calcsize('!i')

    def __init__(self):
        RegexMatchingEventHandler.__init__(self, ignore_regexes=Daemon.IGNORED_REGEX, ignore_directories=True)
        # Initialize variable
        self.daemon_state = 'down'  # TODO implement the daemon state (disconnected, connected, syncronizing, ready...)
        self.dir_state =  {}  # {'timestamp': <timestamp>, 'md5': <md5>}
        self.running = 0
        self.client_snapshot = {}
        self.listener_socket = None
        self.observer = None
        self.cfg = self.load_cfg(Daemon.PATH_CONFIG)
        # We call os.path.abspath to unrelativize the sharing path(now is relative for development purpose)
        # TODO: Allow the setting of sharing path by user
        self.cfg['sharing_path'] = os.path.abspath(self.cfg['sharing_path'])

        self.conn_mng = ConnectionManager(self.cfg)
        # Operations necessary to start the daemon
        self.connect_to_server()
        self.build_client_snapshot()
        # TODO implement NEW sync_with_server
        self._sync_with_server()
        self.create_observer()

    def load_cfg(self, config_path):
        """
        Load config, if impossible to find it or config file is corrupted restore it and load default configuration
        :param config_path: Path of config
        :return: dictionary containing configuration
        """
        def build_default_cfg():
            """
            Restore default config file by writing on file
            :return: default configuration contained in the dictionary DEFAULT_CONFIG
            """
            with open(Daemon.PATH_CONFIG, 'wb') as fo:
                json.dump(Daemon.DEFAULT_CONFIG, fo, skipkeys=True, ensure_ascii=True, indent=4)
            return Daemon.DEFAULT_CONFIG

        if os.path.isfile(config_path):
            try:
                with open(config_path, 'r') as fo:
                    loaded_config = json.load(fo)
            except ValueError:
                print 'Impossible to read "{0}"! "{0}" overwrited and loaded default config!'.format(config_path)
                return build_default_cfg()
            corrupted_config = False
            for k in Daemon.DEFAULT_CONFIG:
                if k not in loaded_config:
                    corrupted_config = True
            if not corrupted_config:
                return loaded_config
            else:
                print '"{0}" corrupted! "{0}" overwrited and loaded default config!'.format(config_path)
                return build_default_cfg()
        else:
            print '{0} doesn\'t exist, "{0}" overwrited and loaded default config!'.format(config_path)
            return build_default_cfg()

    def connect_to_server(self):
        # self.cfg['server_address']
        pass    

    def build_client_snapshot(self):
        self.client_snapshot = {}
        for dirpath, dirs, files in os.walk(self.cfg['sharing_path']):
            for filename in files:
                filepath = os.path.join(dirpath, filename)
                matched_regex = False
                for r in Daemon.IGNORED_REGEX:
                    if re.match(r, filepath) is not None:
                        matched_regex = True
                        print 'Ignored Path:', filepath
                        break
                if not matched_regex:
                    relative_path = self.relativize_path(filepath)
                    with open(filepath, 'rb') as f:
                        self.client_snapshot[relative_path] = ['', hashlib.md5(f.read()).hexdigest()]

    def _is_directory_modified(self):
        # TODO process directory and get global md5. if the directory is modified return 'True', else return 'False'
        return True


    def md5_exists(self, searched_md5):
        # TODO check if md5 match with almost one of md5 of file in the directory
        # return a path if match, 'None' otherwise
        for path in self.client_snapshot:
            if searched_md5 in self.client_snapshot[path][1]:
                return path
        else:
            self.stop(1, 'Copy Error!!')

    def sync_with_server_to_future(self):
        """
        Makes the synchronization with server
        """
        def _get_server_files():
            response = self.conn_mng.dispatch_request('get_server_snapshot', '')
            return response['server_timestamp'], response['files']
        def _filter_tree_difference(server_dir_tree):
            # process local dir_tree and server dir_tree
            # and makes a diffs classification
            # return a dict representing that classification
            # E.g. { 'new_on_server'     : <[<filepath>, ...]>,  # files in server, but not in client
            #   'modified'          : <[<filepath>, ...]>,  # files in server and client, but different
            #   'new_on_client'     : <[<filepath>, ...]>,  # files not in server, but in client
            # }
            client_files = set(self.client_snapshot.keys())
            server_files = set(server_dir_tree.keys())

            new_on_server = list(server_files.difference(client_files))
            new_on_client = list(client_files.difference(server_files))
            modified = []

            for filepath in server_files.intersection(client_files):
                # check files md5
                if server_dir_tree[filepath][1] == self.client_snapshot[filepath][1]:
                    modified.append(filepath)

            return {'new_on_server': new_on_server, 'modified': modified, 'new_on_client': new_on_client}

        def _make_copy(src, dst):
            abs_src = self.absolutize_path(src)
            abs_dst = self.absolutize_path(dst)
            try:
                copy2(abs_src, abs_dst)
            except IOError:
                return False

            self.client_snapshot[dst] = self.client_snapshot[src]
            return True
        def _make_move(src, dst):
            abs_src = self.absolutize_path(src)
            abs_dst = self.absolutize_path(dst)
            try:
                move(abs_src, abs_dst)
            except IOError:
                return False

            return True

        def _check_md5(dir_tree, md5):
            for k, v in dir_tree.items():
                if md5 == v[1]:
                    return k
            return None

        local_timestamp = self.dir_state['timestamp']
        server_timestamp, server_dir_tree = self._get_server_files()

        tree_diff = _filter_tree_difference(server_dir_tree)

        if self._is_directory_modified():
            if local_timestamp >= server_timestamp:
                pass
            else:  # local_timestamp < server_timestamp
                for filepath, timestamp, md5 in tree_diff['new']:
                    if timestamp > local_timestamp:
                        founded_path = self.md5_exists(md5)
                        rel_filepath = self.relativize_path(filepath)
                        if founded_path:
                            _make_copy(src=self.absolutize_path(founded_path), dst=filepath)
                        else:
                            # TODO check if download succeed
                            self.conn_mng.dispatch_request('download', {'filepath': filepath})

                            with open(filepath, 'rb') as fo:
                                self.client_snapshot[rel_filepath][1] = hashlib.md5(fo.read()).hexdigest()
                    else:  # file older then local_timestamp, this mean is time to delete it!
                        # TODO check if delete succeed
                        self.conn_mng.dispatch_request('delete', {'filepath': filepath})
                        if rel_filepath in self.client_snapshot:
                            del self.client_snapshot[rel_filepath]

                for filepath, timestamp, md5 in tree_diff['modified']:
                    pass  # download all files

                for filepath, timestamp, md5 in tree_diff['deleted']:
                    pass  # deleted files

        else:
            if local_timestamp == server_timestamp:
                # send all diffs to server
                pass
            else:  # local_timestamp < server_timestamp
                for filepath, timestamp, md5 in tree_diff['new']:
                    retval = self.md5_exists(md5)
                    if retval:
                        if retval[0] in self.client_snapshot:
                            pass  # copy file
                        else:
                            pass  # rename file
                    else:
                        if timestamp > local_timestamp:
                            pass  # dowload file
                        else:
                            pass  # delete file in server

                for filepath, timestamp, md5 in tree_diff['modified']:
                    if timestamp < local_timestamp:
                        pass  # upload file to server (update)
                    else:
                        pass  # duplicate file (.conflicted)
                        # upload .conflicted file to server

                for filepath, timestamp, md5 in tree_diff['deleted']:  # !!!! file in client and not in server ('deleted' isn't appropriate label, but now functionally)
                    pass  # upload file to server

    def _sync_with_server(self):
        """
        Download from server the files state and find the difference from actual state.
        """

        server_snapshot = self.conn_mng.dispatch_request('get_server_snapshot')
        if server_snapshot is None:
            self.stop(1, '\nReceived bad snapshot. Server down?\n')
        else:
            server_timestamp = server_snapshot['server_timestamp']
            server_snapshot = server_snapshot['files']

        total_md5 = self.calculate_md5_of_dir(self.cfg['sharing_path'])
        print "TOTAL MD5: ", total_md5

        for filepath in server_snapshot: 
            if filepath not in self.client_snapshot:
                # TODO: check if download succeed, if so update client_snapshot with the new file
                self.conn_mng.dispatch_request('download', {'filepath': filepath})
                self.client_snapshot[filepath] = server_snapshot[filepath]            
            elif server_snapshot[filepath][1] != self.client_snapshot[filepath][1]:
                self.conn_mng.dispatch_request('modify', {'filepath': filepath})
                hashed_file = hash_file(self.absolutize_path(filepath))
                self.client_snapshot[filepath] = ['', hashed_file]
        for filepath in self.client_snapshot:
            if filepath not in server_snapshot:
                self.conn_mng.dispatch_request('upload', {'filepath': filepath})


    def relativize_path(self, abs_path):
        """
        This function relativize the path watched by daemon:
        for example: /home/user/watched/subfolder/ will be subfolder/
        """
        folder_watched_abs = os.path.abspath(self.cfg['sharing_path'])
        tokens = abs_path.split(folder_watched_abs)
        # if len(tokens) is not 2 this mean folder_watched_abs is repeated in abs_path more then one time...
        # in this case is impossible to use relative path and have valid path!
        if len(tokens) is 2:
            relative_path = tokens[-1]
            return relative_path[1:]
        else:
            self.stop(1, 'Impossible to use "{}" path, please change dir name'.format(abs_path))

    def absolutize_path(self, rel_path):
        """
        This function absolutize a path that i have relativize before:
        for example: subfolder/ will be /home/user/watched/subfolder/
        """
        abs_path = os.path.join(self.cfg['sharing_path'], rel_path)
        if os.path.isfile(abs_path):
            return abs_path
        else:
            return None

    def create_observer(self):
        """
        Create an instance of the watchdog Observer thread class.
        """
        self.observer = Observer()
        self.observer.schedule(self, path=self.cfg['sharing_path'], recursive=True)

    # TODO handly erorrs in dictionary if the client_dispatcher miss required data!!
    # TODO update struct with new more performance data structure
    # TODO verify what happen if the server return a error message
    ####################################
    # In client_snapshot the structure are {'<filepath>' : '<md5>'} so you have to convert!!!!
    ####################################

    def on_created(self, e):
        def build_data(cmd, e, new_md5=None):
            """
            Prepares the data from event handler to be delivered to connection_manager.
            """
            data = {'cmd': cmd}
            if cmd == 'copy':
                path_with_searched_md5 = self.md5_exists(new_md5)
                # TODO check what happen when i find more than 1 path with the new_md5
                data['file'] = {'src': path_with_searched_md5,
                                'dst': self.relativize_path(e.src_path),
                                'md5': self.client_snapshot[path_with_searched_md5],
                                }
            else:
                f = open(e.src_path, 'rb')
                data['file'] = {'filepath': self.relativize_path(e.src_path),
                                'md5': hashlib.md5(f.read()).hexdigest(),
                                }
            return data

        with open(e.src_path, 'rb') as f:
            new_md5 = hashlib.md5(f.read()).hexdigest()
        relative_path = self.relativize_path(e.src_path)
        # with this check i found the copy events
        if new_md5 in self.client_snapshot.values():
            print 'start copy'
            data = build_data('copy', e, new_md5)
            self.client_snapshot[data['file']['dst']] = data['file']['md5']
        # this elif check that this created aren't modified event
        elif relative_path in self.client_snapshot:
            print 'start modified FROM CREATE!!!!!'
            data = build_data('modify', e)
            self.client_snapshot[data['file']['filepath']] = data['file']['md5']
        else:
            print 'start create'
            data = build_data('upload', e)
            self.client_snapshot[data['file']['filepath']] = data['file']['md5']
        self.conn_mng.dispatch_request(data['cmd'], data['file'])

    def on_moved(self, e):

        print 'start move'
        with open(e.dest_path, 'rb') as f:
            dest_md5 = hashlib.md5(f.read()).hexdigest()
        data = {'cmd': 'move',
                'file': {'src': self.relativize_path(e.src_path),
                         'dst': self.relativize_path(e.dest_path),
                         'md5': dest_md5,
                         }
                }
        self.client_snapshot[data['file']['dst']] = data['file']['md5']
        self.client_snapshot.pop(data['file']['src'], 'NOTHING TO POP')
        self.conn_mng.dispatch_request(data['cmd'], data['file'])

    def on_deleted(self, e):

        print 'start delete'
        rel_deleted_path = self.relativize_path(e.src_path)
        self.client_snapshot.pop(rel_deleted_path, 'NOTHING TO POP')
        self.conn_mng.dispatch_request('delete', {'filepath': rel_deleted_path})

    def on_modified(self, e):

        print 'start modified'
        with open(e.src_path, 'rb') as f:
            data = {'cmd': 'modify',
                    'file': {'filepath': self.relativize_path(e.src_path),
                             'md5': hashlib.md5(f.read()).hexdigest()
                             }
                    }
        filepath = self.relativize_path(e.src_path)
        hashed_file = self.hash_file(e.src_path)
        self.conn_mng.dispatch_request(data['cmd'], data['file'])
        self.client_snapshot[filepath] = ['', hashed_file]


    def start(self):
        """
        Starts the communication with the command_manager.
        """

        self.listener_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener_socket.bind((self.cfg['cmd_address'], self.cfg['cmd_port']))
        self.listener_socket.listen(self.cfg['backlog_listener_sock'])
        r_list = [self.listener_socket]
        self.observer.start()
        self.daemon_state = 'started'
        self.running = 1
        try:
            while self.running:
                r_ready, w_ready, e_ready = select.select(r_list, [], [], self.cfg['timeout_listener_sock'])

                for s in r_ready:

                    if s == self.listener_socket:
                        # handle the server socket
                        client_socket, client_address = self.listener_socket.accept()
                        r_list.append(client_socket)
                    else:
                        # handle all other sockets
                        length = s.recv(Daemon.INT_SIZE)
                        if length:
                            length = int(struct.unpack('!i', length)[0])
                            message = json.loads(s.recv(length))
                            for cmd, data in message.items():
                                if cmd == 'shutdown':
                                    raise KeyboardInterrupt
                                self.conn_mng.dispatch_request(cmd, data)
                        else:
                            s.close()
                            r_list.remove(s)
        except KeyboardInterrupt:
            self.stop(0)

    def stop(self, exit_status, exit_message=None):
        """
        Stop the Daemon components (observer and communication with command_manager).
        """
        if self.daemon_state == 'started':
            self.observer.stop()
            self.observer.join()
            self.listener_socket.close()
        self.running = 0
        if exit_message:
            print exit_message
        exit(exit_status)

    def calculate_md5_of_dir(self, directory, verbose=0):
        """
        Calculate the md5 of the entire directory, 
        with the md5 in client_snapshot and the md5 of full filepath string.
        When the filepath isn't in client_snapshot the md5 is calculated on fly
        :return is the md5 hash of the directory
        """
        if verbose:
            start = time.time()
        md5Hash = hashlib.md5()
        if not os.path.exists(directory):
            return -1
        
        for root, dirs, files in os.walk(directory, followlinks=False):
            for names in files:
                filepath = os.path.join(root,names)
                rel_path = self.relativize_path(filepath)
                if rel_path in self.client_snapshot:
                    md5Hash.update(self.client_snapshot[rel_path][1])
                    md5Hash.update(hashlib.md5(filepath).hexdigest())
                else:
                    hashed_file = self.hash_file(filepath)
                    if hashed_file:
                        md5Hash.update(hashed_file)
                        md5Hash.update(hashlib.md5(filepath).hexdigest())              
                    else:
                        print "can't hash file: ", filepath

        if verbose:
            stop = time.time()
            print stop - start
        return md5Hash.hexdigest()

    def read_file(self, file_path):
        """
        Read file in chunks 
        :return the readed file as binary or None in case of error
        """
        readed = ''
        try:
            f1 = open(file_path, 'rb')
            while 1:
                # Read file in as little chunks
                    buf = f1.read(1024)
                    if not buf:
                        break                
                    readed += buf
            f1.close()
            return readed 
        except (OSError, IOError) as e:
            print e
            return None
            # You can't open the file for some reason

    def hash_file(self, file_path):
        """
        :accept an absolute file path
        :return the md5 hash of received file
        """
        md5Hash = hashlib.md5()
        try:
            f1 = open(file_path, 'rb')
            while 1:
                # Read file in as little chunks
                    buf = f1.read(1024)
                    if not buf:
                        break                
                    md5Hash.update(hashlib.md5(buf).hexdigest())
            f1.close()
            return md5Hash.hexdigest()
        except (OSError, IOError) as e:
            print e
            return None
            # You can't open the file for some reason

if __name__ == '__main__':
    daemon = Daemon()    
    daemon.start()