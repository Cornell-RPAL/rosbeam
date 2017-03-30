#! /usr/bin/env python

"""
usage: %prog TARGET [OPTIONS]
"""

import os, sys, string
from optparse import OptionParser
import subprocess
import json
import base64
import time
import logging
import yaml
import hashlib
import re
import struct
import tarfile
import traceback
import fcntl

try:
  from stutil import release, yaml_util
except:
  rootpath = os.path.abspath(os.path.join(os.path.dirname(__file__), '..','..','..','..'))
  sys.path.insert(0,os.path.join(rootpath, 'externals'))
  import externals
  externals.setup_path(True)
  from stutil import release, yaml_util

TransferInterruptedByProgressFunction = release.TransferInterruptedByProgressFunction

logger = logging.getLogger('change_target')

class ChangeTargetError(Exception):
    pass


class DownloadError(Exception):
    pass

class NoLockFile(Exception):
  pass

class LockFile(object):
  def __init__(self, file_name):
    self.file_name = file_name
    self.lock_file = None

  def __enter__(self):
    # Just assume the directory is going to exist with proper permissions, etc.
    # I wish python had a nice implementation of "robust_open"
    try:
      self.lock_file = open(self.file_name, "w+b")
    except IOError as e:
      logger.error("Could not open lock file: %s. %s"%(self.file_name, e))
      raise NoLockFile

    fcntl.flock(self.lock_file, fcntl.LOCK_EX)

  def __exit__(self, type, value, tb):
    if self.lock_file:
      self.lock_file.close()

# From /usr/share/file/magic
def kernel_version(bzimage):
  """Return the kernel version of a bzImage file
  """
  with open(bzimage,'r') as f:
    f.seek(526)
    addr = struct.unpack('<h', f.read(2))[0]
    addr += 0x200
    f.seek(addr)
    ver = ''
    i = f.read(1)
    while ord(i) != 0:
        ver += i
        i = f.read(1)
  m = re.match(r'^.+\s+\(.*\)\s+(.*)$', ver)
  if m:
    return m.group(1)
  else:
    return None

def cleanup(good_configs, dest, boot_dest, remove_fn = None, exclude_files = None):

  if remove_fn is None:
    def remove(f):
      if (os.path.isdir(f)):
        shutil.rmtree(f)
      else:
        os.remove(f)

    remove_fn = remove

  image_whitelist = [os.path.join(dest,'releases.yaml')]
  kernel_whitelist = []
  for c in good_configs:
    image_whitelist.extend(os.path.normpath(p) for p in c.get('layers',[]))

    if 'kernel' in c:
      if 'file' in c['kernel']:
        kernel_whitelist.append(os.path.normpath(os.path.join(boot_dest,c['kernel']['file'])))
      if 'main' in c['kernel']:
        kernel_whitelist.append(os.path.normpath(os.path.join(boot_dest,c['kernel']['main'])))
      if 'archive' in c['kernel']:
        image_whitelist.append(os.path.normpath(c['kernel']['archive']))

  exclude = set()
  # Add all prefixes to the path whitelist
  for main_file in image_whitelist:
    for p in [ main_file, main_file + ".download", main_file + ".download.hashes" ]:
      while p and p != '/':
        exclude.add(p)
        p = os.path.dirname(p)

  # Do the cleanup:
  for root,dirs,files in os.walk(dest):
    skip = set()
    for f in files + dirs:
      fpath = os.path.normpath(os.path.join(root,f))
      if fpath in image_whitelist:
        skip.add(f)
      if fpath not in exclude:
        remove_fn(fpath)
        skip.add(f)

    # Don't descend into paths explicitly listed in the image_whitelist
    dirs[:] = list(set(dirs) - skip)


  # There's room for some borderline exceptions if certain files are missing, etc.
  # in such a case, we just don't cleanup and hope for the best.
  try:
    bzImage = os.path.join(boot_dest, 'bzImage')
    bzImage_last = os.path.join(boot_dest, 'bzImage.last')
    bzImage_new_last = os.path.join(boot_dest, 'bzImage.last.new')

    bzImage_dest = os.readlink(bzImage)

    # if the bzImage_dest is not in the whitelist, we shouldn't be
    # cleaning up since that would leave us without a kernel that matches
    # our existing targets
    if os.path.normpath(os.path.join(boot_dest,bzImage_dest)) not in kernel_whitelist:
      return

    # Finally, if bzImage_last is about to get cleaned up, we might as well
    # just make bzImage_last point to the same destination as bzImage, since
    # we know, by virtue of the above, that it's not going to get cleaned
    # up

    if os.path.islink(bzImage_last):
      bzImage_last_dest = os.readlink(bzImage_last)
    else:
      logging.error("bzImage.last missing or not a symlink.  Not cleaning up.")
      return

    if os.path.normpath(os.path.join(boot_dest,bzImage_last_dest)) not in kernel_whitelist:
      os.symlink(bzImage_dest, bzImage_new_last)
      os.rename(bzImage_new_last, bzImage_last)
  except Exception, e:
    logging.error("Exception when fixing bzImage.last.  Not cleaning up.\n%s"%traceback.format_exc())
    return

  for root,dirs,files in os.walk(boot_dest):
    # Only worry about the top-level directory for now
    del dirs[:]
    for f in files:
      fpath = os.path.normpath(os.path.join(root,f))
      if not os.path.islink(fpath) and fpath not in kernel_whitelist and f not in exclude_files:
        remove_fn(fpath)


def try_load_yaml(path):
  try:
    with open(path, 'r') as f:
      return yaml.load(f.read(), Loader=yaml_util.MostlySafeLoader)
  except:
    return {}


def needs_upgrade(target, target_file='/store/config/release/target'):

  running_config = try_load_yaml('/var/st/running')
  old_target_config = try_load_yaml(target_file)

  # If running and target both agree on the release_id, we don't need to upgrade
  if running_config.get('release_id',None) == target and old_target_config.get('release_id',None) == target:
    return False
  else:
    return True

def replace(prefix_sub, s):
  if prefix_sub == None:
    return s
  x,y = prefix_sub.split(':')
  return re.sub(r'^'+x, y, s)

def change_target(target, server=None, dest=None, target_file=None, path=None, unstable=None, no_watchdog=None,
        cert=None, do_cleanup=None, prefix_sub=None, no_heartbeat=False, dry_run = False, progress = release.progress_bar):
  """Attempt to change the target release.

  Returns:
    bool -- If dry_run is False: True if system needs to be rebooted. False if system wasn't changed.
            If dry_run is True: True if an update is needed. False if system does not need to change.

  Raises:
    ChangeTargetError or DownloadError if problems
    ReleaseUnknown if the target is unknown
  """

  if server is None:
    server = 'https://local-infr-relay.suitabletech.com:8890'
  if dest is None:
    dest = '/store/images'
  if target_file is None:
    target_file = '/store/config/release/target'
  if path is None:
    path = False
  if unstable is None:
    unstable = False
  if no_watchdog is None:
    no_watchdog = False
  if cert is None:
    cert = '/store/config/device.pem'
  if do_cleanup is None:
    do_cleanup = False

  with LockFile('/store/config/release/lock'):

    if not os.path.exists(dest):
      os.makedirs(dest)

    def get_progress(min_permillion, max_permillion):
        # We use permillions because the progress may only support
        # integers. (That's the case for release.progress_bar.)
        def progress_func(pos, total):
            if not no_heartbeat:
                with open('/var/st/watchdog/heartbeat','w') as f:
                    pass
            return progress(int(min_permillion + (max_permillion - min_permillion) * pos / float(total)), 1000000)
        return progress_func

    running_config = try_load_yaml('/var/st/running')
    working_config = try_load_yaml(os.path.join(os.path.dirname(target_file),'working'))
    old_target_config = try_load_yaml(target_file)

    rsh = release.ReleaseServerHandle(server, cert, cache=dest)

    if target.startswith('CHAN:'):
      chan = target.split(':', 1)[1]
      target = rsh.lookup_release(chan)

      if not target:
        raise ChangeTargetError("Could not find release for channel: %s"%chan)

    # If it's not a path-based change target, and we don't need an upgrade, return early
    if not path and not needs_upgrade(target, target_file):
      return False

    try:
      target_config = {'release_id': replace(prefix_sub, target), 'unstable': unstable, 'no_watchdog': no_watchdog, 'layers': []}
      all_verified = True
      release_path = None
      kern_path = None
      verified = {}

      # We potentially loop through here twice: once to verify the images without actually doing
      # an expensive download, and a second time to cleanup and do any downloading necessary.
      for verify_only in [True, False]:
        if dry_run and not verify_only:
            return True

        # We need to do cleanup before we actually download anything or else it will get deleted
        if do_cleanup and not verify_only:
          cleanup([running_config, working_config, old_target_config, target_config], dest, '/boot', exclude_files=['memtest_st.bin'])

        # For the progress bar, figure out how many files need to be
        # downloaded beyond the software image.
        # (We want everything in target_config except the software image.
        # But then we need to add in the base image.)
        num_extra_files = len(target_config['layers'])
        next_progress_start = 333333

        # Clear layers so that it will be properly constructed again
        target_config['layers'] = []
        def append_layer(layer):
            target_config['layers'].append(replace(prefix_sub, layer))

        if not release_path:
          if path:
            release_path = target
          else:
            r = rsh.get_release(target)
            release_path = r.download(dest, progress=get_progress(0, next_progress_start), verify_only=verify_only)
            if not release_path:
              # Make sure we don't delete a partially downloaded software image
              append_layer(r.get_download_path(dest))
              # If we don't already have the release itself, skip straight to the next step
              continue

        if os.path.isdir(release_path):
          with open(os.path.join(release_path, 'meta.yaml'), 'r') as f:
            meta = yaml.safe_load(f.read())
        else:
          meta_raw = subprocess.check_output(['tar', '-xOf', release_path, './meta.yaml'])
          meta = yaml.safe_load(meta_raw)

        if 'depends' in meta:
          for d in meta['depends']:
            r = rsh.get_release(d)
            # Note: In the verify_only pass, num_extra_files is zero so we need
            # to avoid divide by zero below.
            next_progress_end = next_progress_start + 666667 / num_extra_files if not verify_only else None
            dep = verified.get(d) or r.download(dest, progress=get_progress(next_progress_start, next_progress_end), verify_only=verify_only)
            next_progress_start = next_progress_end
            if not dep:
              all_verified = False
            else:
              verified[d] = dep
            append_layer(r.get_download_path(dest))

        # Must be appended last so that the software image can override
        # other layers. In particular the system image contains an init
        # that needs to be overwritten.
        append_layer(release_path)

        if not kern_path and 'required_kernel' in meta and meta['required_kernel']:
          r = rsh.get_kernel(meta['required_kernel'])
          kern_path = r.download_base(dest, progress=get_progress(next_progress_start, 1000000), verify_only=verify_only)
          if not kern_path:
            all_verified = False
          target_config['kernel'] = {'archive': replace(prefix_sub, r.get_download_base_path(dest))}

        # If everything was already verified, we don't need to do re-verify when we try to download
        if all_verified:
          break

      if kern_path:
        T = tarfile.open(kern_path)
        for m in T.getmembers():
          if m.isfile():
            name = os.path.basename(m.name)
            mpath = os.path.join('/boot', name)
            if os.path.exists(mpath):
              # If we're updating based on a path, it's not a production situation, we we only check size
              if path:
                s1 = m.size
                s2 = os.path.getsize(mpath)
                if s1 == s2:
                  logger.info("Skipping: %s. Size already matches."%name)
                else:
                  logger.info("Removing: %s. Size mismatch."%mpath)
                  os.remove(mpath)
              else:
                h1 = hashlib.sha256(T.extractfile(m).read()).hexdigest()
                h2 = subprocess.Popen(['sha256sum', mpath], stdout=subprocess.PIPE).communicate()[0].split()[0]
                if h1 == h2:
                  logger.info("Skipping: %s. sha256 sum already matches."%name)
                else:
                  logger.info("Removing: %s. sha256 mismatch."%mpath)
                  os.remove(mpath)

            if not os.path.exists(mpath):
              T.extract(m, '/boot')

            if name.startswith('bzImage'):
              target_config['kernel']['file'] = name
              ver = kernel_version(mpath)
              if ver:
                target_config['kernel']['version'] = ver
            if name.startswith('main'):
              target_config['kernel']['main'] = name
    finally:
      if 0:
        try:
            subprocess.check_call(['umount', '/boot'])
        except:
            logger.error("Unmount failed. Ignoring. Lsof output for /boot follows:") # Don't want to mask the actual exception when this fails.
            proc = subprocess.Popen(['lsof'], stdout = subprocess.PIPE)
            while True:
                line = proc.stdout.readline()
                if not line:
                    return
                split_line = line.split()
                if split_line and line.split()[-1].startswith('/boot'):
                    logger.info(line.rstrip())

    if not os.path.exists(os.path.dirname(target_file)):
      os.makedirs(os.path.dirname(target_file))

    with open(target_file, 'w') as f:
      f.write(yaml.safe_dump(target_config, default_flow_style=False))

    return (target_config != running_config)

def main(argv, stdout, environ):

  logging.basicConfig(format="%(asctime)s: %(message)s", level=logging.INFO)

  parser = OptionParser(__doc__.strip())
  parser.add_option("--cert",        action="store",      type="string", dest="cert",        default=None,
    help="Specify a certificate to use when talking to server")
  parser.add_option("--server",      action="store",      type="string", dest="server",      default=None,
    help="Specify which server to download target from if necessary.")
  parser.add_option("--dest",        action="store",      type="string", dest="dest",        default=None,
    help="Specify where to download the image from.")
  parser.add_option("--targetfile",  action="store",      type="string", dest="targetfile",  default=None,
    help="Specify the 'target' file to update.")
  parser.add_option("--path",        action="store_true",                dest="path",        default=False,
    help="Specify that the target provided is a path.")
  parser.add_option("--unstable",    action="store_true",                dest="unstable",    default=False,
    help="Specify that the target provided is unstable and should never be used as a fallback target.")
  parser.add_option("--no-watchdog", action="store_true",                dest="no_watchdog", default=False,
    help="Specify that the target provided should not run with a software watchdog enabled.")
  parser.add_option("--cleanup",     action="store_true",                dest="cleanup",     default=False,
    help="Specify that the /boot and images destination should be cleaned up")
  parser.add_option("--prefix-sub",  action="store",                     dest="prefix_sub",  default=None,
    help="Replace PREFIX:SUB")
  parser.add_option("--no-heartbeat",action="store_true",                dest="no_heartbeat",default=False,
    help="Don't try to touch the heartbeat file when downloading")
  parser.add_option("--default",     action="store_true",                dest="default",     default=False,
    help="Update the system to the default specified by the server")

  (options, args) = parser.parse_args()

  if not (len(args) == 1 or (len(args) == 0 and options.default)):
    parser.error("Please provide a release_id as a target, use --path to specify a location as a target, or specify --default")

  if options.default:
    conf = try_load_yaml('/var/lib/st/current.yaml')
    target = conf.get('upgrade_release_id', '')
    if not target:
      parser.error("current.yaml does not specify an upgrade_release_id")
  else:
    target = args[0]

  try:
    if change_target(target, options.server, options.dest, options.targetfile, options.path, options.unstable, options.no_watchdog, options.cert, options.cleanup, options.prefix_sub, options.no_heartbeat):
      logging.info("System target updated.  Need to st-restart")
      sys.exit(0)
    else:
      logging.info("System target unchanged.")
      sys.exit(1)
  except Exception, e:
    logging.error(traceback.format_exc())
    sys.exit(255)

if __name__ == "__main__":
  main(sys.argv, sys.stdout, os.environ)
