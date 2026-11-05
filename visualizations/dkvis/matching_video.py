"""Compatibility command for the original matching video workflow."""
import sys
import subprocess

from dkvis.presentation.video import main

if __name__ == '__main__':
    try:
        main(['--deck', 'matching-proof', *sys.argv[1:]])
    except (RuntimeError, ValueError, FileNotFoundError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
