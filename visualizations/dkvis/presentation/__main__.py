"""Build, export text, and narrate any registered presentation.

    python -m dkvis.presentation list
    python -m dkvis.presentation slides matching-proof-talk --one-file --handout
    python -m dkvis.presentation text --deck matching-proof-talk
    python -m dkvis.presentation video --deck matching-proof-talk --skip-render
"""
from __future__ import annotations

import argparse
import subprocess
import sys


def main(argv=None):
    args = list(sys.argv[1:] if argv is None else argv)
    commands = ('list', 'slides', 'text', 'video', 'audio', 'serve', 'experiment')
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', choices=commands)
    if not args or args[0] not in commands:
        parser.parse_args(args)
        return
    command, rest = args[0], args[1:]
    if command == 'list':
        argparse.ArgumentParser(description='List decks and transcript availability.').parse_args(rest)
        from dkvis.decks import DECKS
        for deck in DECKS.values():
            speech = 'transcript' if deck.narration else 'slides only'
            print(f'{deck.name:24s} {len(deck.slides):3d} scenes  {speech:11s} {deck.description}')
    elif command == 'slides':
        from dkvis.presentation.build import main as run
        run(rest)
    elif command == 'text':
        from dkvis.presentation.narration import main as run
        run(rest)
    elif command == 'serve':
        from dkvis.presentation.serve import main as run
        run(rest)
    elif command == 'experiment':
        from dkvis.presentation.continuity import main as run
        run(rest)
    elif command == 'audio':
        from dkvis.presentation.audio_quality import main as run
        run(rest)
    else:
        from dkvis.presentation.video import main as run
        run(rest)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, ValueError, FileNotFoundError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
