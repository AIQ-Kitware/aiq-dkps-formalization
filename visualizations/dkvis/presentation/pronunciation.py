"""Whole-word speech hints; authored/displayed text stays unchanged."""
from __future__ import annotations

import re


def validate_replacements(values):
    if not isinstance(values, dict) or any(
        not isinstance(key, str) or not key.strip()
        or not isinstance(value, str) or not value.strip()
        for key, value in values.items()
    ):
        raise ValueError('pronunciation_replacements must map nonempty words/phrases to nonempty strings')
    if len({key.casefold() for key in values}) != len(values):
        raise ValueError('pronunciation_replacements contains duplicate case-insensitive keys')
    return values


def speech_text(text, replacements=None):
    replacements = validate_replacements({} if replacements is None else replacements)
    if not replacements:
        return text
    lookup = {key.casefold(): value for key, value in replacements.items()}
    pattern = r'(?<!\w)(?:' + '|'.join(re.escape(key) for key in sorted(replacements, key=len, reverse=True)) + r')(?!\w)'

    def replace(match):
        original = match[0]
        replacement = lookup[original.casefold()]
        if original.isupper():
            return replacement.upper()
        if original[0].isupper():
            return replacement[0].upper() + replacement[1:]
        return replacement

    # A single pass prevents a replacement from triggering another rule.
    return re.sub(pattern, replace, text, flags=re.IGNORECASE)
