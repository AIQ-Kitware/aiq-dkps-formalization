"""Whole-word speech hints; authored/displayed text stays unchanged."""
from __future__ import annotations

import re
import xml.etree.ElementTree as ET


def load_pls_aliases(path):
    """Read the spelling-alias subset of W3C PLS for a text-only engine.

    This is not a phoneme renderer or a full PLS processor. Fail explicitly on
    entries requiring native phoneme or grammatical-role support.
    """
    root = ET.parse(path).getroot()
    ns = '{http://www.w3.org/2005/01/pronunciation-lexicon}'
    if root.tag != ns + 'lexicon' or root.get('version') != '1.0':
        raise ValueError('Expected a PLS 1.0 pronunciation lexicon')
    aliases = {}
    seen = set()
    for lexeme in root.findall(ns + 'lexeme'):
        if lexeme.find(ns + 'phoneme') is not None or lexeme.get('role'):
            raise ValueError('This text-only adapter supports PLS aliases; phonemes and roles require native engine support')
        values = lexeme.findall(ns + 'alias')
        graphemes = lexeme.findall(ns + 'grapheme')
        if len(values) != 1 or not graphemes:
            raise ValueError('Each text-only PLS entry needs graphemes and exactly one alias')
        value = ''.join(values[0].itertext()).strip()
        for grapheme in graphemes:
            key = ''.join(grapheme.itertext()).strip()
            if key.casefold() in seen:
                raise ValueError(f'Duplicate PLS grapheme: {key}')
            seen.add(key.casefold())
            aliases[key] = value
    if not aliases:
        raise ValueError('PLS lexicon contains no spelling aliases')
    return validate_replacements(aliases)


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
