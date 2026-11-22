#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Source scan of the library files for constructs that can change what a file means or let a
# declaration bypass the kernel, which AxiomGate.lean cannot see in the compiled environment:
# debug options (debug.skipKernelTC), commands that run code at elaboration time (run_cmd,
# run_meta, run_elab, run_tac, by_elab, #eval, initialize, simprocs), new syntax or elaborators
# (syntax, macro, elab, notation and the mixfix commands, elaborator and initialization
# attributes), local or scoped instances, and
# set_option with an option outside ALLOWED_OPTIONS (exactly the options the library uses).
# It also rejects build options in lakefile.toml that pass options or arguments to Lean, and
# (in the default form, on the whole library) every file OddPerfect/**.lean that the root file
# OddPerfect.lean does not import directly, and every import of the root file without a file.
# Comments, docstrings, string literals (raw strings included) and quoted identifiers «...» are
# removed before ordinary token matching; attribute matching also preserves quoted names.
# The match runs on the whole text, so a construct in the middle of a
# line or after a line break is found too. The scan is lexical: it does not parse Lean, so it
# can report a construct that the parser would read differently (fail closed), and it trusts
# the rules above for where comments and strings end.
# Run from the repository root:
#     python3 -I scripts/Controls/source_scan.py                 (OddPerfect.lean, OddPerfect/**.lean, lakefile.toml)
#     python3 -I scripts/Controls/source_scan.py FILE [FILE ...] (the given files only; a file
#                                                 ending in .toml is scanned as a lakefile)
# Prints one line per finding, "path:line: construct", then a summary line.
# Policy: bang-prefixed string syntax (s!, m!, or another such prefix) is forbidden in library
# source because embedded expressions may execute elaborator code. This is a conservative
# restriction, not a complete Lean parser. Quoted attribute names are checked as identifiers.
# TOML option keys are checked after decoding, including Unicode escapes.
# Requires: Python 3.11+ standard library. Running time: about a second.
# Exit status: 0 when nothing is found, 1 when something is found, 2 for a usage error.
# License: GPL 3, same as the repository.

import os
import re
import sys
import tomllib

# The options the library sets, all of them limits of elaboration or linter switches.
ALLOWED_OPTIONS = {
    'Elab.async',
    'linter.dupNamespace',
    'maxHeartbeats',
    'maxRecDepth',
    'synthInstance.maxHeartbeats',
    'synthInstance.maxSize',
}

# Characters of Lean identifiers (ASCII letters, digits, _ ' ! ? and the dot of qualified names,
# Greek and Coptic, letterlike symbols, mathematical script letters, sub- and superscripted
# letters and digits as Lean allows them), so that a keyword glued to another symbol is
# still found.
IDENT_CHAR = (r"[A-Za-z0-9_.'!?\u0370-\u03ff\u1f00-\u1ffe\u2100-\u214f\u2080-\u209c"
              r"\u1d62-\u1d6a\U0001d49c-\U0001d59f]")


# Commands that run code at elaboration time or add syntax, matched as whole tokens.
KEYWORDS = {
    'run_cmd', 'run_meta', 'run_elab', '#eval', '#eval!', 'initialize', 'builtin_initialize',
    'syntax', 'declare_syntax_cat', 'macro', 'macro_rules', 'elab', 'elab_rules',
    'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'run_tac', 'by_elab',
    'simproc', 'dsimproc', 'simproc_decl', 'dsimproc_decl', 'notation3', 'binder_predicate',
}

TOKEN = re.compile('#?' + IDENT_CHAR + '+')
INTERPOLATION_PREFIX = re.compile('(' + IDENT_CHAR + r'+!)\s*$')

# (label, pattern) on the text without comments and strings.
CONSTRUCTS = [
    ('attribute that runs code', r'(?:@\[|\battribute\s*\[)[^\]]*(?<!' + IDENT_CHAR + r')(command_elab|term_elab|'
     r'tactic|delab|app_unexpander|macro|init|simproc|dsimproc|\w+_parser|builtin_\w+)(?!\w)'),
    ('local instance', r'(?<!' + IDENT_CHAR + r')(local|scoped)\s+instance\b'),
    ('local instance', r'attribute\s*\[[^\]]*(?<!' + IDENT_CHAR + r')(local|scoped)\s+instance\b'),
]

OPTION = re.compile(r'(?<!' + IDENT_CHAR + r')set_option\s+([^\s]+)')

LAKE_KEYS = re.compile(
    r'(?<![\w.])(leanOptions|moreLeanArgs|weakLeanArgs|moreServerOptions|moreServerArgs|'
    r'moreGlobalServerArgs|plugins|dynlibs|precompileModules|moreLeancArgs|moreLinkArgs)(?!\w)')


def blank(s):
    return ''.join('\n' if ch == '\n' else ' ' for ch in s)


OUTSIDE = re.compile(r"/-|--|\"|'|\u00ab")
RAW_OPENER = re.compile(r'r(#*)$')
INSIDE = re.compile(r'/-|-/')


def raw_hashes(text, i):
    """For a quote at position i, the hashes of a raw string opener r#...# just before it, or
    None when the quote does not open a raw string."""
    m = RAW_OPENER.search(text, max(0, i - 64), i)
    if not m or (m.start() > 0 and re.match(IDENT_CHAR, text[m.start() - 1])):
        return None
    return m.group(1)


def strip(text, preserve_quoted=False, interpolations=None):
    """Replaces comments, docstrings and string literals by spaces, keeping line breaks."""
    out = []
    i, n = 0, len(text)
    while i < n:
        m = OUTSIDE.search(text, i)
        if not m:
            out.append(text[i:])
            break
        out.append(text[i:m.start()])
        i, tok = m.start(), m.group(0)
        if tok == '/-':
            depth, j = 1, i + 2
            while depth and j < n:
                k = INSIDE.search(text, j)
                if not k:
                    j = n
                    break
                depth += 1 if k.group(0) == '/-' else -1
                j = k.end()
            out.append(blank(text[i:j]))
            i = j
        elif tok == '--':
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        elif tok == '\u00ab':
            # a quoted identifier such as «a"b»: nothing inside it is a quote or a comment
            j = text.find('\u00bb', i + 1)
            j = n if j < 0 else j + 1
            if preserve_quoted and j <= n and text[j - 1:j] == '»':
                out.append(' ' + text[i + 1:j - 1] + ' ')
            else:
                out.append(blank(text[i:j]))
            i = j
        elif tok == '"' and raw_hashes(text, i) is not None:
            # a raw string r"..." or r#"..."#: no escapes, it ends at the quote and the hashes
            close = '"' + raw_hashes(text, i)
            j = text.find(close, i + 1)
            j = n if j < 0 else j + len(close)
            out.append(blank(text[i:j]))
            i = j
        elif tok == '"':
            # Conservative policy: bang-prefixed string syntax may elaborate embedded code.
            # Check before masking; comments and ordinary/raw strings remain excluded.
            prefix = INTERPOLATION_PREFIX.search(''.join(out))
            if prefix and interpolations is not None:
                interpolations.append((prefix.start(), prefix.group(1)))
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append(blank(text[i:j]))
            i = j
        elif i + 2 < n and (text[i + 2] == "'" or text[i + 1] == '\\') \
                and (i == 0 or not re.match(IDENT_CHAR, text[i - 1])):
            # a character literal such as '"' or '\n'
            j = text.find("'", i + 2)
            j = n if j < 0 else j + 1
            out.append(' ' * (j - i))
            i = j
        else:
            out.append(tok)
            i += 1
    return ''.join(out)


def line_of(text, pos):
    return text.count('\n', 0, pos) + 1


def scan_lean(path):
    with open(path, encoding='utf-8') as f:
        raw = f.read()
    interpolations = []
    text = strip(raw, interpolations=interpolations)
    attribute_text = strip(raw, preserve_quoted=True)
    found = [(line_of(raw, pos), 'interpolated string syntax ' + prefix)
             for pos, prefix in interpolations]
    for m in TOKEN.finditer(text):
        tok = m.group(0)
        if tok in KEYWORDS:
            found.append((line_of(text, m.start()), tok))
        elif tok.startswith('debug.'):
            found.append((line_of(text, m.start()), 'debug option ' + tok))
    for label, pat in CONSTRUCTS:
        checked = attribute_text if label == 'attribute that runs code' else text
        for m in re.finditer(pat, checked):
            found.append((line_of(checked, m.start()), label))
    for m in OPTION.finditer(text):
        if m.group(1) not in ALLOWED_OPTIONS:
            found.append((line_of(text, m.start()), 'set_option ' + m.group(1)))
    return sorted(set(found))


def scan_lake(path):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as exc:
        m = re.search(r'\(at line (\d+)', str(exc))
        return [(int(m.group(1)) if m else 1, 'invalid TOML: ' + str(exc))]
    keys = set()
    def visit(value):
        if isinstance(value, dict):
            for key, child in value.items():
                if LAKE_KEYS.fullmatch(key):
                    keys.add(key)
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
    visit(data)
    # Locations are diagnostic only; acceptance uses the decoded TOML keys above.
    locations = {}
    for m in LAKE_KEYS.finditer(text):
        locations.setdefault(m.group(1), line_of(text, m.start()))
    for m in re.finditer(r'"(?:\\.|[^"\\])*"', text):
        try:
            value = tomllib.loads('key = ' + m.group(0))['key']
        except tomllib.TOMLDecodeError:
            continue
        if isinstance(value, str) and value in keys:
            locations.setdefault(value, line_of(text, m.start()))
    return sorted((locations.get(key, 1), 'lakefile option ' + key) for key in keys)


def library_files():
    files = ['OddPerfect.lean']
    for root, dirs, names in os.walk('OddPerfect'):
        dirs.sort()
        files += [os.path.join(root, x) for x in sorted(names) if x.endswith('.lean')]
    return files


def import_problems(files):
    """Library files that the root file OddPerfect.lean does not import directly, and imports
    of the root file without a library file. Without such a check a new module that is missing
    from the root file is never built and never seen by the gate."""
    mods = {f[:-5].replace(os.sep, '.') for f in files if f != 'OddPerfect.lean'}
    with open('OddPerfect.lean', encoding='utf-8') as f:
        root = strip(f.read())
    imported = set(re.findall(r'^import\s+(OddPerfect\.[\w.]+)\s*$', root, re.M))
    found = [(m.replace('.', '/') + '.lean', 'not imported by OddPerfect.lean')
             for m in sorted(mods - imported)]
    found += [('OddPerfect.lean', f'imports {m}, which has no file') for m in sorted(imported - mods)]
    return found


def main(argv):
    if any(a.startswith('-') for a in argv):
        print('usage: source_scan.py [FILE ...]')
        return 2
    if argv:
        lean = [a for a in argv if not a.endswith('.toml')]
        lake = [a for a in argv if a.endswith('.toml')]
    else:
        if not os.path.isfile('OddPerfect.lean') or not os.path.isdir('OddPerfect'):
            print('run from the repository root')
            return 2
        lean, lake = library_files(), ['lakefile.toml']
    total = 0
    for path in lean:
        for line, label in scan_lean(path):
            print(f'{path}:{line}: {label}')
            total += 1
    for path in lake:
        for line, label in scan_lake(path):
            print(f'{path}:{line}: {label}')
            total += 1
    if not argv:
        for path, label in import_problems(lean):
            print(f'{path}: {label}')
            total += 1
    if total:
        print(f'source scan FAILED: {total} findings in {len(lean) + len(lake)} files')
        return 1
    print(f'source scan OK: {len(lean) + len(lake)} files')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
