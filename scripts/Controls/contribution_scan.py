#!/usr/bin/env python3
"""Format scan for contributed proofs (Contributions/<Name>.lean).

    python3 -I scripts/Controls/contribution_scan.py              every Contributions/*.lean
    python3 -I scripts/Controls/contribution_scan.py FILE ...     the given files
    python3 -I scripts/Controls/contribution_scan.py --pull-request BASE
        the change from the git revision BASE to HEAD must add exactly one file
        Contributions/<Name>.lean and touch nothing else; that file is scanned

Exit status 0 when every file passes, 1 with one line per finding otherwise, 2 on a usage error.

Elaborating a Lean file can run code, and some options make Lean skip the kernel. The compiled
environment shows neither, so this scan reads the source before anything compiles it. It is an
allow list: a contributed file may contain imports of Mathlib, of this library and of
OddPerfect.Steps, then theorems, lemmas and definitions with ordinary tactic proofs. Everything
that defines syntax, runs a program at elaboration time, sets an option other than
maxHeartbeats and maxRecDepth, adds an attribute other than @[simp], or names the
metaprogramming namespaces is rejected, and so are string literals and quoted identifiers,
which could hide such text from a reader. The scan is deliberately stricter than the library's
own source scan; a proof that needs more belongs in a discussion with the maintainers.

It is a filter, not a proof of safety: a maintainer still reads the whole file before
compiling it outside a throwaway machine.
"""
import os
import re
import subprocess
import sys

MAX_BYTES = 200_000
MAX_LINE = 100
NAME = re.compile(r'^[A-Z][A-Za-z0-9]*$')
IMPORT = re.compile(r'^import (Mathlib(\.[A-Za-z0-9_]+)*|OddPerfect(\.[A-Za-z0-9_]+)+)$')
STARTERS = ('import', 'open', 'namespace', 'end', 'section', 'variable', 'theorem', 'lemma',
            'private', 'protected', 'def', 'abbrev', 'noncomputable', 'set_option', '@[simp]',
            'termination_by', 'decreasing_by', 'omit', 'include')
# Words that may not occur anywhere outside comments, as whole identifier components.
BANNED = set('''
sorry admit axiom native_decide unsafe partial opaque implemented_by extern export
macro macro_rules syntax elab elab_rules notation notation3 infix infixl infixr prefix postfix
binder_predicate unif_hint declare_syntax_cat initialize builtin_initialize
run_cmd run_tac run_elab run_meta by_elab eval simproc dsimproc simproc_decl
deriving attribute mutual inductive coinductive structure class instance irreducible_def
unseal seal alias proof_wanted compile_inductive add_decl_doc library_note
Lean Elab Meta IO Macro Syntax Parser Command Tactic Environment Expr Name Qq
MetaM CoreM TermElabM TacticM CommandElabM
ofReduceBool reduceBool trustCompiler csimp native debug
'''.split())
OPTIONS = ('maxHeartbeats', 'maxRecDepth')


def strip_comments(text):
    """The text with comments replaced by spaces (line structure kept). Block comments nest.
    Returns None when a block comment is not closed."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == '/-':
                depth += 1; out.append('  '); i += 2
            elif two == '-/':
                depth -= 1; out.append('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif two == '/-':
            depth = 1; out.append('  '); i += 2
        elif two == '--':
            while i < n and text[i] != '\n':
                out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    return None if depth else ''.join(out)


def scan_text(name, raw):
    """Findings (strings) for the contributed file called name.lean with the bytes raw."""
    if not NAME.match(name):
        return ['the file name must be <Name>.lean with Name a step name (letters and digits)']
    if len(raw) > MAX_BYTES:
        return [f'larger than {MAX_BYTES} bytes']
    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError:
        return ['not valid UTF-8']
    found = []
    if '\r' in text or '\t' in text or any(ord(c) < 32 and c != '\n' for c in text):
        found.append('control characters (tabs, carriage returns) are not allowed')
    for k, line in enumerate(text.split('\n'), 1):
        if len(line) > MAX_LINE:
            found.append(f'line {k}: longer than {MAX_LINE} characters')
    code = strip_comments(text)
    if code is None:
        return found + ['a block comment is not closed']
    for ch, why in (('"', 'string literals'), ('«', 'quoted identifiers'),
                    ('»', 'quoted identifiers'), ('#', 'commands and literals that start with #'),
                    ('`', 'quotations and name literals'), ('$', 'antiquotations')):
        if ch in code:
            k = code[:code.index(ch)].count('\n') + 1
            found.append(f'line {k}: {why} are not allowed ({ch})')
    lines = code.split('\n')
    body = False
    has_steps = False
    for k, line in enumerate(lines, 1):
        s = line.strip()
        if not s:
            continue
        if s.startswith('import ') or s == 'import':
            if body:
                found.append(f'line {k}: import after the first declaration')
            elif s == 'import OddPerfect.Steps':
                has_steps = True
            elif not IMPORT.match(s):
                found.append(f'line {k}: only Mathlib and OddPerfect modules may be imported')
            continue
        body = True
        if line[0] not in ' \t' and not s.startswith(STARTERS) and (s[0].isalpha() or s[0] in '@_'):
            found.append(f'line {k}: a line at the left margin must start a theorem, lemma, '
                         f'definition, namespace, section, open, variable or set_option')
        for m in re.finditer(r'@\[([^\]]*)\]?', line):
            if m.group(0) != '@[simp]':
                found.append(f'line {k}: the only attribute allowed is @[simp]')
        for m in re.finditer(r'\bset_option\b\s*(\S*)\s*(\S*)', line):
            if m.group(1) not in OPTIONS or not re.fullmatch(r'[0-9]{1,8}', m.group(2)):
                found.append(f'line {k}: set_option is allowed only for maxHeartbeats and '
                             f'maxRecDepth with a number')
        if re.search(r'[A-Za-z_][A-Za-z0-9_]*%', line):
            found.append(f'line {k}: an identifier followed directly by % (write a space '
                         f'before the remainder operator)')
        for word in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", line if not s.startswith('import ') else ''):
            if word in BANNED:
                found.append(f'line {k}: {word} is not allowed in a contributed file')
    if not has_steps:
        found.append('the file must import OddPerfect.Steps')
    if not re.search(r'^namespace OddPerfect\.Proofs\s*$', code, re.M):
        found.append('the file must open the namespace OddPerfect.Proofs')
    if len(re.findall(r'^theorem ' + name + r'\b', code, re.M)) != 1:
        found.append(f'the file must contain exactly one line starting with "theorem {name}"')
    return found


def scan_file(path):
    name = os.path.basename(path)
    if not name.endswith('.lean'):
        return [f'{path}: not a .lean file']
    try:
        with open(path, 'rb') as f:
            raw = f.read(MAX_BYTES + 1)
    except OSError as e:
        return [f'{path}: {e.strerror}']
    if os.path.islink(path):
        return [f'{path}: symbolic links are not accepted']
    return [f'{path}: {x}' for x in scan_text(name[:-5], raw)]


def pull_request_files(base):
    """The single contributed file of the change from base to HEAD, or findings."""
    r = subprocess.run(['git', 'diff', '--name-status', '--no-renames', base, 'HEAD'],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stderr.strip() or 'git diff failed')
        sys.exit(2)
    rows = [x.split('\t') for x in r.stdout.splitlines() if x]
    bad = [f'{p}: status {st}; a contribution adds one new file Contributions/<Name>.lean '
           f'and changes nothing else' for st, p in rows
           if st != 'A' or not re.fullmatch(r'Contributions/[A-Z][A-Za-z0-9]*\.lean', p)]
    if not bad and len(rows) != 1:
        bad = [f'{len(rows)} files added; a contribution adds exactly one']
    return ([] if bad else [rows[0][1]]), bad


def main(argv):
    found = []
    if argv[:1] == ['--pull-request']:
        if len(argv) != 2:
            print(__doc__); return 2
        files, found = pull_request_files(argv[1])
    elif argv:
        files = argv
    else:
        if not os.path.isdir('Contributions'):
            print('run from the repository root'); return 2
        files = sorted(os.path.join('Contributions', x) for x in os.listdir('Contributions')
                       if x.endswith('.lean'))
    for f in files:
        found += scan_file(f)
    for x in found:
        print(x)
    print(f'contribution scan: {len(files)} files, {len(found)} findings')
    return 1 if found else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
