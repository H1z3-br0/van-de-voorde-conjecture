import re, sys, glob
BAD = re.compile(r'(?<![\w.])(sorry|admit|native_decide|implemented_by|extern|unsafe|skipKernelTC|ofReduceBool|axiom)(?![\w])')


def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)


bad = 0
for f in sorted(glob.glob('BSWCheck/*.lean')) + ['BSWCheck.lean']:
    for k, line in enumerate(strip(open(f).read()).split('\n'), 1):
        m = BAD.search(line)
        if m: print(f'{f}:{k}: {m.group(1)}: {line.strip()}'); bad += 1
sys.exit(1 if bad else 0)
