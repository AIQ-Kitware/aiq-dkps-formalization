import pathlib, re, sys

def convert(text):
    lines = text.split("\n")
    if any(re.fullmatch(r"module\s*", l) for l in lines):
        return None  # already a module
    # 1. locate end of leading copyright block
    ins = 0
    if lines and lines[0].startswith("/-"):
        for i, l in enumerate(lines):
            if l.strip() == "-/":
                ins = i + 1
                break
    # 2. insert `module`
    lines[ins:ins] = ["module", ""]
    # collapse a doubled blank line the original header already supplied
    while ins + 2 < len(lines) and lines[ins + 1] == "" and lines[ins + 2] == "":
        del lines[ins + 2]
    # 3. public-ify top-level imports
    out = []
    last_import = -1
    for i, l in enumerate(lines):
        if re.match(r"^import \S", l):
            l = "public " + l
            last_import = i
        out.append(l)
    lines = out
    # 4. add `public section` if absent
    if not any(l.startswith("public section") for l in lines):
        # after the module docstring if one follows the imports, else after imports
        pos = last_import + 1
        j = pos
        while j < len(lines) and lines[j].strip() == "":
            j += 1
        if j < len(lines) and lines[j].startswith("/-!"):
            while j < len(lines) and lines[j].rstrip() != "-/":
                j += 1
            pos = j + 1
        lines[pos:pos] = ["", "public section"]
    return "\n".join(lines)

for p in map(pathlib.Path, sys.argv[1:]):
    t = p.read_text(encoding="utf-8")
    n = convert(t)
    if n is None:
        print(f"SKIP (already module) {p}")
        continue
    p.write_text(n, encoding="utf-8")
    print(f"CONVERTED {p}")
