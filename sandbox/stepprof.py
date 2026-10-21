#!/usr/bin/env python3
"""Exact per-statement step profile of one snforge test, from its VM trace.

Runs inside the sandbox (sandbox/run.sh NAME PATCH python3 sandbox/stepprof.py TEST [N]).
Re-runs TEST with --save-trace-data, compiles the test crate's Sierra with
universal-sierra-compiler to get the Sierra-statement -> CASM-offset map, and attributes
every executed step (one VM trace entry) to the Sierra statement that emitted it.

Prints the steps per function, then the N hottest Sierra statements (count = steps).
"""
import bisect
import collections
import glob
import json
import os
import re
import subprocess
import sys

test = sys.argv[1]
top = int(sys.argv[2]) if len(sys.argv) > 2 else 60
crate = "pqbench_falcon_512"

subprocess.run(["snforge", "test", "-p", crate, test, "--save-trace-data",
                "--tracked-resource", "cairo-steps"], capture_output=True, text=True)
trace_file = max(glob.glob(f"crates/*/snfoundry_trace/*_{test.split('::')[-1]}.json"),
                 key=os.path.getmtime)
tr = json.load(open(trace_file))
info = tr["cairo_execution_info"]
pcs = [s["pc"] for s in info["casm_level_info"]["vm_trace"]]
sierra_path = info["source_sierra_path"]

prog = json.load(open(sierra_path))
if "sierra_program" in prog:  # snforge test format wraps the program
    prog = prog["sierra_program"]
raw = "/tmp/raw_sierra.json"
json.dump(prog, open(raw, "w"))
subprocess.run(["universal-sierra-compiler", "compile-raw", "--sierra-path", raw,
                "--output-path", "/tmp/casm.json"], check=True, capture_output=True)
casm = json.load(open("/tmp/casm.json"))
dbg = casm["debug_info"]
stmt_off = [s[0] for s in dbg]

stmts = prog["statements"]
funcs = prog["funcs"]
pdbg = prog.get("debug_info") or {}


def names_of(key):
    v = pdbg.get(key) or []
    return {(e[0]["id"] if isinstance(e[0], dict) else e[0]): e[1] for e in v}


user_names = names_of("user_func_names")
libfunc_names = names_of("libfunc_names")


def fname(f):
    i = f["id"]
    return i.get("debug_name") or user_names.get(i["id"], str(i["id"]))


def lname(decl):
    g = decl["long_id"]
    args = []
    for a in g.get("generic_args", []):
        if "Type" in a:
            args.append(str(a["Type"].get("debug_name") or a["Type"]["id"]))
        elif "Value" in a:
            args.append(str(a["Value"]))
        else:
            args.append(str(a)[:40])
    return g["generic_id"] + ("<" + ",".join(args) + ">" if args else "")


fentries = sorted((f["entry_point"], fname(f)) for f in funcs)
fstarts = [e for e, _ in fentries]
lib_names = {l["id"]["id"]: lname(l) for l in prog["libfunc_declarations"]}

# The trace pc is absolute; find the base from the test function's entry offset.
short = test.split("::")[-1]
test_entry = next(e for e, n in fentries if n.endswith(short + "__snforge_internal_test_generated"))
base = pcs[0] - stmt_off[test_entry]

off_sorted = sorted((o, i) for i, o in enumerate(stmt_off))
offs = [o for o, _ in off_sorted]
per_stmt = collections.Counter()
for pc in pcs:
    rel = pc - base
    j = bisect.bisect_right(offs, rel) - 1
    if j >= 0:
        per_stmt[off_sorted[j][1]] += 1

per_func = collections.Counter()
for si, c in per_stmt.items():
    k = bisect.bisect_right(fstarts, si) - 1
    per_func[fentries[k][1]] += c
print(f"total steps {len(pcs)}  attributed {sum(per_stmt.values())}")
for n, c in per_func.most_common(15):
    print(f"{c:8d}  {n[:110]}")
print()
per_lib = collections.Counter()
for si, c in per_stmt.items():
    inv = stmts[si].get("Invocation")
    if inv:
        per_lib[re.sub(r"<.*", "", lib_names.get(inv["libfunc_id"]["id"], "?"))] += c
    else:
        per_lib["return"] += c
for n, c in per_lib.most_common(20):
    print(f"{c:8d}  {n}")
print()
for si, c in per_stmt.most_common(top):
    inv = stmts[si].get("Invocation")
    k = bisect.bisect_right(fstarts, si) - 1
    lib = lib_names.get(inv["libfunc_id"]["id"], "?") if inv else "return"
    print(f"{c:6d}  #{si:<7d} {fentries[k][1].split('::')[-1][:28]:28s} {lib[:120]}")

# Optional: STMT=a,b,... dumps +-CTX statements around each with counts and resolved types.
types = {t["id"]["id"]: t for t in prog["type_declarations"]}


def tname(tid, depth=0):
    t = types.get(tid)
    if t is None or depth > 3:
        return str(tid)
    g = t["long_id"]
    args = []
    for a in g.get("generic_args", []):
        if "Type" in a:
            args.append(tname(a["Type"]["id"], depth + 1))
        elif "Value" in a:
            args.append(str(a["Value"]))
        elif "UserType" in a:
            args.append(str(a["UserType"].get("debug_name") or "")[-30:])
    return g["generic_id"] + ("<" + ",".join(args) + ">" if args else "")


def stmt_text(si):
    st = stmts[si]
    inv = st.get("Invocation")
    if not inv:
        return "return"
    d = next(l for l in prog["libfunc_declarations"] if l["id"]["id"] == inv["libfunc_id"]["id"])
    g = d["long_id"]
    args = [tname(a["Type"]["id"]) if "Type" in a else str(a.get("Value", ""))[:20]
            for a in g.get("generic_args", [])]
    ins = [str(v["id"]) for v in inv["args"]]
    outs = [[str(v["id"]) for v in b["results"]] for b in inv["branches"]]
    return f"{g['generic_id']}<{','.join(args)}>({','.join(ins)}) -> {outs}"


ctx = int(os.environ.get("CTX", "12"))
for s_ in filter(None, os.environ.get("STMT", "").split(",")):
    si = int(s_)
    print(f"--- around #{si}")
    for j in range(si - ctx, si + ctx + 1):
        print(f"{per_stmt.get(j, 0):6d}  #{j:<7d} {stmt_text(j)[:170]}")

if os.environ.get("BYFUNC"):
    agg = collections.Counter()
    for si, c in per_stmt.items():
        inv = stmts[si].get("Invocation")
        lib = re.sub(r"<.*", "", lib_names.get(inv["libfunc_id"]["id"], "?")) if inv else "return"
        k = bisect.bisect_right(fstarts, si) - 1
        agg[(fentries[k][1].split("::")[-1][:30], lib)] += c
    for (f_, l_), c in agg.most_common(40):
        print(f"{c:8d}  {f_:30s} {l_}")

if os.environ.get("KTYPES"):
    agg = collections.Counter()
    for si, c in per_stmt.items():
        k = bisect.bisect_right(fstarts, si) - 1
        if not fentries[k][1].endswith(os.environ["KTYPES"]):
            continue
        inv = stmts[si].get("Invocation")
        if not inv:
            continue
        t = stmt_text(si)
        key = re.sub(r"\(.*", "", t)
        agg[key] += c
    for k_, c in agg.most_common(40):
        print(f"{c:8d}  {k_[:150]}")

if os.environ.get("DUMPF"):
    want = os.environ["DUMPF"]
    i = next(k for k, (e, n) in enumerate(fentries) if n.endswith(want))
    st0, st1 = fentries[i][0], (fentries[i + 1][0] if i + 1 < len(fentries) else len(stmts))
    lo, hi = (int(x) for x in os.environ.get("RANGE", f"0,{st1 - st0}").split(","))
    with open(os.environ.get("OUT", "/work/dump.txt"), "w") as fh:
        for j in range(st0 + lo, min(st0 + hi, st1)):
            fh.write(f"{per_stmt.get(j, 0):6d}  #{j - st0:<6d} {stmt_text(j)[:200]}\n")
    print("dumped", st0, st1)
