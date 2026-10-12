#!/usr/bin/env python3
"""Run `lake build`, recording how long each module compile took.

    ./etc/timed-build.py [--dir DIR] [--] [LAKE_ARGS...]
    ./etc/timed-build.py --selftest

Runs `lake build LAKE_ARGS` with Lake pointed at a copy of the Lean toolchain
(`.lake/build-report/sysroot`, symlinks to the real one) whose `bin/lean` is a
shim back into this script. The shim runs the real `lean` and records, for
every module compile (of any package, Perennial's too), when it started and
ended, its CPU time, peak memory and exit status, in
`.lake/build-report/<build>.jsonl` (DIR/<build>.jsonl with --dir). Lake does
not hash the `lean` path into its traces, so this is `lake build`: it rebuilds
exactly what a plain `lake build` would, leaves the same build behind, and
exits with Lake's status. Only the modules it compiles are timed; one a plain
`lake build` compiled stays up to date, and untimed, until it changes.

`etc/build-report.py` reports on the recorded builds (it only reads them).
Standard library only.
"""

import json
import os
import shlex
import shutil
import signal
import subprocess
import sys
import time

DEFAULT_DIR = os.path.join(".lake", "build-report")


def wrap(real_lean, log, args):
    """Run the real `lean` on `args`; if it compiles a module, record it.

    Lake also runs `lean --githash` and the like; only invocations with a
    `.lean` source are recorded.
    """
    src = next((a for a in args if a.endswith(".lean")), None)
    start = time.time()
    pid = os.fork()
    if pid == 0:
        try:
            os.execv(real_lean, [real_lean] + args)
        finally:
            os._exit(127)
    # Lake's Ctrl-C reaches the real lean too; let it decide, and report it.
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    while True:
        try:
            _pid, status, ru = os.wait4(pid, 0)
            break
        except InterruptedError:
            continue
    end = time.time()
    code = os.waitstatus_to_exitcode(status)
    if src is not None:
        setup = None
        if "--setup" in args and args.index("--setup") + 1 < len(args):
            setup = args[args.index("--setup") + 1]
        record = {
            "file": src,
            "setup": setup,
            "start": start,
            "end": end,
            "user": ru.ru_utime,
            "sys": ru.ru_stime,
            "maxrss_kb": ru.ru_maxrss,
            "status": code,
        }
        # One short O_APPEND write per line: concurrent shims don't interleave.
        with open(log, "a") as f:
            f.write(json.dumps(record) + "\n")
    return code if code >= 0 else 128 - code


def real_sysroot():
    """The Lean toolchain `lean` resolves to here (via elan and lean-toolchain)."""
    out = subprocess.run(
        ["lean", "--print-prefix"], capture_output=True, text=True, check=True
    )
    return out.stdout.strip()


def make_sysroot(root, real, log):
    """A copy of the toolchain at `root`, all symlinks except a `bin/lean` shim."""
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(os.path.join(root, "bin"))
    for name in os.listdir(real):
        if name != "bin":
            os.symlink(os.path.join(real, name), os.path.join(root, name))
    for name in os.listdir(os.path.join(real, "bin")):
        if name != "lean":
            os.symlink(os.path.join(real, "bin", name), os.path.join(root, "bin", name))
    shim = os.path.join(root, "bin", "lean")
    cmd = [
        sys.executable,
        "-I",
        os.path.abspath(__file__),
        "--wrap",
        os.path.join(real, "bin", "lean"),
        os.path.abspath(log),
    ]
    with open(shim, "w") as f:
        f.write(f'#!/bin/sh\nexec {shlex.join(cmd)} "$@"\n')
    os.chmod(shim, 0o755)


def run_build(outdir, lake_args):
    """Run `lake build lake_args` under the shim; (build id, lake's exit status)."""
    os.makedirs(outdir, exist_ok=True)
    start = time.time()
    build = time.strftime("%Y%m%d-%H%M%S", time.localtime(start)) + f"-{os.getpid()}"
    log = os.path.join(outdir, build + ".jsonl")
    with open(log, "w") as f:
        meta = {
            "build": build,
            "start": start,
            "args": lake_args,
            "cores": os.cpu_count(),
        }
        f.write(json.dumps({"meta": meta}) + "\n")
    root = os.path.join(outdir, "sysroot")
    make_sysroot(root, real_sysroot(), log)
    env = dict(
        os.environ, LAKE_OVERRIDE_LEAN="true", LEAN_SYSROOT=os.path.abspath(root)
    )
    status = subprocess.call(["lake", "build"] + lake_args, env=env)
    with open(log, "a") as f:
        f.write(json.dumps({"done": {"end": time.time(), "status": status}}) + "\n")
    return build, status


def selftest():
    """Check the shim against a fake `lean`."""
    import tempfile

    failures, checks = [], []

    def check(name, cond):
        print(("ok   " if cond else "FAIL ") + name)
        checks.append(name)
        if not cond:
            failures.append(name)

    with tempfile.TemporaryDirectory() as tmp:
        # A fake `lean` that compiles only when given a .lean file.
        fake = os.path.join(tmp, "lean")
        with open(fake, "w") as f:
            f.write('#!/bin/sh\ncase "$*" in *--fail*) exit 3;; esac\necho out\n')
        os.chmod(fake, 0o755)
        wlog = os.path.join(tmp, "w.jsonl")
        script = os.path.abspath(__file__)

        def shim(*args):
            return subprocess.run(
                [sys.executable, "-I", script, "--wrap", fake, wlog, *args],
                capture_output=True,
                text=True,
                check=False,
            )

        p = shim("--githash")
        check("shim passes stdout through", p.stdout == "out\n")
        check("shim records nothing for non-compiles", not os.path.exists(wlog))
        shim("M.lean", "--setup", "M.setup.json", "--json")
        p = shim("N.lean", "--fail")
        check("shim passes the exit status through", p.returncode == 3)
        with open(wlog) as f:
            recs = [json.loads(line) for line in f]
        check(
            "shim records compiles",
            [(r["file"], r["setup"], r["status"]) for r in recs]
            == [("M.lean", "M.setup.json", 0), ("N.lean", None, 3)],
        )
    print(f"{len(checks) - len(failures)}/{len(checks)} passed")
    return 1 if failures else 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    # The shim: --wrap REAL_LEAN LOG ARGS..., everything after passed to lean.
    if argv[:1] == ["--wrap"]:
        return wrap(argv[1], argv[2], argv[3:])
    if argv in (["-h"], ["--help"]):
        print(__doc__.strip())
        return 0
    if argv == ["--selftest"]:
        return selftest()
    outdir = DEFAULT_DIR
    if argv[:1] == ["--dir"] and len(argv) > 1:
        outdir, argv = argv[1], argv[2:]
    if argv[:1] == ["--"]:
        argv = argv[1:]
    build, status = run_build(outdir, argv)
    print(f"timed-build: recorded build {build} in {outdir} (lake exited {status}); "
          "`etc/build-report.py` reports on it", file=sys.stderr)
    return status


if __name__ == "__main__":
    sys.exit(main())
