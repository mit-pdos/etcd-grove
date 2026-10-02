#!/usr/bin/env python3

# rocq compile wrapper
#
# Runs `rocq compile`, filters its `-time` output, and records how long each
# file and each Qed took. Three things come out of a build:
#
#   - a per-file line on stdout as each file finishes (--print-time),
#   - a row per file in the `file_timings` table (--timing-db),
#   - a row per Qed in the `qed_timings` table,
#   - when the Makefile has set ROCQ_BUILD_ID, a row per compile in
#     `build_files` (start, end, CPU, peak memory, exit status), and one per
#     build in `builds`.
#
# `file_timings` and `qed_timings` keep the latest time for each file, across
# builds; `build_files` keeps every build apart, which is what makes a
# per-build report possible. `etc/timing-report.py` reads the former back,
# `etc/build-report.py` the latter. Run `./etc/rocqc.py --selftest` to check
# this file against the fixtures in etc/test_coqc/.


import os
import re
import resource
import sqlite3
import subprocess
import sys
from datetime import datetime, timezone
from os import path

# How a file was built. `rocq compile` is invoked once per mode, and the same
# file costs wildly different amounts in each, so the mode is part of a
# timing's identity rather than a detail of it.
MODES = ("vo", "vos", "vok")

FILE_TIMINGS_SCHEMA = (
    """CREATE TABLE IF NOT EXISTS file_timings """
    + """(fname text NOT NULL, mode text NOT NULL, time real, """
    + """PRIMARY KEY (fname, mode) )"""
)

# One row per `make` run that compiled anything: its id and start time (both
# set once by the Makefile), the goals it was given, and its -j.
BUILDS_SCHEMA = (
    """CREATE TABLE IF NOT EXISTS builds """
    + """(build text NOT NULL PRIMARY KEY, start real, goals text, jobs integer)"""
)

# One row per compile within a build. Times are seconds since the epoch;
# user/sys are the CPU seconds of `rocq compile` and its children, maxrss_kb
# their peak resident memory. A failed compile is recorded too (status != 0).
BUILD_FILES_SCHEMA = (
    """CREATE TABLE IF NOT EXISTS build_files """
    + """(build text NOT NULL, fname text NOT NULL, mode text NOT NULL, """
    + """start real NOT NULL, end real NOT NULL, user real, sys real, """
    + """maxrss_kb integer, status integer NOT NULL, """
    + """PRIMARY KEY (build, fname, mode) )"""
)


def make_jobs(makeflags):
    """The -j of the `make` that ran us, from $MAKEFLAGS: 0 for an unbounded
    `-j`, 1 when there is none, None when we were not run by make."""
    if makeflags is None:
        return None
    m = re.search(r"(?:^|\s)-j(\d*)(?:\s|$)", makeflags)
    if m is None:
        return 1
    return int(m.group(1)) if m.group(1) else 0


class BuildInfo:
    """The build a compile belongs to, from the environment the Makefile sets.
    None of it is required: without ROCQ_BUILD_ID nothing per-build is kept."""

    def __init__(self, build, start, goals, jobs):
        self.build = build
        self.start = start
        self.goals = goals
        self.jobs = jobs

    @classmethod
    def from_env(cls, env=None):
        env = os.environ if env is None else env
        build = env.get("ROCQ_BUILD_ID")
        if not build:
            return None
        try:
            start = float(env.get("ROCQ_BUILD_START", ""))
        except ValueError:
            start = None
        return cls(
            build,
            start,
            env.get("ROCQ_BUILD_GOALS", ""),
            make_jobs(env.get("MAKEFLAGS")),
        )


class NullDb:
    def add_qed(self, fname, ident, time):
        pass

    def add_file(self, fname, mode, time):
        pass

    def add_build_file(self, info, fname, mode, start, end, usage, status):
        pass

    def close(self):
        pass


class StdoutDb:
    def add_qed(self, fname, ident, time):
        base = path.basename(fname)
        if time > 0.1:
            print(f"{base:15s} {ident:20s} {time:0.2f}")

    def add_file(self, fname, mode, time):
        if time > 0.1:
            print(f"{fname} [{mode}] {time:0.2f}")

    def add_build_file(self, info, fname, mode, start, end, usage, status):
        pass

    def close(self):
        pass


class TimingDb:
    def __init__(self, conn):
        self.conn = conn

    @classmethod
    def from_file(cls, fname):
        conn = sqlite3.connect(fname, isolation_level=None, timeout=20)
        conn.execute("""PRAGMA synchronous=off""")
        conn.execute(
            """CREATE TABLE IF NOT EXISTS qed_timings """
            + """(fname text NOT NULL, ident text NOT NULL, time real NOT NULL, """
            + """PRIMARY KEY (fname, ident) )"""
        )
        migrate_file_timings(conn)
        conn.execute(FILE_TIMINGS_SCHEMA)
        conn.execute(BUILDS_SCHEMA)
        conn.execute(BUILD_FILES_SCHEMA)
        return cls(conn)

    def add_qed(self, fname, ident, time):
        self.conn.execute(
            """INSERT OR REPLACE INTO qed_timings VALUES (?,?,?)""",
            (fname, ident, time),
        )

    def add_file(self, fname, mode, time):
        self.conn.execute(
            """INSERT OR REPLACE INTO file_timings VALUES (?,?,?)""",
            (fname, mode, time),
        )

    def add_build_file(self, info, fname, mode, start, end, usage, status):
        """Record one compile of build `info`; `usage` is a
        (user, sys, maxrss_kb) triple, or None if it could not be measured."""
        if info is None:
            return
        user, sys_, maxrss = usage if usage is not None else (None, None, None)
        # Every compile of a build offers the same builds row; the first wins.
        self.conn.execute(
            """INSERT OR IGNORE INTO builds VALUES (?,?,?,?)""",
            (info.build, info.start, info.goals, info.jobs),
        )
        self.conn.execute(
            """INSERT OR REPLACE INTO build_files VALUES (?,?,?,?,?,?,?,?,?)""",
            (info.build, fname, mode, start, end, user, sys_, maxrss, status),
        )

    def close(self):
        self.conn.close()


def child_usage():
    """(user, sys, maxrss_kb) of the children this process has waited for.

    rocqc.py runs exactly one `rocq compile` (which may run its own worker
    process; waited-for descendants are included), so this is that
    compile's cost. ru_maxrss is in KiB on Linux and bytes on macOS.
    """
    try:
        ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    except (OSError, ValueError):
        return None
    maxrss = ru.ru_maxrss // 1024 if sys.platform == "darwin" else ru.ru_maxrss
    return (ru.ru_utime, ru.ru_stime, maxrss)


def file_timings_columns(conn):
    return [row[1] for row in conn.execute("""PRAGMA table_info(file_timings)""")]


def migrate_file_timings(conn):
    """Bring a pre-2026-09-21 `file_timings` up to the (fname, mode) schema.

    The old table was keyed on fname alone and carried an `is_vos` flag, so a
    vok build silently overwrote the vo timing for the same file and the two
    could not be told apart afterwards. Legacy rows are kept, with is_vos
    mapped to 'vos'/'vo'; a vok row recorded under the old schema is
    indistinguishable from a vo one and stays labelled 'vo'.

    Idempotent, and safe to race with other `make -j` workers: the check is
    repeated inside an exclusive transaction.
    """
    cols = file_timings_columns(conn)
    if not cols or "mode" in cols:
        # No table yet (the caller creates it), or already migrated.
        return
    conn.execute("""BEGIN IMMEDIATE""")
    try:
        if "mode" in file_timings_columns(conn):
            conn.execute("""COMMIT""")
            return
        conn.execute("""ALTER TABLE file_timings RENAME TO file_timings_legacy""")
        conn.execute(FILE_TIMINGS_SCHEMA)
        conn.execute(
            """INSERT OR REPLACE INTO file_timings (fname, mode, time) """
            + """SELECT fname, CASE is_vos WHEN 1 THEN 'vos' ELSE 'vo' END, time """
            + """FROM file_timings_legacy"""
        )
        conn.execute("""DROP TABLE file_timings_legacy""")
        conn.execute("""COMMIT""")
    except Exception:
        conn.execute("""ROLLBACK""")
        raise


class Classify:
    # `\w` is ASCII-only in a bytes pattern, so an identifier is spelled here
    # as "word bytes, quotes, or any byte of a UTF-8 multibyte sequence".
    # Without the [\x80-\xff] alternative, Goose's `Definition fooⁱᵐᵖˡ` is
    # recorded as "foo", which collides with a plain `foo` in the same file
    # and silently overwrites its timing.
    IDENT_RE = rb"""(?P<ident>(?:\w|[\x80-\xff])(?:\w|'|[\x80-\xff])*)"""
    DEF_RE = re.compile(
        rb"""(?:#\[(local|global|export)\]\s+)?(?:(Local|Global)\s+)?(?:Theorem|Lemma|Instance|Definition|Corollary|Remark|Fact|Program Lemma)\s+"""
        + IDENT_RE
    )
    OBLIGATION_RE = re.compile(rb"""(Next Obligation\.)|(Final Obligation\.)""")
    GOAL_RE = re.compile(rb"""\s*Goal\s+""")
    TIME_RE = re.compile(
        rb"""Chars (?P<start>\d*) - (?P<end>\d*) \[.*\] """
        + rb"""(?P<time>[0-9.]*) secs .*"""
    )
    QED_RE = re.compile(rb"""(?:Time\s*)?Qed\.""")
    obligation_count = 0
    goal_count = 0

    @classmethod
    def is_qed(cls, s):
        return cls.QED_RE.match(s) is not None

    @classmethod
    def get_def(cls, s):
        m = cls.DEF_RE.match(s)
        if m is not None:
            # errors="replace": the match can in principle end mid-character
            # if Rocq's char window cuts one, and a mangled name in a timing
            # report is better than a crashed build.
            return m.group("ident").decode("utf-8", errors="replace")
        m = cls.OBLIGATION_RE.match(s)
        if m is not None:
            cls.obligation_count += 1
            return f"<obligation {cls.obligation_count}>"
        m = cls.GOAL_RE.match(s)
        if m is not None:
            cls.goal_count += 1
            return f"<goal {cls.goal_count}>"
        return None

    @classmethod
    def get_time(cls, s):
        m = cls.TIME_RE.match(s)
        if m is None:
            return None
        return (
            int(m.group("start")),
            int(m.group("end")),
            float(m.group("time")),
        )


class CoqcFilter:
    def __init__(self, vfile, mode, db, contents, start, print_time=None, build=None):
        self.vfile = vfile
        self.mode = mode
        self.contents = contents
        self.db = db
        self.start = start
        # Seconds a file must take before its time is printed, or None to
        # print nothing.
        self.print_time = print_time
        # The BuildInfo this compile belongs to, or None to keep no per-build row.
        self.build = build
        self.curr_def = None

    @classmethod
    def from_coqargs(
        cls, args, db, contents=None, start=None, print_time=None, build=None
    ):
        """Extract the build mode and the input vfile from rocq compile's arguments."""
        if "-vos" in args:
            mode = "vos"
        elif "-vok" in args:
            mode = "vok"
        else:
            mode = "vo"
        vfile = None
        for arg in args:
            if arg.endswith(".v"):
                vfile = arg
                break
        if start is None:
            start = datetime.now(timezone.utc)
        return cls(vfile, mode, db, contents, start, print_time=print_time, build=build)

    @classmethod
    def from_contents(cls, contents, db, start=None):
        return cls("<in-memory>.v", "vo", db, contents, start)

    def _read_vfile(self):
        with open(self.vfile, "rb") as f:
            self.contents = f.read()

    def chars(self, start, end):
        if not self.contents:
            self._read_vfile()
        return self.contents[start:end]

    def update_def(self, ident):
        """Update current definition to ident."""
        self.curr_def = ident

    def update_timing(self, timing_info):
        """Add new timing info based on Classify.get_time."""
        start, end, time = timing_info
        code = self.chars(start, end)
        ident = Classify.get_def(code)
        if ident:
            return self.update_def(ident)
        if Classify.is_qed(code):
            if self.curr_def is None:
                print(
                    self.vfile,
                    f"no proof ident {start} - {end}",
                    file=sys.stderr,
                )
                return
            self.db.add_qed(self.vfile, self.curr_def, time)
            return

    def line(self, ln):
        """Process a line of output from rocq compile."""
        timing_info = Classify.get_time(ln)
        if timing_info:
            return self.update_timing(timing_info)

        sys.stdout.buffer.write(ln)

    def elapsed(self, end_t=None):
        if end_t is None:
            end_t = datetime.now(timezone.utc)
        return (end_t - self.start).total_seconds()

    def report(self, delta):
        """Print this file's build time, if it is over the print threshold.

        One line per file, so that `make -j` output still says which files a
        build is actually spending its time in. The fixed-width seconds field
        makes the line sortable: `grep 'ROCQ TIME' log | sort -rn -k3`.
        """
        if self.print_time is None or delta < self.print_time:
            return
        print(f"ROCQ TIME {delta:8.2f}s {self.mode:3s} {self.vfile}")
        sys.stdout.flush()

    def done(self, end_t=None, record=True, status=0, usage=None):
        """Finish: record the file's time if `record`, and -- whatever the
        outcome -- this compile's row in its build, with exit `status` and
        resource `usage` (see child_usage)."""
        if end_t is None:
            end_t = datetime.now(timezone.utc)
        delta = self.elapsed(end_t)
        if record:
            self.db.add_file(self.vfile, self.mode, delta)
            self.report(delta)
        if self.build is not None:
            self.db.add_build_file(
                self.build,
                self.vfile,
                self.mode,
                self.start.timestamp(),
                end_t.timestamp(),
                usage,
                status,
            )
        self.db.close()


def selftest():
    """Run etc/test_coqc.py's checks without pytest, and exit non-zero on failure."""
    import inspect
    import io
    import traceback

    sys.path.insert(0, path.dirname(path.realpath(__file__)))
    import test_coqc

    class Captured:
        def __init__(self, out, err):
            self.out = out
            self.err = err

    class CapsysShim:
        """The slice of pytest's capsys fixture that test_coqc.py uses."""

        def __init__(self):
            self._out = io.TextIOWrapper(io.BytesIO(), write_through=True)
            self._err = io.TextIOWrapper(io.BytesIO(), write_through=True)
            self._saved = None

        def __enter__(self):
            self._saved = (sys.stdout, sys.stderr)
            sys.stdout, sys.stderr = self._out, self._err
            return self

        def __exit__(self, *exc):
            sys.stdout, sys.stderr = self._saved
            return False

        def readouterr(self):
            return Captured(
                self._out.buffer.getvalue().decode("utf-8"),
                self._err.buffer.getvalue().decode("utf-8"),
            )

    tests = [
        (name, fn)
        for name, fn in sorted(vars(test_coqc).items())
        if name.startswith("test_") and callable(fn)
    ]
    failures = 0
    for name, fn in tests:
        # Classify counts obligations and goals in class variables, so each
        # test has to start from a clean slate.
        Classify.obligation_count = 0
        Classify.goal_count = 0
        # Every test runs under the shim, not just the one that asks for it:
        # CoqcFilter passes rocq's non-timing output straight through, and
        # the fixtures have plenty of it.
        shim = CapsysShim()
        wants_capsys = "capsys" in inspect.signature(fn).parameters
        try:
            with shim:
                fn(shim) if wants_capsys else fn()
        except Exception:  # noqa: BLE001 - a test runner reports every failure
            failures += 1
            print(f"FAIL {name}")
            traceback.print_exc()
        else:
            print(f"ok   {name}")
    print(f"{len(tests) - failures}/{len(tests)} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--no-timing", action="store_true", help="disable all timing tracking"
    )

    parser.add_argument(
        "--timing-db", default=None, help="database to store timing info"
    )

    parser.add_argument(
        "--print-time",
        type=float,
        nargs="?",
        const=0.0,
        default=None,
        metavar="SECS",
        help="print each file's build time as it finishes, "
        + "if it took at least SECS (default 0, i.e. every file)",
    )

    parser.add_argument(
        "--selftest",
        action="store_true",
        help="run this file's tests against etc/test_coqc/ and exit",
    )

    args, coq_args = parser.parse_known_args()

    if args.selftest:
        sys.exit(selftest())

    if args.no_timing:
        db = NullDb()
    elif args.timing_db:
        db = TimingDb.from_file(args.timing_db)
    else:
        db = StdoutDb()

    rocq_args = ["rocq", "compile"]
    rocq_args.append("-time")
    rocq_args += ["-set", "Printing Width=1000000"]
    rocq_args.extend(coq_args)

    filter = CoqcFilter.from_coqargs(
        coq_args, db, print_time=args.print_time, build=BuildInfo.from_env()
    )

    p = subprocess.Popen(rocq_args, stdout=subprocess.PIPE, stderr=sys.stderr)
    try:
        for line in iter(p.stdout.readline, b""):
            filter.line(line)
    except KeyboardInterrupt:
        p.kill()
        p.wait()
        db.close()
        sys.exit(p.returncode)
    p.wait()
    # A failed compile's elapsed time is not what that file costs to build, so
    # it is neither recorded nor printed -- it would otherwise overwrite the
    # last good timing with the time taken to reach an error. Its build row is
    # kept, marked failed: a build report should say what failed.
    filter.done(record=p.returncode == 0, status=p.returncode, usage=child_usage())
    sys.exit(p.returncode)
