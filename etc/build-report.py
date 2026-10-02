#!/usr/bin/env python3
"""Report on one build: how long it took, how parallel it was, and why.

`make ci` prints this after every build (see the Makefile); run it by hand
for any build recorded in the timing database:

    ./etc/build-report.py                      # the latest build
    ./etc/build-report.py --list               # the builds recorded
    ./etc/build-report.py --build ID
    ./etc/build-report.py --format markdown    # for a CI job summary
    ./etc/build-report.py --selftest

The data comes from etc/rocqc.py, which the Makefile runs around every
`rocq compile` and which records, per compile, when it started and ended, its
CPU time, peak memory and exit status, under the id of the `make` run it
belongs to (ROCQ_BUILD_ID, set once per top-level make). Dependencies come
from `.rocqdeps.d`. The report has five parts:

  - the totals: wall time from `make` starting to the last compile ending,
    CPU time, average and peak number of compiles running, the job slots
    `make -j` offered, and the time the build ran at most one compile;
  - parallelism over time, as a chart of running compiles;
  - the critical path *as it happened*: starting from the compile that
    finished last, each step is the dependency that finished last before
    it could start. "idle" is the gap between that dependency finishing and
    the file starting: time spent waiting for a free job slot (or, for the
    first step, for make to start up), not for a dependency. Next to it, the
    longest dependency chain by compile time: how long the build would take
    with unlimited cores;
  - the slowest files, with CPU time and peak memory;
  - where the CPU went, by directory.

A build that compiles nothing (everything up to date) has nothing to report.
Standard library only, so it runs wherever the build does.
"""

import argparse
import os
import sqlite3
import sys
import textwrap
from collections import defaultdict

DEFAULT_DB = ".timing.sqlite3"
DEFAULT_DEPS = ".rocqdeps.d"

# The dependency-file extension a build mode produces, and back.
MODE_EXT = {"vo": ".vo", "vos": ".vos", "vok": ".vok"}
EXT_MODE = {ext: mode for mode, ext in MODE_EXT.items()}

BLOCKS = " ▁▂▃▄▅▆▇█"


class Compile:
    """One `rocq compile` of one file, in one mode, within a build."""

    def __init__(self, fname, mode, start, end, user, sys_, maxrss_kb, status):
        self.fname = os.path.normpath(fname)
        self.mode = mode
        self.start = start
        self.end = end
        self.cpu = (user or 0.0) + (sys_ or 0.0)
        self.maxrss_kb = maxrss_kb or 0
        self.status = status

    @property
    def key(self):
        return (self.fname, self.mode)

    @property
    def time(self):
        return self.end - self.start


class Build:
    def __init__(self, build, start, goals, jobs, compiles):
        self.build = build
        self.compiles = compiles
        first = min(c.start for c in compiles)
        # The Makefile's start time, if recorded, covers `rocq dep` and make's
        # own start-up too; it can only be earlier than the first compile.
        self.start = min(start, first) if start is not None else first
        self.end = max(c.end for c in compiles)
        self.goals = goals or ""
        self.jobs = jobs

    @property
    def wall(self):
        return self.end - self.start

    @property
    def cpu(self):
        return sum(c.cpu for c in self.compiles)

    def failed(self):
        return [c for c in self.compiles if c.status != 0]


# --- reading the database --------------------------------------------------


def has_build_tables(conn):
    names = {r[0] for r in conn.execute("SELECT name FROM sqlite_master")}
    return "build_files" in names and "builds" in names


def list_builds(conn):
    """[(build, goals, jobs, files, start, end)], newest first."""
    if not has_build_tables(conn):
        return []
    rows = conn.execute(
        "SELECT f.build, b.goals, b.jobs, count(*), min(f.start), max(f.end) "
        "FROM build_files f LEFT JOIN builds b ON b.build = f.build "
        "GROUP BY f.build ORDER BY max(f.end) DESC"
    )
    return list(rows)


def load_build(conn, build=None):
    """The build called `build`, or the latest one; None if there is none."""
    if not has_build_tables(conn):
        return None
    if build is None:
        row = conn.execute(
            "SELECT build FROM build_files GROUP BY build ORDER BY max(end) DESC"
        ).fetchone()
        if row is None:
            return None
        build = row[0]
    compiles = [
        Compile(*r)
        for r in conn.execute(
            "SELECT fname, mode, start, end, user, sys, maxrss_kb, status "
            "FROM build_files WHERE build = ?",
            (build,),
        )
    ]
    if not compiles:
        return None
    meta = conn.execute(
        "SELECT start, goals, jobs FROM builds WHERE build = ?", (build,)
    ).fetchone() or (None, "", None)
    return Build(build, meta[0], meta[1], meta[2], compiles)


def read_deps(path):
    """{(file.v, mode): [(dep.v, mode), ...]} from a `rocq dep` makefile.

    A rule `a.vo a.glob ...: a.v b.vo c.vo` says a's vo build waits on b's
    and c's; the vos/vok rules name .vos dependencies the same way. Returns {}
    if the file is missing -- the report then just has no critical path.
    """
    deps = {}
    try:
        with open(path) as f:
            text = f.read().replace("\\\n", " ")
    except OSError:
        return deps
    for line in text.splitlines():
        if ":" not in line:
            continue
        lhs, rhs = line.split(":", 1)
        prereqs = []
        for word in rhs.split():
            base, ext = os.path.splitext(word)
            if ext in EXT_MODE:
                prereqs.append((os.path.normpath(base + ".v"), EXT_MODE[ext]))
        for target in lhs.split():
            base, ext = os.path.splitext(target)
            if ext in EXT_MODE:
                deps[(os.path.normpath(base + ".v"), EXT_MODE[ext])] = prereqs
    return deps


# --- analysis --------------------------------------------------------------


def concurrency_steps(compiles):
    """[(time, running)] -- the number of compiles running from each time on."""
    events = sorted(
        [(c.start, 1) for c in compiles] + [(c.end, -1) for c in compiles],
        key=lambda e: (e[0], e[1]),  # an end before a start at the same instant
    )
    steps, running = [], 0
    for t, d in events:
        running += d
        steps.append((t, running))
    return steps


def peak_concurrency(compiles):
    return max((n for _t, n in concurrency_steps(compiles)), default=0)


def time_at_most(compiles, t0, t1, limit):
    """Seconds in [t0, t1] during which at most `limit` compiles ran."""
    total, prev_t, running = 0.0, t0, 0
    for t, n in concurrency_steps(compiles) + [(t1, 0)]:
        if running <= limit:
            total += max(0.0, min(t, t1) - max(prev_t, t0))
        prev_t, running = t, n
    return total


def profile(compiles, t0, t1, columns):
    """Average number of compiles running in each of `columns` equal slices."""
    width = (t1 - t0) / columns if t1 > t0 else 0.0
    if width <= 0:
        return [0.0] * columns
    busy = [0.0] * columns
    for c in compiles:
        a, b = (c.start - t0) / width, (c.end - t0) / width
        for i in range(max(0, int(a)), min(columns, int(b) + 1)):
            busy[i] += max(0.0, min(b, i + 1) - max(a, i))
    return busy


def observed_critical_path(build, deps):
    """[(compile, waited)] from the first step to the compile that ended last.

    Each step is the dependency of the next that finished last, among those
    built in this build; `waited` is the time between that dependency (or the
    build's start) finishing and the step starting.
    """
    by_key = {c.key: c for c in build.compiles}
    step = max(build.compiles, key=lambda c: c.end)
    path = []
    while step is not None:
        built = [by_key[k] for k in deps.get(step.key, []) if k in by_key]
        blocker = max(built, key=lambda c: c.end, default=None)
        ready = blocker.end if blocker is not None else build.start
        path.append((step, max(0.0, step.start - ready)))
        step = blocker
    path.reverse()
    return path


def dependency_bound(build, deps):
    """The longest chain of dependent compiles in this build, by compile time:
    how long the build would take with unlimited cores. [compile] in order."""
    by_key = {c.key: c for c in build.compiles}
    # key -> (length of the longest chain ending here, the key before it)
    best = {}
    # A dependency ends before its dependent starts, so in order of end time
    # every compile's dependencies have been seen before it.
    for c in sorted(build.compiles, key=lambda c: c.end):
        prev = [(best[k][0], k) for k in deps.get(c.key, []) if k in best]
        length, before = max(prev, default=(0.0, None))
        best[c.key] = (length + c.time, before)
    if not best:
        return []
    key = max(best, key=lambda k: best[k][0])
    chain = []
    while key is not None:
        chain.append(by_key[key])
        key = best[key][1]
    chain.reverse()
    return chain


def directory(fname, depth=5):
    parts = os.path.dirname(fname).split(os.sep)
    return os.sep.join(parts[:depth]) or "."


def cpu_by_directory(compiles):
    """[(directory, cpu, files)], most CPU first."""
    cpu, files = defaultdict(float), defaultdict(int)
    for c in compiles:
        d = directory(c.fname)
        cpu[d] += c.cpu
        files[d] += 1
    return sorted(
        ((d, cpu[d], files[d]) for d in cpu), key=lambda r: r[1], reverse=True
    )


# --- formatting ------------------------------------------------------------


def dur(s):
    """A duration for people: 4.2s, 13m04s, 2h26m."""
    if s < 60:
        return f"{s:.1f}s"
    s = round(s)
    if s < 3600:
        return f"{s // 60}m{s % 60:02d}s"
    return f"{s // 3600}h{(s % 3600) // 60:02d}m"


def clock(s):
    """An offset from the build's start: 0:00, 12:51, 1:02:05."""
    s = round(s)
    if s < 3600:
        return f"{s // 60}:{s % 60:02d}"
    return f"{s // 3600}:{(s % 3600) // 60:02d}:{s % 60:02d}"


def mem(kb):
    if kb >= 1024 * 1024:
        return f"{kb / 1024 / 1024:.1f} GiB"
    return f"{kb / 1024:.0f} MiB"


def jobs_label(jobs):
    if jobs is None:
        return "-j unknown"
    return "-j" if jobs == 0 else f"-j{jobs}"


def chart(values, ymax, height, start_label, mid_label, end_label):
    """A column chart of `values` (0..ymax), `height` rows tall, as lines."""
    ymax = max(ymax, 1e-9)
    label_w = len(f"{ymax:.0f}")
    lines = []
    for row in range(height, 0, -1):
        cells = []
        for v in values:
            eighths = round(v / ymax * height * 8) - (row - 1) * 8
            cells.append(BLOCKS[max(0, min(8, eighths))])
        label = f"{ymax:.0f}" if row == height else ""
        if row == (height + 1) // 2 and height > 2:
            label = f"{ymax / 2:.0f}" if ymax >= 2 else ""
        lines.append(f"{label:>{label_w}} │{''.join(cells).rstrip()}")
    width = len(values)
    lines.append(f"{'0':>{label_w}} └{'─' * width}")
    axis = [" "] * (width + 1)
    for pos, text in ((0, start_label), (width // 2, mid_label), (width, end_label)):
        at = max(0, min(pos - len(text) // 2, width + 1 - len(text)))
        axis[at : at + len(text)] = list(text)
    lines.append(" " * (label_w + 1) + "".join(axis).rstrip())
    return lines


class Report:
    """Everything the report says, computed once, rendered as text or markdown."""

    def __init__(self, build, deps, top=15, columns=60, height=8):
        self.b = build
        self.top = top
        self.columns = columns
        self.height = height
        cs = build.compiles
        self.peak = peak_concurrency(cs)
        self.avg = sum(c.time for c in cs) / build.wall if build.wall > 0 else 0.0
        self.serial = time_at_most(cs, build.start, build.end, 1)
        self.saturated = (
            build.wall - time_at_most(cs, build.start, build.end, build.jobs - 1)
            if build.jobs
            else None
        )
        self.biggest = max(cs, key=lambda c: c.maxrss_kb)
        self.path = observed_critical_path(build, deps) if deps else []
        self.bound = dependency_bound(build, deps) if deps else []
        self.profile = profile(cs, build.start, build.end, columns)

    def title(self):
        b = self.b
        goals = f"make {b.goals}".strip() if b.goals else "make"
        return f"Build report: {goals} ({jobs_label(b.jobs)}), build {b.build}"

    def summary_rows(self):
        b, rows = self.b, []
        rows.append(
            ("wall time", dur(b.wall), "from make starting to the last compile")
        )
        failed = len(b.failed())
        rows.append(
            (
                "compiled",
                f"{len(b.compiles)} file{'s' if len(b.compiles) != 1 else ''}",
                f"{failed} failed" if failed else "none failed",
            )
        )
        rows.append(("CPU time", dur(b.cpu), "user + system, all compiles"))
        spent = sum(c.time for c in b.compiles)
        if spent > 0 and b.cpu > 0:
            share = b.cpu / spent
            note = "CPU ÷ wall time, per compile"
            if share < 0.9:
                note += "; well below 100%: the machine was oversubscribed"
            rows.append(("core share", f"{share:.0%}", note))
        slots = ""
        if b.jobs:
            slots = f" of {b.jobs} job slots ({self.avg / b.jobs:.0%} used)"
        rows.append(
            ("parallelism", f"{self.avg:.1f} average", f"{self.peak} peak{slots}")
        )
        if self.saturated is not None:
            rows.append(
                (
                    "all slots busy",
                    dur(self.saturated),
                    f"{self.saturated / b.wall:.0%} of the wall time" if b.wall else "",
                )
            )
        rows.append(
            (
                "one or none",
                dur(self.serial),
                f"{self.serial / b.wall:.0%} of the wall time ran at most one compile"
                if b.wall
                else "",
            )
        )
        rows.append(("peak memory", mem(self.biggest.maxrss_kb), self.biggest.fname))
        return rows

    def chart_lines(self):
        b = self.b
        ymax = max(b.jobs or 0, self.peak, 1)
        return chart(
            self.profile,
            ymax,
            self.height,
            "0:00",
            clock(b.wall / 2),
            clock(b.wall),
        )

    def chart_caption(self):
        per = self.b.wall / self.columns if self.columns else 0
        return f"compiles running, averaged over each {dur(per)} column"

    def path_rows(self):
        """[(start, time, waited, fname)] with short steps folded together."""
        if not self.path:
            return []
        threshold = 0.01 * self.b.wall
        rows, folded = [], None
        for c, waited in self.path:
            if c.time + waited >= threshold or c is self.path[-1][0]:
                if folded:
                    rows.append(folded)
                    folded = None
                rows.append(
                    (clock(c.start - self.b.start), dur(c.time), dur(waited), c.fname)
                )
            else:
                n, t = (folded[4], folded[5]) if folded else (0, 0.0)
                n, t = n + 1, t + c.time + waited
                folded = (
                    "",
                    dur(t),
                    "",
                    f"({n} shorter step{'s' if n > 1 else ''})",
                    n,
                    t,
                )
        if folded:
            rows.append(folded)
        return [r[:4] for r in rows]

    def path_caption(self):
        b = self.b
        spent = sum(c.time for c, _w in self.path)
        waited = sum(w for _c, w in self.path)
        text = (
            f"{len(self.path)} compiles: {dur(spent)} compiling and {dur(waited)} "
            f"idle (make starting up, or all job slots taken), of the "
            f"{dur(b.wall)} wall time"
        )
        if self.bound:
            bound = sum(c.time for c in self.bound)
            text += (
                f". With unlimited cores this build would take at least "
                f"{dur(bound)} (its longest dependency chain)"
            )
        return text

    def slow_rows(self):
        cs = sorted(self.b.compiles, key=lambda c: c.time, reverse=True)[: self.top]
        return [
            (
                dur(c.time),
                dur(c.cpu),
                mem(c.maxrss_kb),
                c.fname + ("" if c.mode == "vo" else f" [{c.mode}]"),
            )
            for c in cs
        ]

    def dir_rows(self, limit=10):
        total = self.b.cpu or 1.0
        return [
            (dur(cpu), f"{cpu / total:.0%}", str(n), d)
            for d, cpu, n in cpu_by_directory(self.b.compiles)[:limit]
        ]

    def failed_rows(self, limit=20):
        return [(str(c.status), c.fname) for c in self.b.failed()[:limit]]

    # -- renderers --

    def text(self):
        out = [self.title(), ""]
        w = max(len(r[0]) for r in self.summary_rows())
        for k, v, note in self.summary_rows():
            out.append(f"  {k:<{w}}  {v:>12}   {note}".rstrip())
        out += ["", f"Parallelism over time: {self.chart_caption()}"]
        out += ["  " + line for line in self.chart_lines()]
        if self.path:
            out += [
                "",
                "Critical path: the chain of dependencies the last compile waited on",
            ]
            out += textwrap.wrap(
                self.path_caption() + ".",
                width=86,
                initial_indent="  ",
                subsequent_indent="  ",
            )
            out.append(f"  {'start':>8} {'compile':>8} {'idle':>8}  file")
            for start, t, waited, f in self.path_rows():
                out.append(f"  {start:>8} {t:>8} {waited:>8}  {f}")
        out += ["", "Slowest files"]
        out.append(f"  {'time':>8} {'CPU':>8} {'memory':>9}  file")
        for t, cpu, m, f in self.slow_rows():
            out.append(f"  {t:>8} {cpu:>8} {m:>9}  {f}")
        out += ["", "Where the CPU went"]
        out.append(f"  {'CPU':>8} {'share':>6} {'files':>6}  directory")
        for cpu, share, n, d in self.dir_rows():
            out.append(f"  {cpu:>8} {share:>6} {n:>6}  {d}")
        if self.b.failed():
            out += ["", f"Failed compiles ({len(self.b.failed())})"]
            for status, f in self.failed_rows():
                out.append(f"  exit {status:>3}  {f}")
        return "\n".join(out) + "\n"

    def markdown(self):
        def table(header, rows, align):
            lines = ["| " + " | ".join(header) + " |", "|" + "|".join(align) + "|"]
            lines += [
                "| " + " | ".join(cell.replace("|", "\\|") for cell in r) + " |"
                for r in rows
            ]
            return lines

        out = [f"### {self.title()}", ""]
        out += table(
            ("", "", ""),
            [(k, f"**{v}**", n) for k, v, n in self.summary_rows()],
            ("---", "--:", "---"),
        )
        out += ["", f"**Parallelism over time**: {self.chart_caption()}", "", "```text"]
        out += self.chart_lines()
        out += ["```"]
        if self.path:
            out += [
                "",
                "**Critical path**: the chain of dependencies the last compile waited on. "
                + self.path_caption()
                + ".",
                "",
            ]
            out += table(
                ("start", "compile", "idle", "file"),
                [(s, t, w, f"`{f}`" if s else f) for s, t, w, f in self.path_rows()],
                ("--:", "--:", "--:", "---"),
            )
        out += [
            "",
            "<details><summary>Slowest files, and where the CPU went</summary>",
            "",
        ]
        out += table(
            ("time", "CPU", "memory", "file"),
            [(t, c, m, f"`{f}`") for t, c, m, f in self.slow_rows()],
            ("--:", "--:", "--:", "---"),
        )
        out += [""]
        out += table(
            ("CPU", "share", "files", "directory"),
            [(c, s, n, f"`{d}`") for c, s, n, d in self.dir_rows()],
            ("--:", "--:", "--:", "---"),
        )
        out += ["", "</details>"]
        if self.b.failed():
            out += ["", f"**Failed compiles** ({len(self.b.failed())})", ""]
            out += [f"- `{f}` (exit {s})" for s, f in self.failed_rows()]
        return "\n".join(out) + "\n"


# --- selftest --------------------------------------------------------------


def selftest():
    """Check the analysis against a four-file build worked out by hand."""
    import tempfile

    failures, checks = [], []

    def check(name, cond):
        print(("ok   " if cond else "FAIL ") + name)
        checks.append(name)
        if not cond:
            failures.append(name)

    #   a: 0-10    b (needs a): 10-30    c (needs a): 10-15
    #   d (needs b, c): 31-40, one second after b -- a wait for a job slot
    #   e (needs nothing): 0-2, failed
    with tempfile.TemporaryDirectory() as tmp:
        db = os.path.join(tmp, "t.sqlite3")
        deps = os.path.join(tmp, "deps.d")
        with open(deps, "w") as f:
            f.write("x/a.vo x/a.glob: x/a.v\n")
            f.write("x/b.vo x/b.glob: x/b.v x/a.vo\n")
            f.write("x/c.vo: x/c.v ./x/a.vo \\\n  \n")
            f.write("x/d.vo x/d.glob x/d.required_vo: x/d.v x/b.vo x/c.vo\n")
            f.write("x/d.vos x/d.vok: x/d.v x/b.vos x/c.vos\n")
        conn = sqlite3.connect(db)
        conn.execute(
            "CREATE TABLE builds (build text PRIMARY KEY, start real, goals text, "
            "jobs integer)"
        )
        conn.execute(
            "CREATE TABLE build_files (build text, fname text, mode text, "
            "start real, end real, user real, sys real, maxrss_kb integer, "
            "status integer, PRIMARY KEY (build, fname, mode))"
        )
        conn.execute("INSERT INTO builds VALUES ('old', 0, 'ci', 2)")
        conn.execute("INSERT INTO builds VALUES ('b1', 999.0, 'ci', 2)")
        conn.execute("INSERT INTO build_files VALUES ('old','x/a.v','vo',0,1,1,0,1,0)")
        for fname, s, e, rss, status in [
            ("x/a.v", 0, 10, 1000, 0),
            ("x/b.v", 10, 30, 3_000_000, 0),
            ("x/c.v", 10, 15, 500, 0),
            ("./x/d.v", 31, 40, 800, 0),
            ("x/e.v", 0, 2, 100, 1),
        ]:
            conn.execute(
                "INSERT INTO build_files VALUES ('b1',?,'vo',?,?,?,0,?,?)",
                (fname, 1000.0 + s, 1000.0 + e, (e - s) * 0.9, rss, status),
            )
        conn.commit()

        check("latest build is picked", load_build(conn).build == "b1")
        check(
            "builds are listed newest first",
            [r[0] for r in list_builds(conn)] == ["b1", "old"],
        )
        b = load_build(conn, "b1")
        d = read_deps(deps)
        check(
            "deps: continuation lines and ./ are normalised",
            d[("x/c.v", "vo")] == [("x/a.v", "vo")],
        )
        check(
            "deps: vos rules are kept apart",
            d[("x/d.v", "vos")] == [("x/b.v", "vos"), ("x/c.v", "vos")],
        )
        check("wall time runs from make's start", abs(b.wall - 41.0) < 1e-9)
        check("peak concurrency", peak_concurrency(b.compiles) == 2)
        check(
            "one or none",
            abs(time_at_most(b.compiles, b.start, b.end, 1) - 34.0) < 1e-9,
        )
        prof = profile(b.compiles, b.start, b.end, 41)
        check("profile integrates to total compile time", abs(sum(prof) - 46.0) < 1e-9)
        path = observed_critical_path(b, d)
        check(
            "critical path a -> b -> d",
            [c.fname for c, _w in path] == ["x/a.v", "x/b.v", "x/d.v"],
        )
        check("critical path waits", [round(w, 6) for _c, w in path] == [1.0, 0.0, 1.0])
        check(
            "dependency bound a -> b -> d",
            [c.fname for c in dependency_bound(b, d)] == ["x/a.v", "x/b.v", "x/d.v"],
        )
        check("failed compiles", [c.fname for c in b.failed()] == ["x/e.v"])
        r = Report(b, d, columns=20, height=4)
        text, md = r.text(), r.markdown()
        check(
            "text has every section",
            all(
                s in text
                for s in (
                    "wall time",
                    "Parallelism over time",
                    "Critical path",
                    "Slowest files",
                    "Where the CPU went",
                    "Failed compiles",
                )
            ),
        )
        check(
            "text says 41.0s and 39.0s",
            "41.0s" in text and "at least 39.0s" in " ".join(text.split()),
        )
        check(
            "markdown has a table and the chart",
            "| wall time |" in md and "```text" in md,
        )
        check(
            "chart is as wide as asked",
            all(len(line) <= 4 + 20 for line in r.chart_lines()[:-1]),
        )
        check(
            "nothing recorded is not an error",
            load_build(sqlite3.connect(":memory:")) is None,
        )
        check(
            "durations", [dur(4.25), dur(784), dur(8760)] == ["4.2s", "13m04s", "2h26m"]
        )
        conn.close()
    print(f"{len(checks) - len(failures)}/{len(checks)} passed")
    return 1 if failures else 0


# --- main ------------------------------------------------------------------


def main(argv=None):
    p = argparse.ArgumentParser(
        description="Report on one build from etc/rocqc.py's timing database."
    )
    p.add_argument(
        "--db", default=DEFAULT_DB, help=f"timing database (default {DEFAULT_DB})"
    )
    p.add_argument(
        "--deps", default=DEFAULT_DEPS, help=f"rocq dep output (default {DEFAULT_DEPS})"
    )
    p.add_argument("--build", help="the build to report on (default: the latest)")
    p.add_argument(
        "--list", action="store_true", help="list the recorded builds and exit"
    )
    p.add_argument("--format", choices=("text", "markdown"), default="text")
    p.add_argument(
        "--markdown-to",
        metavar="FILE",
        help="also append the markdown report to FILE (e.g. $GITHUB_STEP_SUMMARY)",
    )
    p.add_argument(
        "--top", type=int, default=15, help="slowest files to list (default 15)"
    )
    p.add_argument("--width", type=int, default=60, help="chart columns (default 60)")
    p.add_argument("--selftest", action="store_true", help="run the tests and exit")
    args = p.parse_args(argv)

    if args.selftest:
        return selftest()
    if not os.path.exists(args.db):
        print(f"build-report: no timing database at {args.db}", file=sys.stderr)
        return 0
    conn = sqlite3.connect(args.db)
    if args.list:
        for build, goals, jobs, n, start, end in list_builds(conn):
            label = f"make {goals}".strip() if goals else "make"
            print(
                f"{build}  {label} ({jobs_label(jobs)})  {n} files  {dur(end - start)}"
            )
        return 0
    build = load_build(conn, args.build)
    if build is None:
        what = f"build {args.build}" if args.build else "the latest build"
        print(f"build-report: {what} compiled nothing; nothing to report")
        return 0
    report = Report(build, read_deps(args.deps), top=args.top, columns=args.width)
    sys.stdout.write(report.markdown() if args.format == "markdown" else report.text())
    if args.markdown_to:
        with open(args.markdown_to, "a") as f:
            f.write(report.markdown())
    return 0


if __name__ == "__main__":
    sys.exit(main())
