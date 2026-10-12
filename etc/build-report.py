#!/usr/bin/env python3
"""Report how long a recorded build took, how parallel it was, and why.

    ./etc/build-report.py                       # the latest recorded build
    ./etc/build-report.py --list                # the builds recorded
    ./etc/build-report.py --build ID
    ./etc/build-report.py --format markdown     # for a CI job summary
    ./etc/build-report.py --selftest

It only reads: the builds are those `etc/timed-build.py` ran and recorded,
one `.lake/build-report/<build>.jsonl` each (every module compile's start,
end, CPU time, peak memory and exit status); a plain `lake build` records
nothing. Dependencies are the imports Lake writes to each module's
`.setup.json` (read when the report is made, so a report on an old build uses
the current imports).

The report has five parts:

  - the totals: wall time from `lake` starting to the last compile ending,
    CPU time, average and peak number of compiles running, the machine's
    cores, the time all of them ran a compile, and the time the build ran at
    most one. Lake runs at most one compile per core (observed: never more,
    and runs pinned at the core count), so the cores are its job slots;
  - parallelism over time, as charts of compiles running and of cores busy
    (a Lean compile elaborates declarations in parallel, so it can keep more
    than one core busy);
  - the critical path *as it happened*: starting from the compile that
    finished last, each step is the import that finished last before it
    could start. "idle" is the gap between that import finishing and the
    module starting: a wait for a free slot (all cores running compiles), or
    Lake's own work between compiles, or, for the first step, Lake loading
    the workspace.
    Next to it, the longest import chain by compile time: how long the build
    would take with unlimited cores;
  - the slowest modules, with CPU time and peak memory;
  - where the CPU went, by package and module prefix.

A build that compiles nothing (everything up to date) has nothing to report.
Standard library only.
"""

import argparse
import json
import os
import sys
import textwrap
from collections import defaultdict

DEFAULT_DIR = os.path.join(".lake", "build-report")

BLOCKS = " ▁▂▃▄▅▆▇█"

# Module-name components to group CPU time by (after the package name).
GROUP_DEPTH = 3


# --- reading a build -------------------------------------------------------


class Compile:
    """One `lean` compile of one module within a build."""

    def __init__(self, rec):
        self.file = rec["file"]
        self.setup = rec.get("setup")
        self.start = rec["start"]
        self.end = rec["end"]
        self.cpu = (rec.get("user") or 0.0) + (rec.get("sys") or 0.0)
        self.maxrss_kb = rec.get("maxrss_kb") or 0
        self.status = rec.get("status", 0)
        # Filled in from the setup file, when there is one.
        self.module = os.path.splitext(os.path.basename(self.file))[0]
        self.package = ""
        self.imports = []

    @property
    def time(self):
        return self.end - self.start


class Build:
    def __init__(self, meta, compiles, done=None):
        self.build = meta.get("build", "?")
        self.args = meta.get("args") or []
        self.cores = meta.get("cores")
        self.compiles = compiles
        first = min(c.start for c in compiles)
        # The driver's start covers Lake loading the workspace too.
        start = meta.get("start")
        self.start = min(start, first) if start is not None else first
        self.end = max(c.end for c in compiles)
        self.lake_end = (done or {}).get("end")
        self.lake_status = (done or {}).get("status")

    @property
    def wall(self):
        return self.end - self.start

    @property
    def cpu(self):
        return sum(c.cpu for c in self.compiles)

    def failed(self):
        return [c for c in self.compiles if c.status != 0]


def read_setup(c):
    """Fill in a compile's module, package and imports from its setup file."""
    if not c.setup:
        return
    try:
        with open(c.setup) as f:
            setup = json.load(f)
    except (OSError, ValueError):
        return
    c.module = setup.get("name", c.module)
    c.package = setup.get("package", "")
    # `importArts` is keyed by every module the compile loads (the transitive
    # imports): the last of them to finish is always a direct import.
    c.imports = list(setup.get("importArts", {}))


def list_builds(outdir):
    """[(build, path)], newest first."""
    try:
        names = os.listdir(outdir)
    except OSError:
        return []
    names = sorted((n for n in names if n.endswith(".jsonl")), reverse=True)
    return [(n[: -len(".jsonl")], os.path.join(outdir, n)) for n in names]


def load_build(path, setups=True):
    """The build recorded at `path`; None if it compiled nothing."""
    meta, done, compiles = {}, None, []
    with open(path) as f:
        for line in f:
            try:
                rec = json.loads(line)
            except ValueError:
                continue  # a line cut short by a killed build
            if "meta" in rec:
                meta = rec["meta"]
            elif "done" in rec:
                done = rec["done"]
            else:
                compiles.append(Compile(rec))
    if not compiles:
        return None
    if setups:
        for c in compiles:
            read_setup(c)
    return Build(meta, compiles, done)


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


def profile(compiles, t0, t1, columns, weight=lambda c: 1.0):
    """Average number of compiles running in each of `columns` equal slices.

    With `weight`, each compile counts `weight(c)` while it runs instead of 1:
    `cores_used` makes this the cores busy, spreading each compile's CPU time
    evenly over its run (Lean elaborates a module's declarations in parallel,
    so one compile can keep several cores busy)."""
    width = (t1 - t0) / columns if t1 > t0 else 0.0
    if width <= 0:
        return [0.0] * columns
    busy = [0.0] * columns
    for c in compiles:
        a, b = (c.start - t0) / width, (c.end - t0) / width
        for i in range(max(0, int(a)), min(columns, int(b) + 1)):
            busy[i] += weight(c) * max(0.0, min(b, i + 1) - max(a, i))
    return busy


def cores_used(c):
    return c.cpu / c.time if c.time > 0 else 0.0


def observed_critical_path(build):
    """[(compile, waited)] from the first step to the compile that ended last.

    Each step is the import of the next that finished last, among those
    compiled in this build; `waited` is the time between that import (or the
    build's start) finishing and the step starting.
    """
    by_module = {c.module: c for c in build.compiles}
    step = max(build.compiles, key=lambda c: c.end)
    path = []
    while step is not None:
        built = [
            by_module[m]
            for m in step.imports
            if m in by_module and by_module[m].end <= step.start
        ]
        blocker = max(built, key=lambda c: c.end, default=None)
        ready = blocker.end if blocker is not None else build.start
        path.append((step, max(0.0, step.start - ready)))
        step = blocker
    path.reverse()
    return path


def dependency_bound(build):
    """The longest chain of dependent compiles in this build, by compile time:
    how long the build would take with unlimited cores. [compile] in order."""
    by_module = {c.module: c for c in build.compiles}
    # module -> (length of the longest chain ending here, the module before it)
    best = {}
    # An import ends before its importer starts, so in order of end time
    # every compile's imports have been seen before it.
    for c in sorted(build.compiles, key=lambda c: c.end):
        prev = [(best[m][0], m) for m in c.imports if m in best]
        length, before = max(prev, default=(0.0, None))
        best[c.module] = (length + c.time, before)
    if not best:
        return []
    m = max(best, key=lambda k: best[k][0])
    chain = []
    while m is not None:
        chain.append(by_module[m])
        m = best[m][1]
    chain.reverse()
    return chain


def group(c, depth=GROUP_DEPTH):
    """Where a compile's CPU is counted: its package and module prefix."""
    prefix = ".".join(c.module.split(".")[:depth])
    return f"{c.package}: {prefix}" if c.package else prefix


def cpu_by_group(compiles):
    """[(group, cpu, modules)], most CPU first."""
    cpu, n = defaultdict(float), defaultdict(int)
    for c in compiles:
        g = group(c)
        cpu[g] += c.cpu
        n[g] += 1
    return sorted(((g, cpu[g], n[g]) for g in cpu), key=lambda r: r[1], reverse=True)


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


def chart(values, ymax, height, start_label, mid_label, end_label, line=None):
    """A column chart of `values` (0..ymax), `height` rows tall, as lines.

    `line`, if given, is a level marked with ┄ where no column reaches it
    (the core count)."""
    ymax = max(ymax, 1e-9)
    label_w = len(f"{ymax:.0f}")
    line_row = round(line / ymax * height) if line else None
    lines = []
    for row in range(height, 0, -1):
        cells = []
        for v in values:
            eighths = round(v / ymax * height * 8) - (row - 1) * 8
            cell = BLOCKS[max(0, min(8, eighths))]
            if cell == " " and row == line_row:
                cell = "┄"
            cells.append(cell)
        label = f"{ymax:.0f}" if row == height else ""
        if row == line_row and row != height:
            label = f"{line:.0f}"
        elif row == (height + 1) // 2 and height > 2 and line_row is None:
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

    def __init__(self, build, top=15, columns=60, height=8):
        self.b = build
        self.top = top
        self.columns = columns
        self.height = height
        cs = build.compiles
        self.peak = peak_concurrency(cs)
        self.avg = sum(c.time for c in cs) / build.wall if build.wall > 0 else 0.0
        self.serial = time_at_most(cs, build.start, build.end, 1)
        self.saturated = (
            build.wall - time_at_most(cs, build.start, build.end, build.cores - 1)
            if build.cores
            else None
        )
        self.biggest = max(cs, key=lambda c: c.maxrss_kb)
        self.has_deps = any(c.imports for c in cs)
        self.path = observed_critical_path(build) if self.has_deps else []
        self.bound = dependency_bound(build) if self.has_deps else []
        self.profile = profile(cs, build.start, build.end, columns)
        self.cpu_profile = profile(cs, build.start, build.end, columns, cores_used)
        self.cpu_avg = build.cpu / build.wall if build.wall > 0 else 0.0

    def title(self):
        b = self.b
        cmd = " ".join(["lake build"] + b.args)
        return f"Build report: {cmd}, build {b.build}"

    def summary_rows(self):
        b, rows = self.b, []
        rows.append(
            ("wall time", dur(b.wall), "from lake starting to the last compile")
        )
        n, failed = len(b.compiles), len(b.failed())
        status = f"{failed} failed" if failed else "none failed"
        if b.lake_status not in (None, 0):
            status += f"; lake exited {b.lake_status}"
        rows.append(("compiled", f"{n} module{'s' if n != 1 else ''}", status))
        rows.append(("CPU time", dur(b.cpu), "user + system, all compiles"))
        spent = sum(c.time for c in b.compiles)
        if spent > 0 and b.cpu > 0:
            share = b.cpu / spent
            note = "CPU ÷ wall time, per compile"
            if share < 0.9:
                note += "; well below 100%: compiles waited for a core"
            elif share > 1.1:
                note += "; above 100%: compiles ran threads in parallel"
            rows.append(("core share", f"{share:.0%}", note))
        cores = f" on {b.cores} cores" if b.cores else ""
        rows.append(
            ("parallelism", f"{self.avg:.1f} average", f"{self.peak} peak{cores}")
        )
        rows.append(
            (
                "cores busy",
                f"{self.cpu_avg:.1f} average",
                (
                    f"CPU time ÷ wall time; {max(self.cpu_profile, default=0):.1f} "
                    "in the busiest column"
                ),
            )
        )
        if self.saturated is not None and b.wall > 0:
            rows.append(
                (
                    "all slots busy",
                    dur(self.saturated),
                    (
                        f"{self.saturated / b.wall:.0%} of the wall time ran a "
                        "compile on every core"
                    ),
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
        rows.append(("peak memory", mem(self.biggest.maxrss_kb), self.biggest.module))
        return rows

    def charts(self):
        """[(caption, lines)]: compiles running, then cores busy, over time."""
        b = self.b
        per = dur(b.wall / self.columns if self.columns else 0)
        out = []
        for what, values in (
            ("compiles running", self.profile),
            ("cores busy (each compile's CPU spread over its run)", self.cpu_profile),
        ):
            ymax = max(b.cores or 0, max(values, default=0), 1)
            line = b.cores if b.cores and b.cores < ymax else None
            caption = f"{what}, averaged over each {per} column"
            if line:
                caption += f"; ┄ marks the {b.cores} cores"
            lines = chart(
                values,
                ymax,
                self.height,
                "0:00",
                clock(b.wall / 2),
                clock(b.wall),
                line=line,
            )
            out.append((caption, lines))
        return out

    def path_rows(self):
        """[(start, time, waited, module)] with short steps folded together."""
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
                    (clock(c.start - self.b.start), dur(c.time), dur(waited), c.module)
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
            f"idle (Lake starting up, all cores taken, or Lake's work between "
            f"compiles), of the {dur(b.wall)} wall time"
        )
        if self.bound:
            bound = sum(c.time for c in self.bound)
            text += (
                f". With unlimited cores this build would take at least "
                f"{dur(bound)} (its longest import chain)"
            )
        return text

    def slow_rows(self):
        cs = sorted(self.b.compiles, key=lambda c: c.time, reverse=True)[: self.top]
        return [(dur(c.time), dur(c.cpu), mem(c.maxrss_kb), c.module) for c in cs]

    def group_rows(self, limit=10):
        total = self.b.cpu or 1.0
        return [
            (dur(cpu), f"{cpu / total:.0%}", str(n), g)
            for g, cpu, n in cpu_by_group(self.b.compiles)[:limit]
        ]

    def failed_rows(self, limit=20):
        return [(str(c.status), c.module) for c in self.b.failed()[:limit]]

    # -- renderers --

    def text(self):
        out = [self.title(), ""]
        w = max(len(r[0]) for r in self.summary_rows())
        for k, v, note in self.summary_rows():
            out.append(f"  {k:<{w}}  {v:>12}   {note}".rstrip())
        for caption, lines in self.charts():
            out += ["", f"Parallelism over time: {caption}"]
            out += ["  " + line for line in lines]
        if self.path:
            out += [
                "",
                "Critical path: the chain of imports the last compile waited on",
            ]
            out += textwrap.wrap(
                self.path_caption() + ".",
                width=86,
                initial_indent="  ",
                subsequent_indent="  ",
            )
            out.append(f"  {'start':>8} {'compile':>8} {'idle':>8}  module")
            for start, t, waited, m in self.path_rows():
                out.append(f"  {start:>8} {t:>8} {waited:>8}  {m}")
        out += ["", "Slowest modules"]
        out.append(f"  {'time':>8} {'CPU':>8} {'memory':>9}  module")
        for t, cpu, m, mod in self.slow_rows():
            out.append(f"  {t:>8} {cpu:>8} {m:>9}  {mod}")
        out += ["", "Where the CPU went"]
        out.append(f"  {'CPU':>8} {'share':>6} {'mods':>6}  package: prefix")
        for cpu, share, n, g in self.group_rows():
            out.append(f"  {cpu:>8} {share:>6} {n:>6}  {g}")
        if self.b.failed():
            out += ["", f"Failed compiles ({len(self.b.failed())})"]
            for status, m in self.failed_rows():
                out.append(f"  exit {status:>3}  {m}")
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
        for caption, lines in self.charts():
            out += ["", f"**Parallelism over time**: {caption}", "", "```text"]
            out += lines
            out += ["```"]
        if self.path:
            out += [
                "",
                "**Critical path**: the chain of imports the last compile waited on. "
                + self.path_caption()
                + ".",
                "",
            ]
            out += table(
                ("start", "compile", "idle", "module"),
                [(s, t, w, f"`{m}`" if s else m) for s, t, w, m in self.path_rows()],
                ("--:", "--:", "--:", "---"),
            )
        out += [
            "",
            "<details><summary>Slowest modules, and where the CPU went</summary>",
            "",
        ]
        out += table(
            ("time", "CPU", "memory", "module"),
            [(t, c, m, f"`{mod}`") for t, c, m, mod in self.slow_rows()],
            ("--:", "--:", "--:", "---"),
        )
        out += [""]
        out += table(
            ("CPU", "share", "modules", "package: prefix"),
            [(c, s, n, f"`{g}`") for c, s, n, g in self.group_rows()],
            ("--:", "--:", "--:", "---"),
        )
        out += ["", "</details>"]
        if self.b.failed():
            out += ["", f"**Failed compiles** ({len(self.b.failed())})", ""]
            out += [f"- `{m}` (exit {s})" for s, m in self.failed_rows()]
        return "\n".join(out) + "\n"


# --- selftest --------------------------------------------------------------


def selftest():
    """Check the analysis against small worked examples."""
    import tempfile

    failures, checks = [], []

    def check(name, cond):
        print(("ok   " if cond else "FAIL ") + name)
        checks.append(name)
        if not cond:
            failures.append(name)

    #   A: 0-10    B (imports A): 10-30    C (imports A): 10-15
    #   D (imports B, C, A): 31-40, one second after B -- Lake's own work
    #   E (imports nothing): 0-2, failed
    with tempfile.TemporaryDirectory() as tmp:
        log = os.path.join(tmp, "b1.jsonl")
        imports = {
            "X.A": [],
            "X.B": ["X.A"],
            "X.C": ["X.A"],
            "X.D": ["X.A", "X.B", "X.C", "Other.NotBuilt"],
            "X.E": [],
        }
        with open(log, "w") as f:
            meta = {"build": "b1", "start": 999.0, "args": ["X"], "cores": 2}
            f.write(json.dumps({"meta": meta}) + "\n")
            for mod, s, e, rss, status in [
                ("X.A", 0, 10, 1000, 0),
                ("X.B", 10, 30, 3_000_000, 0),
                ("X.C", 10, 15, 500, 0),
                ("X.D", 31, 40, 800, 0),
                ("X.E", 0, 2, 100, 1),
            ]:
                setup = os.path.join(tmp, mod + ".setup.json")
                with open(setup, "w") as g:
                    arts = {m: [] for m in imports[mod]}
                    json.dump({"name": mod, "package": "x", "importArts": arts}, g)
                rec = {
                    "file": f"X/{mod[2:]}.lean",
                    "setup": setup,
                    "start": 1000.0 + s,
                    "end": 1000.0 + e,
                    "user": (e - s) * 0.9,
                    "sys": 0.0,
                    "maxrss_kb": rss,
                    "status": status,
                }
                f.write(json.dumps(rec) + "\n")
            f.write('{"file": "X/Cut.le')  # a killed build's last line
        with open(os.path.join(tmp, "a0.jsonl"), "w") as f:
            f.write(json.dumps({"meta": {"build": "a0", "start": 0}}) + "\n")

        check(
            "builds are listed newest first",
            [b for b, _p in list_builds(tmp)] == ["b1", "a0"],
        )
        check(
            "nothing compiled is not an error",
            load_build(os.path.join(tmp, "a0.jsonl")) is None,
        )
        b = load_build(log)
        check("a cut-off line is skipped", len(b.compiles) == 5)
        check(
            "setup files give module names",
            sorted(c.module for c in b.compiles) == ["X.A", "X.B", "X.C", "X.D", "X.E"],
        )
        check("wall time runs from lake's start", abs(b.wall - 41.0) < 1e-9)
        check("peak concurrency", peak_concurrency(b.compiles) == 2)
        check(
            "one or none",
            abs(time_at_most(b.compiles, b.start, b.end, 1) - 34.0) < 1e-9,
        )
        prof = profile(b.compiles, b.start, b.end, 41)
        check("profile integrates to total compile time", abs(sum(prof) - 46.0) < 1e-9)
        cpu_prof = profile(b.compiles, b.start, b.end, 41, cores_used)
        check(
            "cores-busy profile integrates to total CPU time",
            abs(sum(cpu_prof) - 0.9 * 46.0) < 1e-9,
        )
        path = observed_critical_path(b)
        check(
            "critical path A -> B -> D",
            [c.module for c, _w in path] == ["X.A", "X.B", "X.D"],
        )
        check("critical path waits", [round(w, 6) for _c, w in path] == [1.0, 0.0, 1.0])
        check(
            "dependency bound A -> B -> D",
            [c.module for c in dependency_bound(b)] == ["X.A", "X.B", "X.D"],
        )
        check("failed compiles", [c.module for c in b.failed()] == ["X.E"])
        r = Report(b, columns=20, height=4)
        text, md = r.text(), r.markdown()
        check(
            "text has every section",
            all(
                s in text
                for s in (
                    "wall time",
                    "Parallelism over time",
                    "Critical path",
                    "Slowest modules",
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
            all(
                len(line) <= 4 + 20
                for _caption, lines in r.charts()
                for line in lines[:-1]
            ),
        )
        check(
            "durations", [dur(4.25), dur(784), dur(8760)] == ["4.2s", "13m04s", "2h26m"]
        )

    print(f"{len(checks) - len(failures)}/{len(checks)} passed")
    return 1 if failures else 0


# --- main ------------------------------------------------------------------


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv[:1] == ["build"]:
        sys.exit("build-report: it only reads recorded builds; "
                 "`etc/timed-build.py [LAKE_ARGS...]` builds and records one")
    p = argparse.ArgumentParser(
        description="Report on the timing of a build recorded by etc/timed-build.py.",
    )
    p.add_argument(
        "--dir",
        default=DEFAULT_DIR,
        help=f"where builds are recorded (default {DEFAULT_DIR})",
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
        "--top", type=int, default=15, help="slowest modules to list (default 15)"
    )
    p.add_argument("--width", type=int, default=60, help="chart columns (default 60)")
    p.add_argument("--selftest", action="store_true", help="run the tests and exit")
    args = p.parse_args(argv)

    if args.selftest:
        return selftest()
    builds = list_builds(args.dir)
    if args.list:
        for build, path in builds:
            b = load_build(path, setups=False)
            if b is None:
                print(f"{build}  compiled nothing")
            else:
                cmd = " ".join(["lake build"] + b.args)
                print(f"{build}  {cmd}  {len(b.compiles)} modules  {dur(b.wall)}")
        return 0
    paths = dict(builds)
    if args.build is None and builds:
        args.build = builds[0][0]
    if args.build not in paths:
        print(f"build-report: no build recorded in {args.dir}", file=sys.stderr)
        return 1
    build = load_build(paths[args.build])
    if build is None:
        print(f"build-report: build {args.build} compiled nothing; nothing to report")
        return 0
    report = Report(build, top=args.top, columns=args.width)
    sys.stdout.write(report.markdown() if args.format == "markdown" else report.text())
    if args.markdown_to:
        with open(args.markdown_to, "a") as f:
            f.write(report.markdown())
    return 0


if __name__ == "__main__":
    sys.exit(main())
