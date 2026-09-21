#!/usr/bin/env python3

# Read back the build timings that etc/rocqc.py records.
#
# Answers "where did the build time go", per file and per Qed, for one build
# mode at a time -- a file's vo, vos and vok builds cost very different
# amounts and are stored as separate rows.
#
#   ./etc/timing-report.py                    # the vo build
#   ./etc/timing-report.py --mode vok         # the vok build
#   ./etc/timing-report.py --filter raft --max-qeds 20
#
# Standard library only, on purpose: this used to need pandas, which meant it
# could not be run on a machine that could nonetheless build the proof.

import sqlite3
import sys

MODES = ("vo", "vos", "vok")

# Prefixes broken out in the summary, longest match first.
GROUPS = ("external/", "new/", "src/")


def file_timings(conn, mode):
    """[(fname, time)] for one build mode, across both schemas.

    Databases written before 2026-09-21 have (fname PRIMARY KEY, is_vos,
    time) and cannot distinguish vo from vok -- everything that was not a vos
    build is reported as vo. etc/rocqc.py migrates such a database the next
    time it writes to it.
    """
    cols = [row[1] for row in conn.execute("PRAGMA table_info(file_timings)")]
    if not cols:
        return []
    if "mode" in cols:
        rows = conn.execute(
            "SELECT fname, time FROM file_timings WHERE mode = ?", (mode,)
        )
        return [(r[0], r[1] or 0.0) for r in rows]
    if mode == "vok":
        return []
    rows = conn.execute(
        "SELECT fname, time FROM file_timings WHERE is_vos = ?",
        (1 if mode == "vos" else 0,),
    )
    return [(r[0], r[1] or 0.0) for r in rows]


def mode_counts(conn):
    """{mode: number of files recorded}, for telling the user what is in the db."""
    return {m: len(file_timings(conn, m)) for m in MODES}


def qed_timings(conn):
    return [
        (r[0], r[1], r[2])
        for r in conn.execute("SELECT fname, ident, time FROM qed_timings")
    ]


def qed_totals(qeds):
    """{fname: summed Qed time}."""
    out = {}
    for fname, _ident, time in qeds:
        out[fname] = out.get(fname, 0.0) + (time or 0.0)
    return out


def group_total(files, prefix):
    return sum(t for fname, t in files if fname.startswith(prefix))


def fmt_row(fname, time, qed_time, width):
    return f"{time:>{width}.1f} {qed_time:>{width}.1f}  {fname}"


def report(conn, mode, pattern, max_files, max_qeds, sort_qed, out=sys.stdout):
    files = file_timings(conn, mode)
    qeds = qed_timings(conn)
    if pattern is not None:
        files = [(f, t) for f, t in files if pattern in f]
        qeds = [(f, i, t) for f, i, t in qeds if pattern in f]
    per_file_qed = qed_totals(qeds)

    width = 8
    total_s = sum(t for _f, t in files)
    print(f"mode         {mode}", file=out)
    print(f"files        {len(files)}", file=out)
    print(f"{'total':12s} {total_s:>{width}.1f}", file=out)
    for prefix in GROUPS:
        grouped = group_total(files, prefix)
        if grouped > 0:
            print(f"{'  ' + prefix.rstrip('/'):12s} {grouped:>{width}.1f}", file=out)

    qed_s = sum(per_file_qed.get(f, 0.0) for f, _t in files)
    pct = f" ({qed_s / total_s * 100:0.0f}%)" if total_s > 0 else ""
    print(f"{'Qed total':12s} {qed_s:>{width}.1f}{pct}", file=out)

    if total_s == 0:
        counts = mode_counts(conn)
        have = ", ".join(f"{m}={n}" for m, n in counts.items() if n)
        print(file=out)
        print(
            f"no {mode} timings recorded" + (f" (database has {have})" if have else ""),
            file=out,
        )
        return

    if max_files > 0:
        rows = sorted(
            ((f, t, per_file_qed.get(f, 0.0)) for f, t in files),
            key=lambda r: r[2] if sort_qed else r[1],
            reverse=True,
        )[:max_files]
        print(file=out)
        print("slow files:", file=out)
        print(f"{'time':>{width}} {'qed':>{width}}  fname", file=out)
        for fname, time, qed_time in rows:
            print(fmt_row(fname, time, qed_time, width), file=out)

    if max_qeds > 0 and qeds:
        print(file=out)
        print("slow QEDs:", file=out)
        print(f"{'time':>{width}}  ident", file=out)
        for fname, ident, time in sorted(qeds, key=lambda r: r[2], reverse=True)[
            :max_qeds
        ]:
            print(f"{time:>{width}.1f}  {ident}  ({fname})", file=out)


def selftest():
    """Check the aggregation against a database built by hand."""
    import io
    import tempfile
    from os.path import join

    failures = []

    def check(name, cond):
        print(("ok   " if cond else "FAIL ") + name)
        if not cond:
            failures.append(name)

    with tempfile.TemporaryDirectory() as d:
        dbfile = join(d, "t.sqlite3")
        conn = sqlite3.connect(dbfile, isolation_level=None)
        conn.execute(
            "CREATE TABLE file_timings (fname text NOT NULL, mode text NOT NULL, "
            "time real, PRIMARY KEY (fname, mode))"
        )
        conn.execute(
            "CREATE TABLE qed_timings (fname text NOT NULL, ident text NOT NULL, "
            "time real NOT NULL, PRIMARY KEY (fname, ident))"
        )
        for row in [
            ("new/a.v", "vo", 100.0),
            ("new/a.v", "vok", 40.0),
            ("new/b.v", "vo", 10.0),
            ("external/c.v", "vo", 5.0),
            ("new/a.v", "vos", 1.0),
        ]:
            conn.execute("INSERT INTO file_timings VALUES (?,?,?)", row)
        for row in [
            ("new/a.v", "lem1", 60.0),
            ("new/a.v", "lem2", 20.0),
            ("new/b.v", "lem3", 1.0),
        ]:
            conn.execute("INSERT INTO qed_timings VALUES (?,?,?)", row)

        check("vo and vok are separate", len(file_timings(conn, "vo")) == 3)
        check("vok row is found", file_timings(conn, "vok") == [("new/a.v", 40.0)])
        check(
            "qed times sum per file", qed_totals(qed_timings(conn))["new/a.v"] == 80.0
        )

        out = io.StringIO()
        report(conn, "vo", None, 10, 10, False, out=out)
        text = out.getvalue()
        check("vo total is 115", "115.0" in text)
        check("external is broken out", "external" in text)
        check("slowest file is first", text.index("new/a.v") < text.index("new/b.v"))

        out = io.StringIO()
        report(conn, "vok", None, 10, 0, False, out=out)
        check("vok total is 40", "40.0" in out.getvalue())

        out = io.StringIO()
        report(conn, "vo", "new/", 10, 0, False, out=out)
        check("filter drops external", "external/c.v" not in out.getvalue())

        out = io.StringIO()
        report(conn, "vo", "nothing-matches", 10, 0, False, out=out)
        check("empty selection says so", "no vo timings recorded" in out.getvalue())
        conn.close()

    # A legacy database is readable without being migrated first.
    with tempfile.TemporaryDirectory() as d:
        dbfile = join(d, "legacy.sqlite3")
        conn = sqlite3.connect(dbfile, isolation_level=None)
        conn.execute(
            "CREATE TABLE file_timings (fname text NOT NULL PRIMARY KEY, "
            "is_vos integer NOT NULL, time real)"
        )
        conn.execute(
            "CREATE TABLE qed_timings (fname text NOT NULL, ident text NOT NULL, "
            "time real NOT NULL, PRIMARY KEY (fname, ident))"
        )
        conn.execute("INSERT INTO file_timings VALUES ('new/a.v', 0, 7.0)")
        conn.execute("INSERT INTO file_timings VALUES ('new/b.v', 1, 2.0)")
        check("legacy vo row", file_timings(conn, "vo") == [("new/a.v", 7.0)])
        check("legacy vos row", file_timings(conn, "vos") == [("new/b.v", 2.0)])
        check("legacy has no vok", file_timings(conn, "vok") == [])
        conn.close()

    print("FAILED: " + ", ".join(failures) if failures else "all checks passed")
    return 1 if failures else 0


if __name__ == "__main__":
    import argparse
    import os.path

    parser = argparse.ArgumentParser(
        description="report build times recorded by etc/rocqc.py"
    )

    parser.add_argument(
        "--max-files",
        type=int,
        default=10,
        help="number of slow files to show",
    )
    parser.add_argument(
        "--max-qeds",
        type=int,
        default=0,
        help="number of slow QED proofs to show",
    )
    parser.add_argument(
        "--sort-qed",
        help="sort by QED time rather than total time",
        action="store_true",
    )
    parser.add_argument(
        "--db", help="sqlite database of timing info", default=".timing.sqlite3"
    )
    parser.add_argument("--filter", help="only files whose path contains this")
    parser.add_argument(
        "--mode",
        choices=MODES,
        default=None,
        help="which build to report on (default vo)",
    )
    parser.add_argument(
        "--vos",
        help="shorthand for --mode vos",
        action="store_true",
    )
    parser.add_argument(
        "--vok",
        help="shorthand for --mode vok",
        action="store_true",
    )
    parser.add_argument(
        "--selftest",
        help="check the aggregation against a hand-built database and exit",
        action="store_true",
    )

    args = parser.parse_args()

    if args.selftest:
        sys.exit(selftest())

    mode = args.mode
    if mode is None:
        mode = "vos" if args.vos else "vok" if args.vok else "vo"

    if not os.path.exists(args.db):
        print(f"database file {args.db} not found", file=sys.stderr)
        sys.exit(1)
    conn = sqlite3.connect(args.db)
    report(
        conn,
        mode,
        args.filter,
        args.max_files,
        args.max_qeds,
        args.sort_qed,
    )
    conn.close()
