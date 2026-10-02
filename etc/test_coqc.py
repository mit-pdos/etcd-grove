# Tests for etc/rocqc.py.
#
# Run them with `./etc/rocqc.py --selftest`, which needs nothing but the
# standard library. They are also plain pytest tests, so `pytest
# etc/test_coqc.py` works where pytest is installed; pytest is not a
# dependency of this repo and no CI job runs it.
#
# `Classify`'s regexes are bytes patterns, because rocqc.py reads `rocq
# compile`'s output as bytes and slices the .v file as bytes -- so every
# fixture here is bytes too. Rocq's `Chars i - j` offsets are byte offsets,
# which is what makes that slicing correct for a file with non-ASCII in it
# (etc/test_coqc/test.v has a σ in it for exactly this reason).

import os.path
import sqlite3
import tempfile
from datetime import datetime, timedelta, timezone
from os.path import join

from rocqc import BuildInfo, Classify, CoqcFilter, TimingDb, make_jobs


class MemDb:
    def __init__(self):
        self.qeds = {}
        self.files = {}
        self.closed = False

    def add_qed(self, fname, ident, time):
        key = (fname, ident)
        assert self.qeds.get(key) is None
        self.qeds[key] = time

    def add_file(self, fname, mode, time):
        assert self.files.get(fname) is None
        self.files[fname] = (mode, time)

    def close(self):
        assert not self.closed


def test_classify_qed():
    assert Classify.is_qed(b"Qed.")
    assert Classify.is_qed(b"Time Qed.")
    assert Classify.is_qed(b"Time  Qed.")

    assert not Classify.is_qed(b"Qed")
    assert not Classify.is_qed(b"NotQed.")


def test_classify_def():
    assert (
        Classify.get_def(
            b"""Definition \xcf\x83 :
    forall (x:nat), x + 1000 = x + 1000 :=
    fun x => eq_refl (x + (500+500))."""
        )
        == "σ"
    )
    assert (
        Classify.get_def(
            rb"""#[global]
Instance GroveOp_fin : Countable GroveOp."""
        )
        == "GroveOp_fin"
    )

    assert Classify.get_def(rb"""Require Import Utf8.""") is None


def test_classify_def_keeps_goose_suffixes():
    """`new/code/` is full of `Definition fooⁱᵐᵖˡ`; the suffix is part of the name."""
    assert Classify.get_def("Definition minⁱᵐᵖˡ : val :=".encode()) == "minⁱᵐᵖˡ"
    assert Classify.get_def("Lemma wp_minⁱᵐᵖˡ :".encode()) == "wp_minⁱᵐᵖˡ"
    # The name and its suffixed sibling must not collapse onto one another.
    assert Classify.get_def(b"Definition min : val :=") == "min"


def test_classify_time():
    assert Classify.get_time(
        b"""Chars 110 - 119 [Print~\xcf\x83.] 0.009 secs (0.006u,0.003s)"""
    ) == (110, 119, 0.009)

    assert Classify.get_time(
        rb"""Chars 120 - 139 [Theorem~thm~:~True.] 0. secs (0.u,0.s)"""
    ) == (120, 139, 0.0)

    assert Classify.get_time(rb"""Debug: (* debug auto: *)""") is None

    assert (
        Classify.get_time(
            b"""\xcf\x83 = \xce\xbb x : nat, eq_refl
     : \xe2\x88\x80 x : nat, x + 1000 = x + 1000"""
        )
        is None
    )


FIXTURE_DIR = join(os.path.dirname(os.path.realpath(__file__)), "test_coqc")


def run_filter(fname):
    db = MemDb()
    vfile = join(FIXTURE_DIR, fname)
    filter = CoqcFilter(vfile, "vo", db, None, datetime.now(timezone.utc))
    with open(join(FIXTURE_DIR, fname + ".out"), "rb") as f:
        for line in f:
            filter.line(line)
    filter.done()
    return db


def test_filter_unit_tests():
    db = MemDb()
    start = datetime.now(timezone.utc)
    vfile = join(FIXTURE_DIR, "test.v")
    filter = CoqcFilter(vfile, "vo", db, None, start)
    with open(join(FIXTURE_DIR, "test.v.out"), "rb") as f:
        for line in f:
            filter.line(line)
    assert (
        filter.chars(21, 111)
        == b"""Definition \xcf\x83 : forall (x:nat), x + 1000 = x + 1000 :=
  fun x => eq_refl (x + (500+500))."""
    )
    end_t = start + timedelta(seconds=0.5)
    filter.done(end_t=end_t)
    assert db.qeds == {
        (vfile, "thm"): 0.0,
        (vfile, "helpful"): 0.037,
        (vfile, "thm'"): 0.0,
    }
    assert db.files[vfile] == ("vo", 0.5)


def test_filter_integration_tests():
    for fname, qeds in {"Abstract.v": {"abstract_away_helper": 0.0}}.items():
        db = run_filter(fname)
        vfile = join(FIXTURE_DIR, fname)
        expected_qeds = {(vfile, ident): t for ident, t in qeds.items()}
        assert db.qeds == expected_qeds


def test_infinite_v_handled(capsys):
    run_filter("infinite.v")
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == ""


# --- build mode ------------------------------------------------------------
#
# The mode is read off rocq compile's own arguments, since that is the only
# place that says which of the three builds this is.


def test_mode_from_coqargs():
    def mode_of(args):
        return CoqcFilter.from_coqargs(args, MemDb()).mode

    assert mode_of(["-Q", "new", "New", "-o", "a.vo", "a.v"]) == "vo"
    assert mode_of(["-Q", "new", "New", "-vos", "a.v", "-o", "a.vos"]) == "vos"
    assert mode_of(["-Q", "new", "New", "-time", "-vok", "a.v", "-o", "a.vok"]) == "vok"


def test_vfile_from_coqargs():
    filter = CoqcFilter.from_coqargs(["-Q", "new", "New", "-vok", "new/a.v"], MemDb())
    assert filter.vfile == "new/a.v"


# --- reporting -------------------------------------------------------------


def report_line(delta, mode="vo", threshold=0.0):
    import io
    import sys

    filter = CoqcFilter("new/a.v", mode, MemDb(), None, datetime.now(timezone.utc))
    filter.print_time = threshold
    saved = sys.stdout
    sys.stdout = io.StringIO()
    try:
        filter.report(delta)
        return sys.stdout.getvalue()
    finally:
        sys.stdout = saved


def test_report_prints_one_sortable_line():
    line = report_line(12.345)
    assert line == "ROCQ TIME    12.35s vo  new/a.v\n"
    # The seconds field is what `sort -rn -k3` keys on.
    assert line.split()[2] == "12.35s"
    assert report_line(3.0, mode="vok").split()[3] == "vok"


def test_report_respects_threshold_and_off_switch():
    assert report_line(1.0, threshold=5.0) == ""
    assert report_line(9.0, threshold=5.0) != ""

    import io
    import sys

    filter = CoqcFilter("new/a.v", "vo", MemDb(), None, datetime.now(timezone.utc))
    assert filter.print_time is None
    saved, sys.stdout = sys.stdout, io.StringIO()
    try:
        filter.report(1000.0)
        assert sys.stdout.getvalue() == ""
    finally:
        sys.stdout = saved


def test_done_does_not_record_a_failed_compile():
    db = MemDb()
    filter = CoqcFilter("new/a.v", "vo", db, None, datetime.now(timezone.utc))
    filter.done(record=False)
    assert db.files == {}


# --- the timing database ---------------------------------------------------


def test_vo_and_vok_timings_coexist():
    """The bug this schema exists to fix: one file, three modes, three rows."""
    with tempfile.TemporaryDirectory() as d:
        dbfile = join(d, "t.sqlite3")
        db = TimingDb.from_file(dbfile)
        db.add_file("new/a.v", "vo", 100.0)
        db.add_file("new/a.v", "vok", 40.0)
        db.add_file("new/a.v", "vos", 2.0)
        db.add_file("new/a.v", "vo", 110.0)  # a rebuild replaces its own row
        db.close()

        conn = sqlite3.connect(dbfile)
        rows = {
            mode: time
            for mode, time in conn.execute(
                "SELECT mode, time FROM file_timings WHERE fname = 'new/a.v'"
            )
        }
        conn.close()
        assert rows == {"vo": 110.0, "vok": 40.0, "vos": 2.0}


LEGACY_SCHEMA = (
    "CREATE TABLE file_timings "
    "(fname text NOT NULL PRIMARY KEY, is_vos integer NOT NULL, time real)"
)


def test_legacy_database_is_migrated_in_place():
    with tempfile.TemporaryDirectory() as d:
        dbfile = join(d, "t.sqlite3")
        conn = sqlite3.connect(dbfile, isolation_level=None)
        conn.execute(LEGACY_SCHEMA)
        conn.execute("INSERT INTO file_timings VALUES ('new/a.v', 0, 100.0)")
        conn.execute("INSERT INTO file_timings VALUES ('new/b.v', 1, 3.0)")
        conn.close()

        TimingDb.from_file(dbfile).close()
        # Opening it a second time must be a no-op, not a second migration.
        TimingDb.from_file(dbfile).close()

        conn = sqlite3.connect(dbfile)
        rows = sorted(conn.execute("SELECT fname, mode, time FROM file_timings"))
        tables = [
            r[0]
            for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")
        ]
        conn.close()
        assert rows == [("new/a.v", "vo", 100.0), ("new/b.v", "vos", 3.0)]
        assert "file_timings_legacy" not in tables


def test_fresh_database_gets_the_mode_schema():
    with tempfile.TemporaryDirectory() as d:
        dbfile = join(d, "t.sqlite3")
        TimingDb.from_file(dbfile).close()
        conn = sqlite3.connect(dbfile)
        cols = [r[1] for r in conn.execute("PRAGMA table_info(file_timings)")]
        conn.close()
        assert "mode" in cols
        assert "is_vos" not in cols


# --- per-build rows --------------------------------------------------------
#
# What etc/build-report.py reads: one `builds` row per make run, one
# `build_files` row per compile, failed compiles included.


def test_make_jobs_from_makeflags():
    assert make_jobs(None) is None
    assert make_jobs("s") == 1
    assert make_jobs("ks -j4 --jobserver-auth=fifo:/tmp/GMfifo1") == 4
    assert make_jobs("s -j") == 0
    assert make_jobs("-j24") == 24


def test_build_info_needs_an_id():
    assert BuildInfo.from_env({}) is None
    info = BuildInfo.from_env(
        {
            "ROCQ_BUILD_ID": "b1",
            "ROCQ_BUILD_START": "100.5",
            "ROCQ_BUILD_GOALS": "ci",
            "MAKEFLAGS": "s -j8",
        }
    )
    assert (info.build, info.start, info.goals, info.jobs) == ("b1", 100.5, "ci", 8)


def test_build_rows_are_recorded_for_success_and_failure():
    with tempfile.TemporaryDirectory() as d:
        dbfile = join(d, "t.sqlite3")
        info = BuildInfo("b1", 100.0, "ci", 4)
        start = datetime.fromtimestamp(110.0, timezone.utc)
        for vfile, status, record in (("new/a.v", 0, True), ("new/b.v", 1, False)):
            filter = CoqcFilter(
                vfile, "vo", TimingDb.from_file(dbfile), b"", start, build=info
            )
            filter.done(
                end_t=start + timedelta(seconds=5),
                record=record,
                status=status,
                usage=(4.0, 0.5, 2048),
            )
        conn = sqlite3.connect(dbfile)
        builds = conn.execute("SELECT * FROM builds").fetchall()
        rows = conn.execute(
            "SELECT fname, start, end, user, maxrss_kb, status FROM build_files "
            "ORDER BY fname"
        ).fetchall()
        timed = conn.execute("SELECT fname FROM file_timings").fetchall()
        conn.close()
        assert builds == [("b1", 100.0, "ci", 4)]
        assert rows == [
            ("new/a.v", 110.0, 115.0, 4.0, 2048, 0),
            ("new/b.v", 110.0, 115.0, 4.0, 2048, 1),
        ]
        # the failed compile is in its build, but not in file_timings
        assert timed == [("new/a.v",)]
