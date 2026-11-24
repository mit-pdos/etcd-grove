#!/usr/bin/env python3
"""Regenerate, or check, the Goose translations of raft and etcd (in `Code/`, `GeneratedProof/`).

usage: etc/goose.py [--check] [--project NAME]... [--src NAME=DIR]... [--perennial DIR]

  --check      translate into a scratch directory and compare with the checked-in
               files; exit 1 (printing a diff) if they differ.  A gate for CI: the
               checked-in translation must be exactly what the pinned translator
               produces from the pinned Go source.  Also exit 1 if the examples'
               go.mod files replace etcd or raft by another revision than the
               projects' pins (GO_MOD_PINS; without --check, only a warning).
  --project    only this project (raft, bbolt, etcd, kv, kvreconf, durable, prophkv, bboltfs, crashlog, walfs, durablekv, kvdurable, putget, putget-dist, putgetc, putget3, putgetN, leaseN, leaseexpiryN, txnlinfaultsN, restartN, authN, authlease, auth3, etcd-wal,
               linkvtxn, porcupine, bridge, lintest, raft-witness, kvwitness, raft-noax, kvdurable-noax, kvnet, raft-tla, tracecheck, antithesis, k8s-apiserver,
               k8s-daemonset, k8s-compactor, k8s-all, etcd-all, k8s-authz, k8s-authz-driver, bbolt-bank, bbolttest or remote; repeatable; default: all).
  --src        translate project NAME from the local checkout DIR instead of
               cloning its pinned revision (default: $<NAME>_SRC, e.g. $ETCD_SRC,
               $ETCD_RAFT_SRC).  For a pinned revision not yet pushed, or for trying
               a source change.  The output says so; with --check, DIR must be at
               the pinned revision with no uncommitted changes.
  --perennial  use the translator of this Perennial checkout instead of the pinned
               one (default: $PERENNIAL_DIR, else the revision pinned in
               lake-manifest.json); for trying a translator change locally.

Each project is a Go repository at a pinned revision, translated into `Code/` and
`GeneratedProof/`: the packages in its list, with goose's `-lean-root PKG=` mapping
every non-standard-library Go path the translation reaches to the empty root
(modules `Code.<pkg>`, `GeneratedProof.<pkg>`; standard-library packages stay
`Perennial.*`, Perennial's).  A project's `parts` translate more of its packages into a
module root of their own (`<root>/Code/`, configured by `<root>/Code/**.toml`), and a project
may itself translate into such a root (`root`): for a Go path two sources translate (now raft's
witness experiment, the parallel tree `RaftWitness/` of projects raft-witness and kvwitness; until
stage R6 of the raft v3.7 retarget, 2026-10-16, etcd's raft dependency in `EtcdDeps/` and the raft
proof's parallel tree `Raft37/`, both raft's path).
A project's prophecy patches (`etc/proph-patches/<project>/*.patch`: changes that only add
prophecy variables and their resolutions, checked by etc/proph_patch.py) are applied to a copy of
its source (`.lake/goose/<project>.proph`) before translation, in --check mode too.
Without --check, the generated `.lean` files under `{Code,GeneratedProof}/`
(in the subdirectories the project owns) are replaced by fresh output.  The Goose
configuration (`*.toml`, next to the code) is input and is never touched.

The translator (`goose`, `proofgen`) is built with `go` from Perennial's `goose/`.
The pinned Perennial is `.lake/packages/perennial` when Lake has already checked it
out at the pinned revision, otherwise a clone in `.lake/goose/perennial`.  A
project's source is cloned into `.lake/goose/<name>` at its pinned revision, except
for a project in this repository (`local`), whose source is that directory.

Every `go` command runs with `GOTOOLCHAIN` set to the pinned GO_TOOLCHAIN (Go fetches it if
absent): the translation of a standard-library package (names-only `net/http`, `encoding/json`,
...) is of the toolchain's own source, which changes between patch releases (go1.27.1's
`net/http` gives a different translation from go1.27.3's).
"""

import argparse
import difflib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
WORK = os.path.join(ROOT, ".lake", "goose")
# The Go toolchain the translations are generated with (the module docstring says why).
GO_TOOLCHAIN = "go1.27.3"

# Project raft's pin (projects raft and raft-tla translate two builds of it).
RAFT_REV = "d2c16c558247d0a07b96986fc348a003dad80f6e"

# The part RaftNoAx (raft without hand-written axioms, notes/raft-noax-part.md): project raft-noax's
# pin (the fork's branch raft37-goose-lean-noax-wire-core, notes/raft-noax.md), and project kvdurable-noax's
# source directory and Go package, examples/raft/kvdurablenoax (`etc/copy-part.py`, which reads these,
# renames the copied kvdurable proofs' package accordingly).
RAFT_NOAX_REV = "e98d795867e6d626df1cc4e71faa00c1c1f42764"
KVDURABLE_NOAX_DIR = os.path.join("examples", "raft", "kvdurablenoax")
KVDURABLE_NOAX_PKG = "github.com/mit-pdos/etcd-grove/examples/raft/kvdurablenoax"


@dataclass
class Part:
    """A translation of some of a project's packages into the module root `root`: for a Go
    path that is also translated from another source (none now; etcd's own raft dependency
    was one, `EtcdDeps/`), so that the two have different modules."""
    root: str
    lean_roots: list
    packages: list
    owned: list


@dataclass
class Project:
    name: str
    # The Go source, at a pinned revision (upstream, or a fork that makes the code
    # translatable).  Change the revision here and rerun etc/goose.py.
    repo: str
    rev: str
    # goose's -lean-root PKG=ROOT arguments: Go path prefixes -> Lean module root.
    lean_roots: list
    # Go packages to translate (resolved in the checkout's root module/workspace).
    packages: list
    # Output paths owned by this project, relative to Code/ and GeneratedProof/: a
    # directory, and the `.lean` file of the same name beside it (`go_etcd_io/bbolt`:
    # `bbolt.lean` and `bbolt/`).
    owned: list
    # More translations of packages of the same checkout, each into a module root of
    # its own (`<root>/Code/`, `<root>/GeneratedProof/`, configured by `<root>/Code/**.toml`).
    parts: list = field(default_factory=list)
    # The Go modules of the checkout whose code etc/verified-code.py counts (not its
    # tests or tools); None: every module of the checkout.
    counted_modules: list = None
    # The Go source is this directory of this repository (relative to its root) instead
    # of a fork (`repo`, `rev`: None).
    local: str = None
    # Additional Go build tags the packages are loaded with, beside `goose` (goose's and proofgen's
    # `-tags`, Perennial c6b39d4f8). Every package of one program must be translated with the same
    # tags: projects raft-tla and tracecheck (the `with_tla` build) are the only ones with any.
    tags: list = None
    # The module root of the translation: "" for `Code/`, `GeneratedProof/`; else
    # `<root>/Code/`, `<root>/GeneratedProof/` (configured by `<root>/Code/**.toml`), for
    # a project whose Go paths another project also translates (raft-witness and kvwitness,
    # the parallel tree `RaftWitness/`; raft v3.7 was one, the parallel tree `Raft37/` the
    # raft proof was ported into).
    root: str = ""
    # Standard-library packages the translation takes from their models in models/ (e.g.
    # ["net/rpc", "net/http"]; models/goroot.py's STD_MODELS) instead of the toolchain's source:
    # goose runs on a GOROOT of links whose packages' Go files are the models' (models/goroot.py
    # farm; goose's go/packages reads files from disk, so a `go build -overlay` file in GOFLAGS
    # would not reach it). None: the toolchain's own source, as every other project.
    std_models: list = None
    # Modules the translation takes from their models in models/ (module path -> the model's
    # directory, relative to the repository: {"google.golang.org/grpc": "models/grpc"}; a model of a
    # module keeps its module path and API, models/README.md): goose runs with the project's
    # workspace (its go.work, or its go.mod) plus `replace <path> => <model>`, written to a
    # temporary file (GOWORK, or -modfile in GOFLAGS), as models/grpc/gomodel.py does for go
    # builds. None: every module from the module cache.
    module_models: dict = None
    # Expand tabs in the translation's comments to four spaces (Go doc comments indented with tabs:
    # goose copies them into `/-- … -/`, where Lean rejects a tab at the start of a line; a goose gap,
    # notes/perennial-changes.md, 2026-11-23). A tab outside a comment is an error. False: as goose
    # writes it.
    expand_comment_tabs: bool = False
    # (mit-pdos/etcd-grove#24, J3) named Go types "import/path.Type" whose same-package JSON methods
    # (models/json/jsongen.py's same-package mode, jsongen_core.py "THE SAME-PACKAGE METHODS":
    # `json_model_gen.go`, build tag `goose || netmodel`, methods `JSONModel*`, which the
    # encoding/json model's Marshal/Unmarshal/Encode/Decode call by the value's method set) the
    # project's own translation (module root `root`, not its parts) sees. As #37's pbmodel_roots, by
    # the one mechanism of model files over real packages (`model_overlay`): generated afresh on every
    # run (so `--check` regenerates them) from the types' reflection dump into the scratch directory,
    # and handed to goose and proofgen in the project's one `-overlay` file (Perennial 078ceec6f), so
    # the fork stays upstream's; `models.lab` (the generated code's `jsoncodec`, models/) joins the
    # workspace. The Go side builds the same program with `-tags netmodel` and that overlay
    # (examples/models/jsonetcd/jsonmodel_forks.py tests the methods against encoding/json).
    jsonmodel_roots: list = None

    @property
    def env(self):
        return self.name.upper().replace("-", "_") + "_SRC"


PROJECTS = [
    Project(
        name="raft",
        # The raft etcd links (go.etcd.io/raft/v3 v3.7.0 in etcd's go.mod: etcd-io/raft
        # b867cf13, protobuf-go v2 raftpb: messages, entries, snapshots are pointers with
        # getters) plus two fixes rebased onto it: the single-voter read-index shortcut
        # (issues/raft-readindex-singleton-stale.md) and the probe-to-replicate shortcut taken
        # only when `pr.Next == pr.Match+1` (issues/raft-stale-term-appresp-index-zero-ack.md;
        # D21 M3): branch raft37-goose-lean-a1 of the etcd fork (raft37-goose-lean, 509271dac,
        # plus the second fix); and (2026-10-28) a third, the configuration switched to a
        # snapshot's when it is applied, not restored (issues/raft-snapshot-during-apply-stale-confchange.md):
        # branch raft37-goose-lean-a2, 565c2bd on a1; and (2026-11-10, premise fixes 2) a fourth,
        # `ConfState.Equivalent` comparing the configurations, not the messages (`proto.Equal`
        # compared unknown fields: nonissues/raft-confstate-unknown-fields-panic.md), d2c16c5 on
        # a2. (The raft proof was ported to it in a parallel tree, the module root Raft37,
        # stages R0-R5 of notes/raft-retarget-plan.md; stage R6 made it the raft tree, 2026-10-16.)
        # Modules Code.go_etcd_io.raft.v3*, GeneratedProof.go_etcd_io.raft.v3*.
        repo="https://github.com/upamanyus/etcd",
        rev=RAFT_REV,
        # raft's `proto` import is the names-only `Code.google_golang_org.protobuf.proto`
        # of the etcd project (as the protobuf runtime types raftpb's messages hold).
        # (`os`, `io/fs`: this repository's translations, project bboltfs's, not Perennial's; every
        # project is on them since 2026-11-03, so that bbolt's `os.FileMode` fields translate)
        lean_roots=["go.etcd.io/raft/v3=", "google.golang.org=", "os=", "io/fs="],
        packages=[
            ".",
            "go.etcd.io/raft/v3/confchange",
            "go.etcd.io/raft/v3/quorum",
            "go.etcd.io/raft/v3/raftpb",
            "go.etcd.io/raft/v3/tracker",
        ],
        owned=[os.path.join("go_etcd_io", "raft")],
        counted_modules=["go.etcd.io/raft/v3"],
    ),
    Project(
        name="bbolt",
        # bbolt as etcd links it (go.etcd.io/bbolt v1.5.0 in etcd's go.mod: etcd-io/bbolt
        # e7a8b2d), from the fork upamanyus/bbolt, branch `goose-lean` (3207bacf): its branch
        # `goose` (e353cbe, the forms Perennial's byte memory follows: `unsafe.Add`/`unsafe.Slice`
        # helpers, whole-struct copies through a local; Perennial's
        # docs/design/unsafe-memory.md, section 6), the fix of etcd-io/bbolt#1311
        # (issues/bbolt-commit-meta-error-frees-reader-pages.md), a crash-safe `init`
        # (nonissues/bbolt-init-not-crash-safe.md), a named type for `DB.ops` and no `retry:`
        # label; then branch `goose-lean-v2` (b30879b2): `getPageSize` returns a meta read error
        # instead of probing further (D18), `splitTwo`'s float threshold factored out as
        # `splitThreshold`, trusted (D17) (b30879b2); then `Tx.WriteTo` writes the current meta at
        # page txid%2 (e1fae5c, a bug: two torn meta writes after restoring an odd-txid copy
        # leave no valid meta), `%v` for errors in logger calls (27b1412, upstream main's change)
        # and a no-op default logger (b3e06648); then `Open` maps the file through `mmapUnlocked`, closes
        # under the locks after its transaction began, and `loadFreelist` publishes the freelist
        # under `metalock` (743299d8, verification only); then a writable `Open` fdatasyncs the file
        # before its first commit (c5a6065d, issues/bbolt-open-unsynced-meta-kill-then-power-loss.md;
        # 004c930 its robustness test), closing under the locks if that sync fails (ea4cab52, as the
        # failed transaction's exit: the proof needs the locks' halves of the fields `close` clears); then
        # `Put` refuses an entry (key plus value) above 2^28 bytes with `ErrValueTooLarge` (3f8520bd, branch
        # `goose-lean-entrymax`; issues/bbolt-max-value-size-unusable.md: `Put` accepted values a page of four
        # entries cannot hold within `MaxAllocSize`; the verified bbolt's `bboltEntryMax`; approved by the
        # user 2026-11-19, auth-schema-srv port, route (d')). Branch goose-lean-init-image (42c80a7) restricts init recovery to the
        # first write's four-page image. With bodies (bbolt.toml, bbolt/**.toml; notes/bbolt-v2-infra.md). Its `os`,
        # `io/fs`, `syscall` and `golang.org/x/sys/unix` (project bboltfs: the models of the Linux
        # file extension osFsExt), `hash` and `encoding/hex` (project etcd) are this repository's
        # translations. Modules
        # Code.go_etcd_io.bbolt*, GeneratedProof.go_etcd_io.bbolt*.
        repo="https://github.com/upamanyus/bbolt",
        # Split oversized leaves and admit all individually readable key/value pairs.
        # Then (real fmt stage 1, 2026-11-24, #9) 7d335aa3e (branch `goose-lean-fmt1`, on ca88bb6a8):
        # `Options.String` formats its bools with `%v` (as `%t`), the free-list type as a string, and
        # whether `OpenFile`/`Logger` are set in place of their addresses (`%p`).
        rev="7d335aa3eb233822487e9dd7eb2c8f95d99ea2ad",
        lean_roots=["go.etcd.io/bbolt=", "golang.org/x/sys=", "syscall=", "hash=",
                    "encoding/hex=", "os=", "io/fs="],
        packages=[
            "go.etcd.io/bbolt",
            "go.etcd.io/bbolt/errors",
            "go.etcd.io/bbolt/internal/common",
            "go.etcd.io/bbolt/internal/freelist",
        ],
        owned=[os.path.join("go_etcd_io", "bbolt")],
        counted_modules=["go.etcd.io/bbolt"],
    ),
    Project(
        name="etcd",
        # Branch `goose-lean`: upstream main (2026-10), the commits that make it
        # translatable, and the four bug fixes of `cache-ready-after-retry` (64313a1f8; its
        # two other commits are reverted: no code change unless it fixes a bug),
        # `recipes-closed-watch-channel` (0aa6c6af8, cherry-picked as 0df483bee) and
        # `watch-progress-closed-substream` (1ac646214, cherry-picked as 107edf7e4) and
        # `watch-progress-before-created` (c267e0ffe, cherry-picked as 09669450f), and the
        # backend's write-back dedupe, etcd-io/etcd#21987 cherry-picked with regression tests
        # as ea78ec948 (issues/etcd-backend-duplicate-put-stale-read.md; D19i (A)), and
        # `raftAdvancedC` (issues/etcd-compact-past-raft-applied.md; D19i part 1) as 06aa6e6e, and
        # (D19l) etcd-io/etcd#22297 cherry-picked as 5615016f6 (`syncWatchersLoop`'s ticker reset,
        # nonissues/etcd-watch-sync-ticker-reset-zero.md) and `AuthInfoFromTLS`'s checked assertion
        # as 17c88a667 (nonissues/etcd-auth-tls-info-assert.md), and the client's
        # `closeRequireLeader` context alignment (a7bd9a16e,
        # issues/etcd-lease-close-require-leader-ctx-misaligned.md) and the retry interceptor's
        # non-repeatable context-error return (8a24be2a3, nonissues/etcd-client-retry-put-ctx-error.md),
        # and the gRPC quota's current backend (8f793b820,
        # issues/etcd-quota-stale-backend-after-snapshot.md; D22g (A)) and the auth store's move
        # before the old backend's close (d52eec43e,
        # issues/etcd-auth-snapshot-closed-backend-panic.md; D22k (A)), and the merged snapshot
        # sent only at its message's term (de825d8c6, issues/etcd-merged-snapshot-stale-term.md;
        # D22a), and (D25, the watch client's reconnection) the four fixes of branch
        # `watch-resume-fixes` (04375baaa..b3c29bc17, made on 8a24be2a3) cherry-picked on top: a
        # server-canceled substream's id reset (cafce83d8,
        # nonissues/etcd-watch-resume-stale-canceled-id.md) and no nil channel on `retc`
        # (c15c7dda8, nonissues/etcd-watch-resume-nil-watch-chan.md) and the resume revision only
        # moving forward (2e2dc077c, issues/etcd-watch-resume-below-start-revision.md) and
        # `waitCancelSubstreams` adding one goroutine at a time to its wait group (2aed163b1,
        # nonissues/etcd-watch-resume-waitgroup-overflow.md), and (D22, the snapshot path) the alarm
        # store recovered in place (8fd98af04, issues/etcd-alarm-store-snapshot-race.md) and a
        # snapshot's older files released only after `applySnapshot` opens it (188113160,
        # issues/etcd-release-snapdb-before-open.md). Then (D30n, 2026-10-23) branch
        # `goose-lean-getproph2` (on 188113160; `goose-lean-getproph`'s 942601555 made on
        # 2aed163b1, cherry-picked): `kubernetes.Client.Get` resolves a prophecy with its
        # response's revision and the key's mod revision (bc9c3868c; verification only, a no-op
        # in Go). Then (D43 M3, 2026-10-25) branch `goose-lean-leaderwait` (on bc9c3868c): the
        # leader's raft loop waits for its apply loop before `Advance` when a `Ready` commits a
        # conf change, as a follower's does (4d9282b0f,
        # issues/etcd-leader-advance-before-applyconfchange.md; raft's dynamic mode needs a
        # `Ready`'s conf changes applied before `Advance`). Then (D43 M4, 2026-10-26) branch
        # `goose-lean-learnerfix` (on 4d9282b0f): a removed local member is no learner, rather
        # than a panic (c00a2dc06, issues/etcd-unary-interceptor-learner-removed.md;
        # etcd-io/etcd#22188's fix). Then (the auth plan's E3z, 2026-10-27) branch
        # `goose-lean-grantfix` (on c00a2dc06): `RoleGrantPermission` replaces every permission
        # on the range (acafa0317, issues/etcd-auth-grant-permission-same-key.md). Then (the
        # spec-first pilot, 2026-10-27) branch `goose-lean-grantfix-compactorstart` (on acafa0317):
        # the auto-compactor run by `start()`, not by `NewServer` (a20f6760f, the cherry-pick of
        # 964dccdb4; nonissues/etcd-compactor-started-before-start.md). Then (M2, 2026-10-28) branch
        # `goose-lean-compactfix` (on a20f6760f): upstream's fixes of the compaction of a key deleted
        # and put again in the compacted revision (etcd-io/etcd#22377, `keyIndex.doCompact`,
        # e7bb9f2de; #22395, the gRPC txn overlap check, 249d76bea;
        # issues/etcd-compaction-delete-then-put.md). Then (S1, the snapshot plan's #7, 2026-10-31)
        # branch `goose-lean-snapguard` (on 249d76bea): the queued MsgSnap merged only if its
        # snapshot is at or below the applied index (633036387; a guard for the proof, not a bug
        # fix: notes/decisions.md, "The merged snapshot's index guard"). Then (#8's J8a-3,
        # 2026-11-01) branch `goose-lean-watchcfg` (on 633036387): `NewWatchServer` keeps the adjusted
        # progress interval local instead of writing `s.Cfg` (7cf3644ec,
        # nonissues/etcd-cfg-watch-progress-interval-race.md). Then (#8's J8a-7, 2026-11-01) branch
        # `goose-lean-remotepause` (on 7cf3644ec): a remote paused by a flag under its own mutex,
        # as a peer, so that `CutPeer`/`MendPeer` may be repeated (ab3c28d9a; the nonissue
        # nonissues/etcd-rafthttp-cutpeer-twice-remote-panic.md). Then (the restart plan's R2b-1,
        # 2026-11-02) branch `goose-lean-walsnap` (on ab3c28d9a): `wal.ReadAll` returns the log the
        # records write, not entries a received snapshot discarded (6293455e0, revised ce3dbc097,
        # nonissues/etcd-wal-stale-entries-above-snapshot.md), and `recoverSnapshot` opens the WAL at
        # the snapshot record of the highest index (nonissues/etcd-wal-snapshot-record-order.md);
        # then (the WAL API's axiom review, 2026-11-03, 323320bb8) a restart at a received snapshot
        # names its next WAL file after it, and `LatestSnapshotEntry` takes the highest record
        # (nonissues/etcd-wal-restart-file-below-snapshot.md). Then (2026-11-03) branch
        # `goose-lean-noproph2` (on 323320bb8): bc9c3868c reverted (673da07c8), its prophecy now the
        # prophecy patch etc/proph-patches/etcd/01-client-get-revision.patch (notes/decisions.md,
        # "Prophecies as patches of the Go code"); the fork carries no code for verification only.
        # Then (sweep repairs 1, R1-3, 2026-11-08) a4d2bb172 on `goose-lean`: `purgeFile` no longer
        # purges `.snap.db` files (`ReleaseSnapDBs` removes the ones below an opened or taken
        # snapshot; nonissues/etcd-purge-snapdb-unopened.md, the user's option A via etcd-grove-82).
        # Then (the WAL crash spec's W3, 2026-11-11) branch `goose-lean-walsync` (on a4d2bb172): the
        # WAL's three power-loss fixes the user approved, for the bare fsync(2) contract:
        # `ReadAll` fdatasyncs the tail it zeroed (41fddbc2d,
        # nonissues/etcd-wal-readall-zero-unsynced.md), `Create` fsyncs `<dir>.tmp` before renaming
        # it (161796636, nonissues/etcd-wal-create-dir-entry-unsynced.md), and `TouchDirAll` fsyncs
        # the parent of each directory it creates (71f99a4bf,
        # nonissues/etcd-fileutil-touchdirall-parent-unsynced.md).
        # Then (W3b, 2026-11-11) b18c2d500 on `goose-lean` (F-N4, for a kill, a restart without a
        # reboot, then a power loss): `TouchDirAll` fsyncs the parent of an existing directory too
        # (055b2f69a, nonissues/etcd-fileutil-touchdirall-existing-after-kill.md), and `ReadAll` in
        # write mode fsyncs the WAL directory and its parent (b18c2d500,
        # nonissues/etcd-wal-dir-names-after-kill.md).
        # Then (WAL W4a revision, 2026-11-12) c90b03b56 on `goose-lean`: `Exist` reports a WAL when
        # its directory cannot be read, so `Create` never removes one
        # (nonissues/etcd-wal-exist-readdir-error-removes-wal.md).
        # Then (WAL W4a.2, 2026-11-12) 1aaca041c on `goose-lean-exist`: a write-mode `ReadAll` reports
        # `ErrSnapshotNotFound` when no record matched its start snapshot
        # (nonissues/etcd-wal-readall-snapshot-not-found-masked.md).
        # Then (WAL W4a.2, 2026-11-12) 0b50f0426 on `goose-lean-exist`: a cut names its segment
        # max(w.enti, the highest snapshot index saved or read)+1, so that Open at a snapshot of the
        # WAL starts at or before its record (the same nonissue).
        # Then (restart S6a, 2026-11-13) 2eaeb872b on `goose-lean-snaplink` (on 0b50f0426):
        # `SaveDBFrom` links its file into place (`os.Link`), so that of two concurrent saves of one
        # index exactly one puts its file in place and the other keeps it
        # (nonissues/etcd-snap-savedbfrom-concurrent-rename.md; the user's decision via etcd-grove-81).
        # Then (restart3 A1, 2026-11-15) 6e8f0c004 (branch `restart3-ag`, on 2eaeb872b; to be pushed
        # to `goose-lean`): `applyAll`'s merge defers a merged snapshot inside the replay window
        # (`ep.appliedi < ConsistentIndex()`) and reports every dropped `MsgSnap` failed
        # (`ReportSnapshot`), so that a merged image is always at its own index and a dropped one
        # does not leave the follower in `StateSnapshot` (notes/restart3-a0-draft.md §3, §8; D-A0-1,
        # approved by the user via etcd-grove-81; D-A0-6).
        # Then (the WAL over fsExt, 2026-11-14) branch `goose-lean-walfs`: the WAL's local fixes
        # 0001-0005 (notes/wal-fsext-fork/README.md: `NewFileReader`'s Stat, `Create`'s cleanup, the
        # byte-mix tests, `N.tmp` opened with `O_TRUNC`, `Create`'s parent close) and 0006 (2026-11-15:
        # `WAL.Sync` takes `w.mu`, issues/etcd-wal-sync-releaselockto-race.md, the reproduced data
        # race with `ReleaseLockTo`), first on 2eaeb872b (3df9b265f, e115818f5), rebased (2026-11-16,
        # wal-lean session 6) onto 6e8f0c004 with each commit's author, committer and dates kept:
        # 8c28a4296. Then (wal-link, 2026-11-18, approved by the user via etcd-grove-03) fix 0007
        # on it, branch `goose-lean-walfs3`: `SaveSnapshot` cuts once the tail passes
        # `SegmentSizeBytes`, as `Save` does (nonissues/etcd-wal-savesnapshot-tail-efbig.md):
        # f01ae14c9; then 0008 (34dea163a, branch `goose-lean-walfs3-fp`): `SaveSnapshot` does not cut
        # while `w.fp` is nil (`Create`'s call, before the pipeline exists; 0007 alone made a `Create`
        # whose first segment passes `SegmentSizeBytes` panic in `cut`).
        # Then 0009 (wal-link, 2026-11-19, approved by the user via etcd-grove-03; d3feef9bc, branch
        # `goose-lean-walfs3-fp9`, pushed 2026-11-19): `WAL.Save` refuses a batch whose sum of `proto.Size(e)+64` passes
        # `MaxSaveBatchBytes` (4 TiB) with `ErrSaveBatchTooLarge`, before `w.mu.Lock()`
        # (nonissues/etcd-wal-save-batch-efbig.md).
        # Branch
        # `goose` (upstream main of 2026-03) stays as it is: the Rocq translations
        # (etcd-grove `main`, Perennial `master`) are regenerated from it by name.
        repo="https://github.com/upamanyus/etcd",
        # Includes legacy WAL recovery and the same-term snapshot send without an index guard.
        # Then (auth-mediation M3, 2026-11-21, the user's Q4 option (i) via etcd-grove-03) 4416a5786
        # (branch `goose-lean-rangestream-clone`, on 34f5142d0): upstream's fix of the keys-only
        # `RangeStream` data race cherry-picked (etcd-io/etcd@9acc0ebe37: `rangeStream`'s next key is
        # `append(bytes.Clone(lastKey), 0)`, no longer an append into mvcc's index key;
        # nonissues/etcd-rangestream-keysonly-index-key-race.md).
        # goose-lean-replay-snapshot-readers keeps the legacy WAL recovery and RangeStream fixes.
        # Same-term snapshots stream the backend during restart replay. The label comes from the
        # frozen image and its Ready's retained entry terms (issues/etcd-merged-snapshot-replay-failure.md).
        # Then (errors-astype, 2026-11-22, mit-pdos/etcd-grove#29, the user's decision) edc800c6f
        # (branch `goose-lean-astype`, on d7c7f6434): `errors.As` -> Go 1.26's `errors.AsType`, the
        # modernize analyzer's errorsastype rewrite across the modules, and by hand where `As` is the
        # first operand of an `&&` (fileutil's preallocExtend/preallocFixed, isSafeRetryImmutableRPC),
        # so that those proofs use Perennial's proved `AsType` spec instead of its `errors.As` axiom.
        # Then (prove-ps2-srvgoroutines, 2026-11-24, etcd-grove#42 item 2, per the fmt decision on
        # mit-pdos/perennial#671) bc2b5f4d0 (branch `goose-lean-fmtattrs`, on edc800c6f): `publishV3`'s
        # three log lines format the member's attributes field by field,
        # `fmt.Sprintf("{Name:%s ClientURLs:[%s]}", Name, strings.Join(ClientURLs, " "))`, the same bytes
        # as `fmt.Sprintf("%+v", s.attributes)`, which reaches fmt's reflection-based `printValue`.
        # Then (sortslice, 2026-11-24, mit-pdos/etcd-grove#18, approved by Upamanyu via
        # coordinator-E) 6b942d23f (branch `goose-lean-slicessort-on-fmtattrs`, on bc2b5f4d0; first
        # a336e97f9 on edc800c6f, branch `goose-lean-slicessort`): mvcc's `hashStorage.Store` sorts with
        # `slices.SortFunc(s.hashes, cmp.Compare on Revision)` instead of `sort.Slice` (whose reflection
        # Perennial does not model), an upstream-ready change.
        # Then (real fmt stage 1, 2026-11-24, mit-pdos/etcd-grove#9) 3d8797e8 (branch
        # `goose-lean-fmt1c`, the commits of `goose-lean-fmt1` rebased onto 6b942d23f): `Election.Campaign`, `Mutex.tryAcquire` and
        # `store.restore` convert a method-less named lease ID to `int64` before `fmt.Sprintf`
        # formats it (`%x`, `%016x`): byte-identical output, through `fmtInteger` (Perennial's verified
        # subset) instead of `printValue`. Then df6af0c36 (same branch): `Client.dial` numbers its
        # dial targets with a package counter (`clientTargetSeq`, an `atomic.Uint64`) in place of
        # `%p` of the client, which real `fmt` does not cover (the decision on #9,
        # issuecomment-7122889900: fork rewrites, no `%p` axiom).
        rev="df6af0c36a6bf5394765d3740aaf26ca27eb8ca9",
        # grpc-go v1.84.0 (etcd's go.mod) from its model, models/grpc (the same API; its transport
        # and connection management replaced: models/README.md, "The grpc model"), so that grpc's
        # specs can be proved over the model's bodies (notes/phase7-plan.md, S0)
        module_models={"google.golang.org/grpc": "models/grpc"},
        # (#24 J3, 2026-11-23) membership's records with the encoding/json model's same-package methods
        # (`JSONModel*`, over models.lab/jsoncodec: the part Net/'s translation, `models.lab=Net`):
        # the member records the backend, the v2 store and the conf-change contexts hold
        jsonmodel_roots=["go.etcd.io/etcd/server/v3/etcdserver/api/membership." + t
                         for t in ("Member", "RaftAttributes", "Attributes", "ConfigChangeContext")],
        # go.etcd.io/raft/v3 (etcd's go.mod: v3.7.0) is the raft above (v3.7.0 plus the
        # read-index fix), translated by the raft project: not translated here.
        lean_roots=["go.etcd.io/etcd=", "k8s.io=", "google.golang.org=", "go.uber.org=",
                    "models.lab=Net",
                    "go.etcd.io/bbolt=", "go.opentelemetry.io=", "os=", "io/fs=",
                    "github.com/dustin/go-humanize=", "github.com/prometheus/client_golang=",
                    "github.com/prometheus/client_model=",
                    "github.com/jonboulle/clockwork=",
                    "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net", "hash=", "path=", "internal/nettrace=",
                    "encoding/hex=", "container/heap=",
                    "github.com/Masterminds/semver=", "go.etcd.io/raft/v3=",
                    "golang.org/x/time=", "golang.org/x/crypto=", "github.com/xiang90/probing=",
                    "crypto/tls=",
                    # (D43 M4, 2026-10-26) membership's `json.Unmarshal` (the k8s-apiserver
                    # project's names-only translation, `Code/encoding/json.lean`)
                    "encoding/json=",
                    "github.com/grpc-ecosystem=",
                    # the server's UserAdd/UserChangePassword (the auth plan's E2x): base64 names
                    # only, the k8s-apiserver project's translation (Code/encoding/base64.toml)
                    "encoding/base64=",
                    # (the WAL over fsExt, 2026-11-15: notes/wal-lean-integration.md) the
                    # standard-library packages the WAL calls that Perennial does not translate:
                    # `bufio`'s Reader and `path/filepath`'s lexical functions (over
                    # `internal/filepathlite`) with bodies, `hash/crc32` (`hash=` above) names only
                    "bufio=", "path/filepath=", "internal/filepathlite=",
                    # (crc32-hooks2, 2026-11-22) `hash/crc32`'s `slicingUpdate` calls
                    # `byteorder.LEUint32` (project k8s-apiserver's translation,
                    # Code/internal/byteorder.toml)
                    "internal/byteorder=",
                    # (the same) `fileutil`'s lock and preallocation calls: the per-byte file
                    # extension's `syscall` and `golang.org/x/sys/unix` (project bboltfs's), as `os=`
                    "syscall=", "golang.org/x/sys=", "internal/poll=", "internal/syscall=",
                    # (featuregate-3, 2026-11-23) `flag`, which featuregate's `MutableFeatureGate`
                    # names (`AddFlag(*flag.FlagSet, ...)`): this repository's, as `os=` (Perennial's
                    # would import Perennial's `os`, which must never meet project bboltfs's)
                    "flag="],
        packages=[
            # with bodies (cache/v3.toml)
            "go.etcd.io/etcd/cache/v3",
            # with bodies (client/v3/concurrency.toml): Session, Mutex, Election, STM
            "go.etcd.io/etcd/client/v3/concurrency",
            # with bodies (client/v3/leasing.toml): the leasing KV and its lease cache
            "go.etcd.io/etcd/client/v3/leasing",
            # with bodies (client/v3/experimental/recipes.toml): barrier, double barrier, queue,
            # priority queue, RWMutex
            "go.etcd.io/etcd/client/v3/experimental/recipes",
            # the server's consistent index, with bodies (cindex.toml), or some of them
            # (etcdserver.toml: the apply thread; storage/schema.toml: cindex.go)
            "go.etcd.io/etcd/server/v3/etcdserver/cindex",
            "go.etcd.io/etcd/server/v3/etcdserver",
            "go.etcd.io/etcd/server/v3/storage/schema",
            "go.etcd.io/etcd/server/v3/storage/schema/snapshotmeta",
            # with bodies (pkg/v3/adt.toml): the interval tree of mvcc's watcher groups
            "go.etcd.io/etcd/pkg/v3/adt",
            # with bodies (etcdserver/txn.toml): the server's Range, Put, DeleteRange, Txn over
            # the mvcc core
            "go.etcd.io/etcd/server/v3/etcdserver/txn",
            # with bodies (etcdserver/apply.toml): the applier chain, between the apply thread
            # and the txn package (metrics.go names only)
            "go.etcd.io/etcd/server/v3/etcdserver/apply",
            # with bodies (etcdserver/api/v3rpc.toml): the gRPC KV service's handlers, the
            # request checks, the response header, togRPCError (the request path)
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc",
            # with bodies (etcdserver/api/v3lock.toml, v3election.toml; the auth plan's A3c):
            # the Lock and Election services' servers over the client's concurrency package,
            # and their protobuf messages (v3lock/v3lockpb.toml, v3election/v3electionpb.toml)
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3lock",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3lock/v3lockpb",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3election",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3election/v3electionpb",
            # names only, with the two features the request path reads
            "go.etcd.io/etcd/server/v3/features",
            # with bodies (storage/backend.toml): the backend over bbolt, its buffers and
            # transactions
            "go.etcd.io/etcd/server/v3/storage/backend",
            # types and names only: what the server's types and the apply thread name
            "go.etcd.io/etcd/server/v3/storage",
            "go.etcd.io/etcd/server/v3/storage/mvcc",
            "go.etcd.io/etcd/server/v3/config",
            # with bodies (storage/datadir.toml): the data directory's layout, `BackendPath`'s
            "go.etcd.io/etcd/server/v3/storage/datadir",
            "go.etcd.io/etcd/server/v3/etcdserver/api/membership",
            "go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp",
            "go.etcd.io/etcd/server/v3/etcdserver/api/snap",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v2stats",
            # names only (D21 M2): `Process`'s `403` errors (`httptypes.NewHTTPError`)
            "go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp/types",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm",
            # with bodies (etcdserver/api/v3compactor.toml): the auto-compactor (the spec-first
            # pilot, notes/compactor-pilot-plan.md)
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3compactor",
            # names only: what the apply package names (api.UpdateCapability,
            # version.DowngradeInfo, the membership requests, semver)
            "go.etcd.io/etcd/server/v3/etcdserver/api",
            "go.etcd.io/etcd/server/v3/etcdserver/version",
            "go.etcd.io/etcd/api/v3/membershippb",
            # names only: the version strings the server's `start` logs (the request path's
            # unit 4c)
            "go.etcd.io/etcd/api/v3/version",
            "go.etcd.io/etcd/api/v3/authpb",
            "github.com/Masterminds/semver/v3",
            "go.etcd.io/etcd/server/v3/etcdserver/errors",
            "go.etcd.io/etcd/server/v3/etcdserver/read",
            "go.etcd.io/etcd/server/v3/lease",
            # names only (the lease-renew plan, 2026-11-01): `LeaseRenew`'s forwarding to the
            # leader (`RenewHTTP`, `LeasePrefix`), a contract
            "go.etcd.io/etcd/server/v3/lease/leasehttp",
            # types only: the lease's protobuf message (the lessor's persistTo, Revoke)
            "go.etcd.io/etcd/server/v3/lease/leasepb",
            "go.etcd.io/etcd/server/v3/auth",
            # names only but for the cost bounds `auth.NewAuthStore` reads (the auth plan's E2a)
            "golang.org/x/crypto/bcrypt",
            "go.etcd.io/etcd/pkg/v3/contention",
            "go.etcd.io/etcd/pkg/v3/idutil",
            # (prove-ps2-srvgoroutines, 2026-11-24, #42) `FDUsage`/`FDLimit` trusted (pkg/v3/runtime.toml):
            # `monitorFileDescriptor`'s leaves
            "go.etcd.io/etcd/pkg/v3/runtime",
            "go.etcd.io/etcd/pkg/v3/notify",
            "go.etcd.io/etcd/pkg/v3/pbutil",
            "go.etcd.io/etcd/pkg/v3/traceutil",
            # names only: the type of mvcc's store.fifoSched
            "go.etcd.io/etcd/pkg/v3/schedule",
            # with bodies (pkg/v3/wait.toml, pkg/v3/idutil.toml): the wait registry and the
            # request id generator of the request path
            "go.etcd.io/etcd/pkg/v3/wait",
            "go.etcd.io/etcd/client/pkg/v3/types",
            "go.etcd.io/etcd/client/pkg/v3/verify",
            # names only: what the raft wrapper's construction names (stage R8b of the raft
            # v3.7 retarget, 2026-10-16: `newRaftNode`'s dead logger branch, the WAL
            # `bootstrappedRaft.newRaftNode` wraps)
            "go.etcd.io/etcd/client/pkg/v3/logutil",
            # (the WAL over fsExt, 2026-11-13; in the main tree since 2026-11-15) the real WAL with
            # bodies (wal.toml: but version.go and metrics.go, names only), `walpb`, `fileutil`,
            # `pkg/v3/ioutil` (PageWriter) and `pkg/v3/crc`, and the standard-library packages they
            # call that nothing else translates (`hash/crc32` names only; `bufio`'s `Reader` and
            # `path/filepath`'s lexical functions, over `internal/filepathlite`, with bodies)
            "go.etcd.io/etcd/server/v3/storage/wal",
            "go.etcd.io/etcd/server/v3/storage/wal/walpb",
            "go.etcd.io/etcd/client/pkg/v3/fileutil",
            "go.etcd.io/etcd/pkg/v3/crc",
            "hash/crc32", "bufio", "path/filepath", "internal/filepathlite",
            "go.etcd.io/etcd/client/pkg/v3/transport",
            "go.etcd.io/etcd/pkg/v3/featuregate",
            # (featuregate-3) names only, but for its initializers and `init` (Code/flag.toml)
            "flag",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3discovery",
            # (go.etcd.io/bbolt, etcd's go.mod: v1.5.0, is the bbolt project's translation, from
            # the fork: not translated here)
            "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc",
            # names only: what mvcc's watchStream.Watch calls (SpanFromContext, Span.End)
            "go.opentelemetry.io/otel/trace",
            # types only: the interfaces trace.Span embeds and the types of its methods' parameters
            # (so that Goose translates Span as an interface)
            "go.opentelemetry.io/otel/trace/embedded",
            # (otel-tracing, 2026-11-23) with bodies: the no-op tracer `traceutil.Tracer` holds
            # (`noop.NewTracerProvider().Tracer(...)`, its initializer)
            "go.opentelemetry.io/otel/trace/noop",
            "go.opentelemetry.io/otel/codes",
            "go.opentelemetry.io/otel/attribute",
            # (prove-misc, 2026-11-20) names only but its package variables: the carrier interface
            # otelgrpc's `metadataSupplier` is asserted to implement (`var _ propagation.TextMapCarrier`)
            "go.opentelemetry.io/otel/propagation",
            "google.golang.org/protobuf/proto",
            "google.golang.org/protobuf/reflect/protoreflect",
            "go.uber.org/zap",
            "go.uber.org/zap/zapcore",
            # (prove-misc, 2026-11-20) what zapcore's package variables call: its generic `sync.Pool`
            # wrapper (`pool.New`) and its terminal colors (`color.Add`, `fmt.Sprintf`)
            "go.uber.org/zap/internal/pool",
            "go.uber.org/zap/internal/color",
            # (prove-initleft, 2026-11-21) types only: `LeveledEnabler`, which zap's `var _` asserts
            "go.uber.org/zap/internal",
            # (zap-z1, 2026-11-23) what `Logger.check` names on paths no proof takes (stack traces,
            # buffers): names only but the package variables of `bufferpool` (`check` reads `Get`)
            # and the `buffer.NewPool` they call
            "go.uber.org/zap/internal/stacktrace", "go.uber.org/zap/internal/bufferpool",
            "go.uber.org/zap/buffer",
            # (zap-z2, 2026-11-23) what `zapcore.CheckedEntry.Write` and its terminal hooks call: zap's
            # `internal/exit` (`With`, over `os.Exit`) with its body, `multierr` names only (no core)
            "go.uber.org/zap/internal/exit", "go.uber.org/multierr",
            # names only: the auto-compactor's clock (the spec-first pilot)
            "github.com/jonboulle/clockwork",
            "github.com/dustin/go-humanize",
            # names only: the metrics mvcc's transactions and key index update
            "github.com/prometheus/client_golang/prometheus",
            # (prove-ps2-metrics, 2026-11-22) names only: the package of the type of prometheus's
            # `gauge`'s field `labelPairs` (`[]*dto.LabelPair`), so that the struct is translated (its
            # methods are, with their bodies). (`counter` also needs `timestamppb`, whose names-only
            # initializer would add two trust-boundary axioms: not taken.)
            # (prom-registry, route (b), 2026-11-22) and of `Desc.constLabelPairs` (the default registry
            # is translated)
            "github.com/prometheus/client_model/go",
            # standard-library packages Perennial does not translate: their names are here
            # (encoding/hex: the backend's putSeq check formats keys with it)
            "net/http",
            # (prove-http3, 2026-11-21) `CanonicalMIMEHeaderKey` and `MIMEHeader.Set`/`Get`, with
            # their bodies (Code/net/textproto.toml): what `http.Header.Set`/`Get` call
            "net/textproto",
            # (net-swap, 2026-11-22) `net` is the part Net/'s (project net's, over the net extension:
            # `net=Net` below), no longer translated here names only
            "encoding/hex",
            # (container/heap: the lessor's expiry notifier pushes and fixes its queue)
            "container/heap",
            # types and names only (their .toml)
            "go.etcd.io/etcd/client/v3",
            # with bodies (client/v3/kubernetes.toml): the client the Kubernetes API server's
            # etcd3 store calls (project k8s-apiserver; notes/k8s-etcd3-goose.md)
            "go.etcd.io/etcd/client/v3/kubernetes",
            # names only: grpc's logger, which the etcd3 store names (project k8s-apiserver)
            "google.golang.org/grpc/grpclog",
            # (prove-k8s3, 2026-11-21) types only: the interface grpclog's `LoggerV2` names
            "google.golang.org/grpc/grpclog/internal",
            "go.etcd.io/etcd/api/v3/etcdserverpb",
            "go.etcd.io/etcd/api/v3/mvccpb",
            "go.etcd.io/etcd/api/v3/v3rpc/rpctypes",
            "k8s.io/utils/third_party/forked/golang/btree",
            # names only: what `clientv3.WatchResponse.Err` calls
            "google.golang.org/grpc/codes",
            "google.golang.org/grpc/status",
            # names only: the target of the alias grpc/status.Status (client/v3/leasing)
            "google.golang.org/grpc/internal/status",
            # the types of protobuf messages' fields (protoimpl.MessageState, ...)
            "google.golang.org/protobuf/runtime/protoimpl",
            "google.golang.org/protobuf/internal/impl",
            "google.golang.org/protobuf/internal/pragma",
            # names only: the types of clientv3.Client's fields
            "google.golang.org/grpc",
            "google.golang.org/grpc/credentials",
            # types and names only: the peer the client's retry interceptor asks grpc for
            # (unit P3a)
            "google.golang.org/grpc/peer",
            # types and names only: the incoming metadata the auth store's AuthInfoFromCtx
            # reads (unit P2)
            "google.golang.org/grpc/metadata",
            "go.etcd.io/etcd/client/v3/credentials",
            "go.etcd.io/etcd/client/v3/internal/resolver",
            # names only (item 5, client construction): what `clientv3.New`'s dial names:
            # the credentials requirement of an endpoint, grpc's keepalive parameters, insecure
            # credentials and resolver builders (the type of `grpc.WithResolvers`'s parameter,
            # for the trusted body of `dialWithBalancer`), and the type of `Config.TLS`
            # (crypto/tls, a standard-library package Perennial does not translate)
            "go.etcd.io/etcd/client/v3/internal/endpoint",
            "google.golang.org/grpc/keepalive",
            "google.golang.org/grpc/credentials/insecure",
            "google.golang.org/grpc/resolver",
            # (prove-grpc3, 2026-11-21) with bodies: the manual resolver etcd's resolver embeds;
            # types only: the types of its and grpc's resolver state's fields
            "google.golang.org/grpc/resolver/manual",
            "google.golang.org/grpc/serviceconfig",
            "google.golang.org/grpc/attributes",
            "crypto/tls",
            # types only (the interfaces `Hash`, `Hash32`, ...): the type of mvcc's
            # `kvHasher.hash` field, so that Goose translates `kvHasher`
            "hash",
            # types and names only: the FNV hash the DaemonSet controller's `controller.ComputeHash`
            # writes into (project k8s-daemonset; notes/k8s-daemonset-goose.md); here since this
            # project owns `hash`
            "hash/fnv",
            # names only (D38, rafthttp's stage 1): what rafthttp's message path calls of the
            # standard library's `path` (the stream handler's URL parsing) and of etcd's
            # `pkg/v3/ioutil` (the pipeline handler's limited reader) and `pkg/v3/httputil`
            "path",
            "go.etcd.io/etcd/pkg/v3/ioutil",
            "go.etcd.io/etcd/pkg/v3/httputil",
            # names only (item 4, the server start): what `v3rpc.Server` names: grpc-prometheus
            # (its server metrics and interceptors), grpc's health service and its protobuf
            # package (the registration, the serving status), grpc's reflection interface
            # (`ServerMetrics.InitializeMetrics`'s parameter)
            "github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus",
            "google.golang.org/grpc/health",
            "google.golang.org/grpc/health/grpc_health_v1",
            "google.golang.org/grpc/reflection",
            # types and names only: grpc's stats handler interface, the type of otelgrpc's
            # `NewServerHandler`'s result (so that an implementation can return one: etcd-refimpl)
            "google.golang.org/grpc/stats",
            # (and go.uber.org/zap, above)
            # names only: the types of rafthttp.Transport's fields, so that its struct is
            # translated (NewServer builds one; unit N4, 2026-10-17)
            "golang.org/x/time/rate",
            "github.com/xiang90/probing",
            # names only: the types of the server's configuration's fields (types.URLs' url.URL,
            # transport.TLSInfo's crypto/tls types, crypto/tls listed above), so that those
            # structs are translated (NewServer splits the configuration; unit N4, 2026-10-17)
            "net/url",
            # types only (k8s 7f-4, Addendum T-h0): the context keys net/http's client reads
            # (`httptrace.clientEventContextKey`, `nettrace.TraceKey`,
            # `nettrace.LookupIPAltResolverKey`), named by `leasehttp.RenewHTTP.spec`'s premise
            "net/http/httptrace",
            "internal/nettrace",
        ],
        owned=[os.path.join("go_etcd_io", "etcd"),
               os.path.join("github_com", "prometheus"),
               os.path.join("github_com", "Masterminds"),
               os.path.join("k8s_io", "utils", "third_party"), "google_golang_org", "go_uber_org",
               "go_opentelemetry_io",
               os.path.join("net", "http"), os.path.join("net", "textproto"), os.path.join("net", "url"),
               "hash", "path", os.path.join("internal", "nettrace"), os.path.join("encoding", "hex"),
               os.path.join("crypto", "tls"),
               os.path.join("container", "heap"),
               os.path.join("github_com", "dustin"), os.path.join("github_com", "jonboulle"),
               os.path.join("golang_org", "x", "time"),
               os.path.join("golang_org", "x", "crypto"),
               os.path.join("github_com", "xiang90"),
               os.path.join("github_com", "grpc_ecosystem"),
               "bufio", os.path.join("path", "filepath"), os.path.join("internal", "filepathlite"),
               "flag"],
        # etcd itself: not its tests, tools or root module
        counted_modules=[
            "go.etcd.io/etcd/api/v3",
            "go.etcd.io/etcd/cache/v3",
            "go.etcd.io/etcd/client/pkg/v3",
            "go.etcd.io/etcd/client/v3",
            "go.etcd.io/etcd/etcdctl/v3",
            "go.etcd.io/etcd/etcdutl/v3",
            "go.etcd.io/etcd/pkg/v3",
            "go.etcd.io/etcd/server/v3",
        ],
        # the WAL's records alone into the part RaftNoAx too, over its raftpb
        # (notes/raft-noax-part.md): `proto`'s schemas (`PbSchema.lean`), which raft's message
        # invariant reads, name walpb's two registered types
        parts=[Part(
            root="RaftNoAx",
            lean_roots=["go.etcd.io/etcd/server/v3/storage/wal/walpb=RaftNoAx", "go.etcd.io/etcd=",
                        "go.etcd.io/raft/v3=RaftNoAx", "google.golang.org="],
            packages=["go.etcd.io/etcd/server/v3/storage/wal/walpb"],
            owned=[os.path.join("go_etcd_io", "etcd", "server", "v3", "storage", "wal", "walpb")]),
            # and into the part KvNet, over its raft (raft-noax's; notes/kvnet-part.md)
            Part(
            root="KvNet",
            lean_roots=["go.etcd.io/etcd/server/v3/storage/wal/walpb=KvNet", "go.etcd.io/etcd=",
                        "go.etcd.io/raft/v3=KvNet", "google.golang.org="],
            packages=["go.etcd.io/etcd/server/v3/storage/wal/walpb"],
            owned=[os.path.join("go_etcd_io", "etcd", "server", "v3", "storage", "wal", "walpb")])],
        # (jsonlean, 2026-11-23, mit-pdos/etcd-grove#24) encoding/json from its model
        # (models/encoding/json): the names the main tree's `Code/encoding/json.lean` declares
        # (project k8s-apiserver's, names only) are the model's
        std_models=["encoding/json"],
    ),
    Project(
        name="kv",
        # An example application on raft's Node: a replicated string-to-string key-value
        # store (Put, Get, Append; until 2026-10-19 the replicated string register
        # `examples/register`), with its randomized linearizability test over the lintest
        # driver and porcupine (check.go). A package of the examples' Go module (examples/go.mod),
        # which replaces go.etcd.io/raft/v3 by the revision pinned above
        # (`github.com/upamanyus/etcd/v3`, the fork's pseudo-version under a /v3 path, since
        # its go.mod declares go.etcd.io/raft/v3; GO_MOD_PINS checks the two agree), and lintest and
        # porcupine by this repository's copies.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "kv"),
        # (raft v3.7, stage R6b: the store reaches protobuf-go's `proto`, which the raft
        # tree translates into the root, `Code.google_golang_org.protobuf.proto`; lintest is
        # the lintest project's translation, porcupine the porcupine project's)
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=", "google.golang.org=",
                    "github.com/anishathalye/porcupine="],
        # the store; not its command (cmd/kvcheck), which only runs it
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kv")],
    ),
    Project(
        name="kvreconf",
        # The key-value store on raft that reconfigures and snapshots (`examples/raft/kvreconf`: every
        # choice the application may make is random; notes/raft-unified-plan.md, U11), with its
        # randomized linearizability test (check.go). A package of the examples' Go module, as kv.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "kvreconf"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=", "google.golang.org=",
                    "github.com/anishathalye/porcupine=", "github.com/mit-pdos/gokv="],
        # the store; not its command (cmd/kvreconfcheck), which only runs it; and gokv's
        # trusted_proph (examples/go.mod's gokv), whose ResolveBytes `Cluster.Read` resolves its
        # prophecy with (trusted: Code/github_com/mit_pdos/gokv/trusted_proph.toml)
        packages=[".", "github.com/mit-pdos/gokv/trusted_proph"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvreconf"),
               os.path.join("github_com", "mit_pdos", "gokv", "trusted_proph")],
        # the store alone into the part RaftNoAx too, over its raft (notes/raft-noax-part.md): the
        # kvdurable proofs the part copies use kvreconf's shared proofs, which name its translation
        parts=[Part(
            root="RaftNoAx",
            lean_roots=["github.com/mit-pdos/etcd-grove/examples/raft/kvreconf=RaftNoAx",
                        "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=RaftNoAx", "google.golang.org=",
                        "github.com/anishathalye/porcupine=", "github.com/mit-pdos/gokv="],
            packages=["."],
            owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvreconf")]),
            # and into the part KvNet (notes/kvnet-part.md), for the same reason: kvnet's store proofs
            # reuse kvdurablenoax's, which stand on kvreconf's shared proofs
            Part(
            root="KvNet",
            lean_roots=["github.com/mit-pdos/etcd-grove/examples/raft/kvreconf=KvNet",
                        "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=KvNet", "google.golang.org=",
                        "github.com/anishathalye/porcupine=", "github.com/mit-pdos/gokv="],
            packages=["."],
            owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvreconf")])],
    ),
    Project(
        name="durable",
        # A node's durable state, named files read and written whole (`examples/lib/durable`): the
        # Go side of the GooseLang extension durableExt (GooseLang/Ext/Durable), its functions
        # trusted (TrustedCode/github_com/mit_pdos/etcd_grove/examples/lib/durable.lean, which names
        # the extension; goose needs to know nothing of it). A package of the examples' Go
        # module (examples/go.mod).
        repo=None,
        rev=None,
        local=os.path.join("examples", "lib", "durable"),
        lean_roots=["github.com/mit-pdos/etcd-grove="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "durable")],
        # (2026-11-14, W4c U2: notes/wal-fsext-w4c-plan.md) translated with its bodies into the part
        # `WalTester/` too (until 2026-11-15 `LinuxFs/`), over the main tree's `os` (fsExt) and
        # `path/filepath`, where its specs are proved (no trusted function:
        # `WalTester/Code/.../examples/lib/durable.toml` absent); the main tree's stays trusted over
        # `durableExt` for kvdurable, kvfile and etcdstart (notes/wal-lean-integration.md)
        parts=[Part(
            root="WalTester",
            lean_roots=["github.com/mit-pdos/etcd-grove/examples/lib/durable=WalTester",
                        "github.com/mit-pdos/etcd-grove=", "os=", "syscall=", "golang.org/x/sys=",
                        "io/fs=", "internal/poll=", "internal/syscall=", "path/filepath=",
                        "internal/filepathlite="],
            packages=["."],
            owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "durable")]),
            # and the same into the part KvNet (notes/kvnet-part.md): kvnet's store writes its files
            # through the bodied `durable`, over fsExt
            Part(
            root="KvNet",
            lean_roots=["github.com/mit-pdos/etcd-grove/examples/lib/durable=KvNet",
                        "github.com/mit-pdos/etcd-grove=", "os=", "syscall=", "golang.org/x/sys=",
                        "io/fs=", "internal/poll=", "internal/syscall=", "path/filepath=",
                        "internal/filepathlite="],
            packages=["."],
            owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "durable")])],
    ),
    Project(
        name="prophkv",
        # GetAny's logically atomic spec over a prophecy of its random choice (`examples/goose/prophkv`,
        # a port of Perennial's goose/testdata/examples/prophkv): the prophecy is a prophecy patch
        # (etc/proph-patches/prophkv/), the first one of this repository. A package of the
        # examples' Go module (examples/go.mod), importing only goose-lang/primitive.
        repo=None,
        rev=None,
        local=os.path.join("examples", "goose", "prophkv"),
        lean_roots=["github.com/mit-pdos/etcd-grove="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "goose", "prophkv")],
    ),
    Project(
        name="bboltfs",
        # minibolt and its programs (`examples/osfs/bboltfs`), the acceptance test of the Linux file
        # extension fsExt (GooseLang/Ext/Fs, notes/fs-semantics-v2.md). Its `os`, `syscall` and
        # `golang.org/x/sys/unix` are this repository's translations, not Perennial's (whose
        # `os.toml` trusts nothing): the constants and types minibolt needs, and the functions it
        # calls trusted, modeled by the extension's operations (TrustedCode/os.lean,
        # TrustedCode/syscall.lean, TrustedCode/golang_org/x/sys/unix.lean). A package of the
        # examples' Go module (examples/go.mod).
        repo=None,
        rev=None,
        local=os.path.join("examples", "osfs", "bboltfs"),
        # (`io/fs`, which Perennial does not translate: the types `os` names, `FileInfo`,
        # `FileMode` and `PathError`, the errors the models return)
        # (`internal/poll` and `internal/syscall/unix`, 2026-11-07: what `os`'s translated
        # initializer reads; Perennial's import its own `syscall`)
        lean_roots=["github.com/mit-pdos/etcd-grove=", "os=", "syscall=", "golang.org/x/sys=",
                    "io/fs=", "internal/poll=", "internal/syscall="],
        packages=[".", "os", "syscall", "golang.org/x/sys/unix", "io/fs", "internal/poll",
                  "internal/syscall/unix"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "osfs", "bboltfs"),
               "os", "syscall", os.path.join("golang_org", "x", "sys"), os.path.join("io", "fs"),
               os.path.join("internal", "poll"), os.path.join("internal", "syscall")],
    ),
    Project(
        name="crashlog",
        # the smallest crash-safe program over the Linux file extension (`examples/osfs/crashlog`): a
        # commit flag guarding 8 bytes of data, proved crash-safe end to end
        # (Proof/github_com/mit_pdos/etcd_grove/examples/osfs/crashlog/). Its `os` and `syscall` are
        # project bboltfs's translations (the same lean roots), which own them; only the package
        # itself is translated here. A package of the examples' Go module (examples/go.mod).
        repo=None,
        rev=None,
        local=os.path.join("examples", "osfs", "crashlog"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "os=", "syscall=", "golang.org/x/sys=",
                    "io/fs=", "internal/poll=", "internal/syscall="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "osfs", "crashlog")],
    ),
    Project(
        name="walfs",
        # the WAL's file-system calls (`examples/osfs/walfs`, notes/walfs-ext-plan.md): a segment
        # committed by rename (segdir.go), a directory made to appear by rename (dirswap.go), a
        # segment's own calls (seglog.go). Its `os`, `syscall` and `golang.org/x/sys/unix` are
        # project bboltfs's translations, as for crashlog. A package of the examples' Go module.
        repo=None,
        rev=None,
        local=os.path.join("examples", "osfs", "walfs"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "os=", "syscall=", "golang.org/x/sys=",
                    "io/fs="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "osfs", "walfs")],
    ),
    Project(
        name="net",
        # The net extension's `net` and the programs proved over it (`examples/net/`,
        # notes/net-tcp.md): this repository's translation of `net` (the interfaces; `conn`, `TCPConn`,
        # `TCPListener`, `OpError` and the functions the examples call trusted,
        # `Net/TrustedCode/net.lean`, over `netExt`, `GooseLang/Ext/Net`), and the examples'
        # packages. In the part `Net/` (configured by `Net/Code/**.toml`): the main tree's
        # `net` is names only, with the axioms etcd's server proofs use, so the part declares the
        # same names and nothing outside it imports it. A package of the examples' Go module.
        repo=None,
        rev=None,
        local=os.path.join("examples", "net"),
        root="Net",
        # (v3, 2026-11-14) `os`, `syscall`, `internal/poll`, `io/fs`, `internal/syscall` are the
        # main tree's, as every project's (`net`'s errors are their values: `*os.SyscallError`,
        # `poll.ErrNetClosing`, `poll.ErrDeadlineExceeded`).
        lean_roots=["github.com/mit-pdos/etcd-grove=Net", "net=Net", "os=", "syscall=",
                    "io/fs=", "internal/poll=", "internal/syscall="],
        packages=["net", "./wire", "./echo", "./framed", "./acceptloop", "./duplex", "./halfclose",
                  "./shutdown", "./preface",
                  # each node a command of its example, its own process (examples/net/README.md)
                  "./echo/cmd/server",
                  "./echo/cmd/client",
                  "./echo/cmd/junk",
                  "./framed/cmd/server",
                  "./framed/cmd/client",
                  "./framed/cmd/junk",
                  "./acceptloop/cmd/server",
                  "./acceptloop/cmd/client",
                  "./duplex/cmd/server",
                  "./duplex/cmd/client",
                  "./halfclose/cmd/server",
                  "./halfclose/cmd/client",
                  "./preface/cmd/server",
                  "./preface/cmd/client",
                  "./preface/cmd/junk",
                  "./shutdown/cmd/node"],
        owned=["net", os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "net")],
        # `net` alone into the part KvNet too (notes/kvnet-part.md): kvnet's transport and client
        # protocol are over the net extension
        parts=[Part(
            root="KvNet",
            lean_roots=["net=KvNet", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
            packages=["net"],
            owned=["net"])],
    ),
    Project(
        name="models",
        # Our trusted models of real libraries, shared by etcd's proofs and the dsverify kits
        # (models/README.md; notes/dsverify-net-port-plan.md, phase 5): the Go module `models.lab` in `models/`,
        # a module path that names neither (the part is exported to the kits, which must not see
        # this repository: notes/decisions.md, "Shared Go runtime under a neutral module path").
        # Now the codecs' helpers: `pbcodec` (protobuf's wire format) and `jsoncodec` (JSON's
        # syntax), which the codecs generated by models/protobuf/pbgen.py and models/json/jsongen.py call. Into the
        # part `Net/`, with its bodies (no trusted function).
        repo=None,
        rev=None,
        local="models",
        root="Net",
        lean_roots=["models.lab=Net"],
        packages=["./pbcodec", "./jsoncodec"],
        owned=["models_lab"],
    ),
    Project(
        name="remote",
        # Clients on machines of their own (notes/remote-port-plan.md; dsverify-lab's Remote, ported):
        # `examples/lib/remote` (a Go module of its own, beside lintest, whose RunC it drives) and its
        # instance `counter` with its four machines' commands. Into the part `Net/` (it calls `net`,
        # whose main-tree translation is names only), with lintest, lintest/counter and porcupine the
        # main tree's (the lintest and porcupine projects' translations).
        repo=None,
        rev=None,
        local=os.path.join("examples", "lib", "remote"),
        root="Net",
        lean_roots=["github.com/mit-pdos/etcd-grove/examples/lib/remote=Net",
                    "github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=", "internal/syscall="],
        packages=[".", "./counter", "./counter/cmd/orch", "./counter/cmd/client0",
                  "./counter/cmd/client1", "./counter/cmd/server"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "remote")],
    ),
    Project(
        name="models-net",
        # Our models of standard-library packages (models/README.md; notes/dsverify-net-port-plan.md,
        # phase 5.2): `net/rpc` and `net/http`, Go 1.27.3's source with the parts goose cannot take
        # or that are the hard core replaced (models/net/{rpc,http}, marked MODEL; the difference:
        # models/diff.py), translated from the models (std_models: a GOROOT of links,
        # models/goroot.py). Into the part `Net/` (`Net/Code/net/{rpc,http}.lean`, inside project
        # net's `net`, which leaves them to this project), with `net` the part's.
        repo=None,
        rev=None,
        local="models",
        root="Net",
        # (`bufio`: the main tree's translation, as for project etcd's part)
        # (`net/url`, `path`, `crypto/tls`: the main tree's names-only translations; `net/textproto` and the
        # vendored `httpguts`, which the model's server calls, names only here)
        lean_roots=["models.lab=Net", "net=Net", "os=", "syscall=", "io/fs=", "internal/poll=",
                    "internal/syscall=", "bufio=", "net/url=", "path=", "crypto/tls=", "vendor=Net",
                    "golang.org/x/net/http/httpguts=Net", "go/token=Net", "mime/multipart=Net"],
        # (`net/http/internal/ascii`: names only, what `readTransfer`'s `parseTransferEncoding` names;
        # `net/http/internal`: the toolchain's chunked writer with its bodies, phase 7 S5)
        packages=["net/rpc", "net/http", "net/textproto", "vendor/golang.org/x/net/http/httpguts",
                  "go/token", "mime/multipart", "net/http/internal/ascii", "net/http/internal"],
        owned=[os.path.join("net", "rpc"), os.path.join("net", "http"),
               os.path.join("net", "textproto"), os.path.join("mime", "multipart"),
               os.path.join("vendor", "golang_org", "x", "net", "http", "httpguts"),
               os.path.join("go", "token")],
        std_models=["net/rpc", "net/http"],
    ),
    Project(
        name="durablekv",
        # kv made durable (`examples/raft/kvfile`): each replica's raft state in a file of the
        # durable package, rewritten whole before the messages that depend on it are sent;
        # replicas crash and restart from their files, and clients retry an operation with the
        # same encoding, which takes effect once. A package of the examples' Go module
        # (examples/go.mod), with kv's imports and the durable package's.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "kvfile"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=", "google.golang.org=",
                    "github.com/anishathalye/porcupine="],
        # the store; not its command (cmd/durablekv), which only runs it
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvfile")],
    ),
    Project(
        name="kvdurable",
        # kvreconf made durable (`examples/raft/kvdurable`): kvreconf's store, its every application
        # choice at random, with each replica's raft storage in a file of the durable package
        # (written whole, before what raft needs durable is relied on; what it does not need,
        # written late or not at all), and replicas that crash and restart from their files. A
        # package of the examples' Go module, with kvreconf's imports (trusted_proph, translated
        # by kvreconf's project) and the durable package's.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "kvdurable"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=", "google.golang.org=",
                    "github.com/anishathalye/porcupine=", "github.com/mit-pdos/gokv="],
        # the store; not its command (cmd/kvdurablecheck), which only runs it
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvdurable")],
    ),
    Project(
        name="common",
        # The examples' shared start of etcd (`examples/lib/etcdstart`): a member's configuration and
        # server (one member's, `StartServer`; a cluster's, `NewMember`, `StartMember`), its gRPC
        # service on a listener (`Serve`), a client of one address (`NewClient`), each translated
        # and proved once. A package of the examples' Go module (examples/go.mod), as every example
        # but kvwitness. Its imports are the etcd project's translations (names reached through the
        # empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "lib", "etcdstart"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "etcdstart")],
    ),
    Project(
        name="cluster3",
        # The examples' three-member cluster under network partitions (`examples/lib/cluster3`;
        # until 2026-11-05 package partition's own, moved for the compactor's three-member example,
        # notes/k8s-compactor-plan.md K6): a member started and its gRPC service served
        # (`StartMember`), a bridge to its client address (`StartBridge`), the cluster
        # (`StartCluster`), a client of every bridge (`NewClient`), the partitioner and its steps. A
        # package of the examples' Go module (examples/go.mod); its imports are the etcd, common and
        # bridge projects' translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "lib", "cluster3"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "cluster3")],
    ),
    Project(
        name="putget",
        # The adequacy example of etcd's server and client (open-work item 9): one member
        # started in-process, a client's Put and Get of one key. A package of the examples' Go
        # module (examples/go.mod), which replaces etcd's modules by the etcd fork at the etcd pin
        # above and go.etcd.io/raft/v3 by the raft pin (pseudo-versions; GO_MOD_PINS checks them).
        # Its imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "putget"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "putget")],
    ),
    Project(
        name="putget-dist",
        # putget_safe's two programs (notes/putget-dist-plan.md): the member machine's
        # (`putget.Member`: etcdstart's StartServer and Serve) and the client machine's
        # (`putget.Client`: Put, Get, check), of
        # examples/etcd/dist (etcd_safe's directory, notes/etcd-dist-plan.md; its server and client
        # packages are stage D2's). A package of the examples' Go module (examples/go.mod), as putget.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "dist"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["./putget"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "dist")],
    ),
    Project(
        name="axiomcx-bboltnan",
        # A counterexample to the bbolt key-value axioms (notes/axiom-review/bbolt.md): a NaN
        # FillPercent makes Commit panic, which the axioms exclude. A package of the examples' Go
        # module; bbolt is the etcd project's names-only translation.
        repo=None,
        rev=None,
        local=os.path.join("examples", "axiomcx", "bboltnan"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/bbolt="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "axiomcx", "bboltnan")],
    ),
    Project(
        name="putgetc",
        # putget with the auto-compactor on (notes/m2-plan.md, M2's first result): one member
        # started in-process with the compactor in revision mode (common.StartCompactingServer),
        # a client's Put and Get of one key.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "compacted"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "compacted")],
    ),
    Project(
        name="compactkv",
        # putgetc under compaction pressure (the client's `kv.Compact`, 2026-11-01): rounds of a
        # client's Put, a Compact at the revision before it and a Get, on one member with the
        # auto-compactor on.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "compactwatch"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "compactwatch")],
    ),
    Project(
        name="leasekv",
        # the closed lease example (2026-11-02, notes/lease-ex-plan.md): one member started
        # in-process, a client, and its lease reads (`Leases`, `TimeToLive`), checked.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "lease"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "lease")],
    ),
    Project(
        name="leasegrant",
        # the closed lease-grant example (2026-11-02, notes/lease-grant-plan.md): one member
        # started in-process, a client, a lease granted (`Grant`), then listed (`Leases`), checked.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "leasegrant"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "leasegrant")],
    ),
    Project(
        name="leaseexpiry",
        # the closed lease-expiry example (2026-11-04, notes/lease-expiry-plan.md, Part E): one
        # member started in-process, a client, a lease of the shortest TTL granted (`Grant`), its
        # `TimeToLive` polled until not found, then listed (`Leases`), checked.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "leaseexpiry"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "leaseexpiry")],
    ),
    Project(
        name="leasecatchup",
        # the multi-member lease example (2026-11-06, notes/lease-mono3-plan.md, lease-mono3 step 1):
        # three members started in-process (cluster3) in the monotone lease mode, a lease granted
        # through member 3, member 3 cut off while fillers are granted through member 1 (the log
        # compacted), the links mended, and member 3's listing (`Leases`) checked to hold the
        # lease once it has caught up by a snapshot. A package of the examples' Go module.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "leasecatchup"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "leasecatchup")],
    ),
    Project(
        name="linkvtxn",
        # The lintest driver over etcd's KV API as its robustness tester drives it
        # (notes/linkv-txn-plan.md, stage D): one member started in-process and a client to it,
        # as in putget, and lintest.Run's clients doing gets, lists, puts, deletes and
        # transactions, checked by porcupine against
        # the robustness model's Go form (Model, the Lean TxnModel's). A package of the
        # examples' Go module (examples/go.mod; its tests' robustness model is etcd's tests/v3,
        # test-only); its imports are the etcd, lintest and porcupine projects'
        # translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "txnlin"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "txnlin")],
    ),
    Project(
        name="linkv3p",
        # linkvtxn's workload under network partitions (notes/partition-plan.md): three members
        # started in-process as in putget3, each serving its gRPC API, a client to each, a partitioner
        # goroutine cutting and mending links on `Main`'s schedule (etcd's `CutPeer`/`MendPeer`;
        # since 2026-11-05 the cluster3 project's),
        # and linkvtxn's workload (`Gen`, `Apply`, `Model`, imported; its own `Apply` picks the
        # member; linkv's until 2026-10-20, notes/linkv3p-txn-plan.md). A package of the
        # examples' Go module (examples/go.mod); its imports are the etcd,
        # linkvtxn, lintest and porcupine projects' translations (names reached through the empty
        # root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "partition"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "partition")],
    ),
    Project(
        name="mvccrand",
        # mvcc's randomized tester (notes/mvccrand.md): the watchable store over a real backend and
        # lessor with a post-lock hook, one writer, concurrent floored readers and a watch stream,
        # each result checked against the history. A package of the examples' Go module
        # (examples/go.mod); its imports are the etcd project's translations (names reached through
        # the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "mvccrand"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/Masterminds/semver=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=", "google.golang.org=",
                    "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "mvccrand")],
    ),
    Project(
        name="mvccfull",
        # mvcc's full tester (notes/mvccfull.md): two members over real backends and lessors,
        # one log with compactions, snapshot installs and restarts, concurrent readers, hash
        # checks and watch streams, every choice from primitive.RandomUint64. A package of the
        # examples' Go module (examples/go.mod); its imports are the etcd project's translations
        # (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "mvccfull"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/Masterminds/semver=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=", "google.golang.org=",
                    "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "mvccfull")],
    ),
    Project(
        name="watchkv",
        # The watch example: one member started in-process, as in putget, a prefix watch from
        # revision 1, writer goroutines putting random keys under the prefix, and a check of the
        # watched events against the writes. A package of the examples' Go module
        # (examples/go.mod); its imports are the etcd project's translations (names
        # reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "watch"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "watch")],
    ),
    Project(
        name="authkv",
        # The authentication example (notes/auth-plan.md, D-AU5): one member started in-process
        # with the simple token provider, auth set up and enabled through a client, four
        # principals (two users, no token, an invalid token) running a workload inside and outside
        # the one granted range, and checks that the server refused what the auth state does not
        # permit. A package of the examples' Go module (examples/go.mod); its imports are the
        # etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "auth"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "auth")],
    ),
    Project(
        name="auth3",
        # authkv with three members (notes/auth3-scope.md, A1): three members started in-process
        # with auth on, each serving its raft handler on its own peer listener, then authkv's run
        # (auth.Run) through the first, every client on it. A package of the examples' Go module
        # (examples/go.mod); its imports are the etcd project's translations (names reached
        # through the empty root) and examples/etcd/auth.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "auth3"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "auth3")],
    ),
    Project(
        name="cachekv",
        # watchkv with the watch read through etcd's cache: one member started in-process, as in
        # putget, a cache of the prefix over the client, a cache watch from revision 2, writer
        # goroutines putting random keys under the prefix, and watchkv's check. A package of
        # the examples' Go module (examples/go.mod); its
        # imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "cache"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "cache")],
    ),
    Project(
        name="putget3",
        # putget with three members (D21 stage M5): three members started in-process, each
        # serving its raft handler on its own peer listener, a client's Put and Get through the
        # first. A package of the examples' Go module (examples/go.mod); its
        # imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "putget3"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "putget3")],
    ),
    Project(
        name="putgetN",
        # putget3 with any number of members (notes/clusterN-scope.md): Main(k) starts k members
        # in-process (etcdstart.Members, etcdstart.StartMembers), each serving its raft handler on
        # its own peer listener, a client's Put and Get through the first. A package of the
        # examples' Go module (examples/go.mod); its imports are the etcd project's translations
        # (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "putgetN"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "putgetN")],
    ),
    Project(
        name="authN",
        # auth3 with any number of members (notes/authN-plan.md): Main(k) starts k members
        # in-process with auth on (etcdstart.Members, etcdstart.StartMembersAuth), each serving its
        # raft handler on its own peer listener and its gRPC API, then authkv's set-up, barriers,
        # workloads and checks across them (run). A package of the examples' Go module
        # (examples/go.mod); its imports are the etcd project's translations (names reached
        # through the empty root) and examples/etcd/auth.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "authN"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "authN")],
    ),
    Project(
        name="authlease",
        # the lease rows of etcd's auth on authN's start (notes/auth-lease-s4-draft.md): Main(k)
        # starts k members in-process with auth on (etcdstart.StartMembersAuth), authkv's set-up,
        # barriers, the leases granted and attached by root and u, then the refusal checks and u's
        # revocation (run). A package of the examples' Go module (examples/go.mod); its imports are
        # the etcd project's translations (names reached through the empty root) and
        # examples/etcd/auth.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "authlease"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "authlease")],
    ),
    Project(
        name="leaseN",
        # the lease example with any number of members (notes/leaseN-plan.md): Main(k) starts k
        # members in-process (etcdstart.Members, etcdstart.StartMembers), each serving its raft
        # handler and its gRPC API, then the lease example's two reads at every member (run). A
        # package of the examples' Go module (examples/go.mod); its imports are the etcd
        # project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "leaseN"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "leaseN")],
    ),
    Project(
        name="leaseexpiryN",
        # the lease-expiry example with any number of members (notes/leaseN-plan.md): Main(k)
        # starts k members in-process (etcdstart.Members, etcdstart.StartMembers), each serving its
        # raft handler and its gRPC API, grants a lease through every member, and checks at every
        # member that the lease granted through it, once gone from its listing, stays gone (run).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "leaseexpiryN"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "leaseexpiryN")],
    ),
    Project(
        name="txnlinfaultsN",
        # linkv3p (examples/etcd/partition) with any number of members (notes/txnlinfaultsN-plan.md):
        # Main(k, clients, ops, sched) starts k members in-process (etcdstart.Members,
        # etcdstart.StartMembers), each serving its gRPC API (etcdstart.Serve) behind a bridge
        # (cluster3.StartBridge), k clients of every bridge, cluster3's partitioner on the schedule
        # and partition's Check (txnlin's workload). A package of the examples' Go module
        # (examples/go.mod); its imports are the etcd, partition, cluster3, lintest and porcupine
        # projects' translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "txnlinfaultsN"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "txnlinfaultsN")],
    ),
    Project(
        name="restart3",
        # The three-member restart example (restart3, notes/restart3-scope.md §4): in-process Puts
        # through member 1 before and while a follower is stopped (HardStop), the follower started
        # again on its data directory (the WAL replayed past a snapshot record, a merged snapshot
        # installed), its peer address served by the example's swap handler, and an in-process
        # Range at it checked exactly. A package of the examples' Go module (examples/go.mod); its
        # imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "restart"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "restart")],
    ),
    Project(
        name="restartN",
        # restart3 with any number of members (notes/restartN-plan.md): Run(k) starts k members
        # in-process (etcdstart.Members, StartMembers' steps with each peer address served through
        # the example's swap handler), in-process Puts through member 0 before and while a follower
        # is stopped (HardStop), the follower started again on its data directory (a merged snapshot
        # installed), and an in-process Range at it checked exactly. A package of the examples' Go
        # module (examples/go.mod); its imports are the etcd project's translations (names reached
        # through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "restartN"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "restartN")],
    ),
    Project(
        name="restart1",
        # The one-member restart example (restart S7, notes/restart-s7-scope.md): one member started
        # in-process, Puts of distinct keys through its own API, a graceful stop (HardStop) and a
        # start again on its data directory (the WAL replayed past a snapshot record), and a
        # Range through the restarted member's API checked exactly. A package of the examples' Go
        # module (examples/go.mod); its imports are the etcd project's translations (names reached
        # through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "restart1"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "restart1")],
    ),
    Project(
        name="etcd-all",
        # The program of the one closed etcd theorem, etcd_safe (notes/etcd-unified-scope.md):
        # package `.` of examples/etcd/all (a package of the examples' Go module, examples/go.mod),
        # eleven drivers at once in four parts (KV, Auth, Lease, Restart), with bodies. Everything
        # it names outside the package is the drivers' and the etcd project's translations (the
        # empty root): the drivers are not translated again.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "all"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "all")],
    ),
    Project(
        name="etcd-wal",
        # The WAL robustness tester (WAL W4c; `etcd_wal_safe`, notes/decisions.md "WAL W4c"): one
        # incarnation of a member's WAL per run (`Main`, rerun after every crash), checking each
        # restart's read against the crash-aware WAL spec, with its reference state in a durable
        # file (lib/durable). A package of the examples' Go module (examples/go.mod); its imports
        # are the etcd project's translations (`wal`, `walpb`, `fileutil` with bodies). Its crash
        # driver (`*_test.go`, `crashtest/`) is Go-only.
        repo=None,
        rev=None,
        local=os.path.join("examples", "etcd", "wal"),
        # (2026-11-14, W4c U1: notes/wal-fsext-w4c-plan.md) translated with its bodies (`purgeRound`
        # too) over the per-byte file extension's `os`, the WAL, `fileutil`, `walpb` (the main tree's)
        # and `lib/durable` with bodies, all in the part `WalTester/` (until 2026-11-15 `LinuxFs/`;
        # `WalTester/Code/.../examples/etcd/wal.toml` absent: every function translated): the main
        # tree's `lib/durable` is the trusted one (notes/wal-lean-integration.md). The absDisk
        # tester's main-tree translation retired with it (2026-11-15).
        root="WalTester",
        lean_roots=["github.com/mit-pdos/etcd-grove/examples/etcd/wal=WalTester",
                    "github.com/mit-pdos/etcd-grove/examples/lib/durable=WalTester",
                    "github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "os=", "syscall=", "golang.org/x/sys=",
                    "io/fs=", "internal/poll=", "internal/syscall=", "path/filepath=",
                    "internal/filepathlite="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "etcd", "wal")],
    ),
    Project(
        name="porcupine",
        # The linearizability checker of etcd's robustness tests (github.com/anishathalye/
        # porcupine v1.3.1, the version in etcd's tests/go.mod), vendored with the one change
        # that makes it translatable (third_party/porcupine/UPSTREAM.md).
        repo=None,
        rev=None,
        local=os.path.join("third_party", "porcupine"),
        lean_roots=["github.com/anishathalye/porcupine="],
        packages=["."],
        owned=[os.path.join("github_com", "anishathalye")],
    ),
    Project(
        name="porcupine-dag",
        # porcupine's open pull request #46 (practical-systems-iitd/porcupine 29a6b8e6c, "Support
        # system-specific consistency models via DAG-based execution"), vendored beside v1.3.1
        # with the one change that makes it translatable (third_party/porcupine-dag/UPSTREAM.md).
        # Translated into the parallel tree PorcupineDag (modules PorcupineDag.Code.github_com.
        # anishathalye.porcupine, ...), which nothing outside it imports: the same Go path as
        # project porcupine; configured by PorcupineDag/Code/**.toml.
        repo=None,
        rev=None,
        local=os.path.join("third_party", "porcupine-dag"),
        root="PorcupineDag",
        lean_roots=["github.com/anishathalye/porcupine=PorcupineDag"],
        packages=["."],
        owned=[os.path.join("github_com", "anishathalye")],
    ),
    Project(
        name="bridge",
        # etcd's integration tests' TCP bridge between a client and a member (tests/framework/
        # integration/bridge.go at the etcd pin), vendored with an exported constructor
        # (third_party/bridge/UPSTREAM.md): linkv3p's cuts between a client and its member
        # (notes/client-cut-plan.md). Its imports are standard library: io, sync (Perennial's)
        # and net (the etcd project's names, the empty root).
        repo=None,
        rev=None,
        local=os.path.join("third_party", "bridge"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "third_party")],
    ),
    Project(
        name="lintest",
        # A generic driver over porcupine: clients that run a linearizable library's
        # operations, traced as etcd's robustness tests trace them, then checked. A Go module of
        # its own (needing only porcupine), which the examples' module and kvwitness's replace by
        # this directory.
        repo=None,
        rev=None,
        local=os.path.join("examples", "lib", "lintest"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine="],
        # the driver, and instances of it: a counter under a mutex, its model; and the scalable-proof
        # experiment's log-applied register (logkv) and its variants, each adding one feature
        packages=[".", "./counter", "./logkv", "./logkvcompact", "./logkvsnap", "./logkvrw",
                  "./logkvappend",
                  # the driver with an apply told the client's id (examples/lib/remote's)
                  "./perclient"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lib", "lintest")],
    ),
    Project(
        name="raft-witness",
        # The witness experiment (notes/raft-witness.md; a candidate implementation of
        # etcd-io/raft#133, not merged upstream): branch raft-witness-goose-lean of the etcd
        # fork, etcd-io/raft#168 rebased onto raft37-goose-lean-a1 (project raft's pin) with
        # the fixes of notes/raft-witness-vs-pr168.md and the ConfState.Equivalent fix
        # at 3e3ed2d. Branch raft-witness-goose-lean-joint-progress computes the index
        # supported by both halves when they share a witness. Translated into RaftWitness
        # (modules RaftWitness.Code.go_etcd_io.raft.v3*, ...), which nothing outside it imports;
        # the same packages as project raft, configured by RaftWitness/Code/**.toml.
        repo="https://github.com/upamanyus/etcd",
        rev="13190826c05a3e8357e7a9041db70ab5a0644582",
        root="RaftWitness",
        # raft's `proto` import is the main tree's names-only `Code.google_golang_org.protobuf.proto`
        lean_roots=["go.etcd.io/raft/v3=RaftWitness", "google.golang.org=", "os=", "io/fs="],
        packages=[
            ".",
            "go.etcd.io/raft/v3/confchange",
            "go.etcd.io/raft/v3/quorum",
            "go.etcd.io/raft/v3/raftpb",
            "go.etcd.io/raft/v3/tracker",
        ],
        owned=[os.path.join("go_etcd_io", "raft")],
        counted_modules=["go.etcd.io/raft/v3"],
    ),
    Project(
        name="k8s-apiserver",
        # The survey of the Kubernetes API server's etcd3 storage backend
        # (notes/k8s-etcd3-goose.md): `k8s.io/apiserver/pkg/storage/etcd3` and
        # `k8s.io/apiserver/pkg/storage`, with bodies, over etcd's client (the etcd project's
        # translation, with `client/v3/kubernetes`). A Go module of this repository
        # (examples/k8s/etcd3) requiring k8s.io/apiserver at a master pseudo-version (2026-10-21)
        # and replacing etcd's modules by the etcd fork at the etcd pin; the API server's other
        # dependencies names only (their .toml). Also the driver itself (the package `.`,
        # notes/k8s-etcd3-plan.md phase 6), whose imports beyond the store are the etcd, lintest
        # and porcupine projects' translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "k8s", "etcd3"),
        lean_roots=["k8s.io=", "go.etcd.io/etcd=", "google.golang.org=", "go.uber.org=", "os=", "io/fs=",
                    "go.opentelemetry.io=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net", "encoding/json=", "encoding/base64=",
                    # (prove-authcrypto, 2026-11-21) base64's decoder's big-endian stores
                    # (Code/internal/byteorder.toml), with their bodies
                    "internal/byteorder=",
                    "path=", "github.com/mit-pdos/etcd-grove=",
                    "github.com/anishathalye/porcupine=",
                    # the etcd project's names-only translations, which client-go's workqueue
                    # and flowcontrol name (notes/k8s-clientgo-goose.md)
                    "golang.org/x/time=", "container/heap=", "github.com/go-logr=",
                    # pflag, names only: `FlagSet`, which featuregate's `MutableFeatureGate.AddFlag`
                    # names (so that goose translates the interface: the driver's noStreaming)
                    "github.com/spf13=",
                    # types only (the context sweep's fixes, 2026-11-13): runtime/trace's context
                    # key and `Task`, which `k8sctx.k8sCtxOk` names (Code/runtime/trace.toml)
                    "runtime/trace=",
                    # (k8s 7g) go-cmp, names only, which the driver's copy of Kubernetes'
                    # checker calls (its .toml); `maps` is Perennial's (2026-11-23)
                    "github.com/google="],
        packages=[
            ".",
            # (k8s 7g, notes/k8s-7g-scope.md §1.1) the driver's copy of Kubernetes' checker
            # (upstream plus etc/k8s-correctness/d30g.patch), with bodies (correctness.toml)
            "./correctness",
            "github.com/google/go-cmp/cmp",
            "k8s.io/apiserver/pkg/storage/etcd3",
            "k8s.io/apiserver/pkg/storage",
            # the watch cache's store, with bodies (notes/kep-6404-plan.md)
            "k8s.io/apiserver/pkg/storage/cacher",
            "k8s.io/apiserver/pkg/storage/cacher/store",
            "k8s.io/apiserver/pkg/storage/cacher/delegator",
            "k8s.io/apiserver/pkg/storage/cacher/metrics",
            "k8s.io/apiserver/pkg/storage/cacher/progress",
            "k8s.io/client-go/util/consistencydetector",
            "k8s.io/client-go/util/watchlist",
            "k8s.io/component-base/metrics",
            "k8s.io/apiserver/pkg/storage/cacher/consistency",
            "k8s.io/apiserver/pkg/storage/cacher/key",
            "k8s.io/client-go/tools/cache",
            # client-go's leaf libraries, with bodies (notes/k8s-clientgo-goose.md; the DaemonSet
            # controller, notes/k8s-daemonset-plan.md)
            "k8s.io/client-go/util/workqueue",
            "k8s.io/client-go/util/consistency",
            "k8s.io/apimachinery/pkg/util/sets",
            "k8s.io/apimachinery/pkg/util/resourceversion",
            "k8s.io/client-go/util/flowcontrol",
            "k8s.io/client-go/util/retry",
            "k8s.io/client-go/features",
            "k8s.io/client-go/listers",
            "k8s.io/client-go/listers/apps/v1",
            "k8s.io/client-go/listers/core/v1",
            # the typed clients' interfaces the model API server implements (project
            # k8s-daemonset; notes/k8s-apimodel-goose.md), types and names only, and what their
            # methods name, names only
            "k8s.io/client-go/kubernetes",
            "k8s.io/client-go/kubernetes/typed/admissionregistration/v1",
            "k8s.io/client-go/kubernetes/typed/admissionregistration/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/admissionregistration/v1beta1",
            "k8s.io/client-go/kubernetes/typed/apiserverinternal/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/apps/v1",
            "k8s.io/client-go/kubernetes/typed/apps/v1beta1",
            "k8s.io/client-go/kubernetes/typed/apps/v1beta2",
            "k8s.io/client-go/kubernetes/typed/authentication/v1",
            "k8s.io/client-go/kubernetes/typed/authentication/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/authentication/v1beta1",
            "k8s.io/client-go/kubernetes/typed/authorization/v1",
            "k8s.io/client-go/kubernetes/typed/authorization/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/authorization/v1beta1",
            "k8s.io/client-go/kubernetes/typed/autoscaling/v1",
            "k8s.io/client-go/kubernetes/typed/autoscaling/v2",
            "k8s.io/client-go/kubernetes/typed/batch/v1",
            "k8s.io/client-go/kubernetes/typed/batch/v1beta1",
            "k8s.io/client-go/kubernetes/typed/certificates/v1",
            "k8s.io/client-go/kubernetes/typed/certificates/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/certificates/v1beta1",
            "k8s.io/client-go/kubernetes/typed/coordination/v1",
            "k8s.io/client-go/kubernetes/typed/coordination/v1alpha2",
            "k8s.io/client-go/kubernetes/typed/coordination/v1beta1",
            "k8s.io/client-go/kubernetes/typed/core/v1",
            "k8s.io/client-go/kubernetes/typed/discovery/v1",
            "k8s.io/client-go/kubernetes/typed/discovery/v1beta1",
            "k8s.io/client-go/kubernetes/typed/events/v1",
            "k8s.io/client-go/kubernetes/typed/events/v1beta1",
            "k8s.io/client-go/kubernetes/typed/extensions/v1beta1",
            "k8s.io/client-go/kubernetes/typed/flowcontrol/v1",
            "k8s.io/client-go/kubernetes/typed/flowcontrol/v1beta1",
            "k8s.io/client-go/kubernetes/typed/flowcontrol/v1beta2",
            "k8s.io/client-go/kubernetes/typed/flowcontrol/v1beta3",
            "k8s.io/client-go/kubernetes/typed/lifecycle/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/networking/v1",
            "k8s.io/client-go/kubernetes/typed/networking/v1beta1",
            "k8s.io/client-go/kubernetes/typed/node/v1",
            "k8s.io/client-go/kubernetes/typed/node/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/node/v1beta1",
            "k8s.io/client-go/kubernetes/typed/policy/v1",
            "k8s.io/client-go/kubernetes/typed/policy/v1beta1",
            "k8s.io/client-go/kubernetes/typed/rbac/v1",
            "k8s.io/client-go/kubernetes/typed/rbac/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/rbac/v1beta1",
            "k8s.io/client-go/kubernetes/typed/resource/v1",
            "k8s.io/client-go/kubernetes/typed/resource/v1alpha3",
            "k8s.io/client-go/kubernetes/typed/resource/v1beta1",
            "k8s.io/client-go/kubernetes/typed/resource/v1beta2",
            "k8s.io/client-go/kubernetes/typed/scheduling/v1",
            "k8s.io/client-go/kubernetes/typed/scheduling/v1alpha3",
            "k8s.io/client-go/kubernetes/typed/scheduling/v1beta1",
            "k8s.io/client-go/kubernetes/typed/storage/v1",
            "k8s.io/client-go/kubernetes/typed/storage/v1alpha1",
            "k8s.io/client-go/kubernetes/typed/storage/v1beta1",
            "k8s.io/client-go/kubernetes/typed/storagemigration/v1",
            "k8s.io/client-go/kubernetes/typed/storagemigration/v1beta1",
            "k8s.io/client-go/rest",
            "k8s.io/client-go/discovery",
            "k8s.io/client-go/applyconfigurations/core/v1",
            "k8s.io/client-go/applyconfigurations/apps/v1",
            "k8s.io/client-go/applyconfigurations/autoscaling/v1",
            "k8s.io/api/policy/v1",
            "k8s.io/api/policy/v1beta1",
            "k8s.io/api/authentication/v1",
            "k8s.io/api/autoscaling/v1",
            # types and names only (their .toml): what the two name
            "k8s.io/apimachinery/pkg/api/errors",
            "k8s.io/apimachinery/pkg/api/validate/content",
            "k8s.io/apimachinery/pkg/api/meta",
            "k8s.io/apimachinery/pkg/apis/meta/v1",
            "k8s.io/apimachinery/pkg/apis/meta/v1/unstructured",
            "k8s.io/apimachinery/pkg/conversion",
            "k8s.io/apimachinery/pkg/fields",
            "k8s.io/apimachinery/pkg/labels",
            "k8s.io/apimachinery/pkg/runtime",
            "k8s.io/apimachinery/pkg/runtime/schema",
            "k8s.io/apimachinery/pkg/sharding",
            "k8s.io/apimachinery/pkg/types",
            "k8s.io/apimachinery/pkg/util/errors",
            "k8s.io/apimachinery/pkg/util/runtime",
            "k8s.io/apimachinery/pkg/util/validation/field",
            "k8s.io/apimachinery/pkg/util/wait",
            "k8s.io/apimachinery/pkg/util/version",
            "k8s.io/apimachinery/pkg/util/naming",
            "k8s.io/apimachinery/pkg/util/intstr",
            "k8s.io/apimachinery/pkg/api/resource",
            # (the API types the listers return: concrete structs, notes/k8s-clientgo-goose.md)
            "k8s.io/api/apps/v1",
            "k8s.io/api/core/v1",
            "k8s.io/apimachinery/pkg/watch",
            "k8s.io/apiserver/pkg/audit",
            "k8s.io/apiserver/pkg/endpoints/request",
            "k8s.io/apiserver/pkg/features",
            "k8s.io/apiserver/pkg/storage/etcd3/metrics",
            "k8s.io/apiserver/pkg/storage/feature",
            "k8s.io/apiserver/pkg/storage/value",
            "k8s.io/apiserver/pkg/util/feature",
            "k8s.io/apiserver/pkg/util/flowcontrol",
            "k8s.io/component-base/tracing",
            "k8s.io/component-base/featuregate",
            # (pflag, names only: what featuregate's interfaces name, Code/github_com/spf13/pflag.toml)
            "github.com/spf13/pflag",
            "k8s.io/klog/v2",
            # (klog-leaves, 2026-11-23) types and constants only: what klog's `loggingT` names
            "k8s.io/klog/v2/internal/severity",
            # (logr: the target of klog's alias `Logger`, notes/k8s-clientgo-goose.md)
            "github.com/go-logr/logr",
            "k8s.io/utils/clock",
            "k8s.io/utils/trace",
            "encoding/json",
            "encoding/base64",
            "internal/byteorder",
            # types only (the context sweep's fixes, 2026-11-13): runtime/trace's context key
            "runtime/trace",
            # (`path` is the etcd project's, with the bodies rafthttp needs: `Code/path.toml`)
            # types and names only: what the DaemonSet controller and its example name beyond the
            # above (project k8s-daemonset translates the controller; notes/k8s-daemonset-goose.md),
            # here because this project owns their directories and translates them from the same
            # client-go, apimachinery and component-base (CLIENT_GO_PINS)
            "k8s.io/api/extensions/v1beta1",
            "k8s.io/apimachinery/pkg/api/equality",
            "k8s.io/apimachinery/pkg/selection",
            "k8s.io/apimachinery/pkg/util/json",
            "k8s.io/apimachinery/pkg/util/rand",
            "k8s.io/apimachinery/pkg/util/strategicpatch",
            "k8s.io/apimachinery/pkg/util/validation",
            "k8s.io/client-go/informers",
            "k8s.io/client-go/informers/apps",
            "k8s.io/client-go/informers/core",
            "k8s.io/client-go/informers/apps/v1",
            "k8s.io/client-go/informers/core/v1",
            "k8s.io/client-go/kubernetes/scheme",
            "k8s.io/client-go/tools/record",
            "k8s.io/component-base/metrics/legacyregistry",
            "k8s.io/component-base/zpages/features",
            "k8s.io/utils/dump",
            "k8s.io/utils/ptr",
            # the informer layer (phase 4 of notes/k8s-daemonset-plan.md;
            # notes/k8s-daemonset-goose.md, "The informers"): with bodies the factory's
            # interfaces, the reflector's pager, the shared informer's sync tracking and its
            # listeners' ring buffer (tools/cache itself and the typed informers above, with
            # bodies now); names only what they name beyond the above
            "k8s.io/client-go/informers/internalinterfaces",
            "k8s.io/client-go/tools/pager",
            "k8s.io/client-go/tools/cache/synctrack",
            "k8s.io/utils/buffer",
            "k8s.io/apimachinery/pkg/apis/meta/v1beta1",
            "k8s.io/apimachinery/pkg/apis/meta/internalversion",
            "k8s.io/apimachinery/pkg/util/net",
            "k8s.io/apimachinery/pkg/util/diff",
            "k8s.io/apimachinery/pkg/util/cache",
        ],
        # (of k8s.io/apiserver, the packages it translates: pkg/authorization and
        # pkg/authentication are project k8s-authz's, from the fork with conditional authorization)
        owned=[os.path.join("k8s_io", "apiserver", "pkg", d)
               for d in ("audit", "endpoints", "features", "storage", "util")] +
              [os.path.join("k8s_io", "apimachinery"),
               os.path.join("k8s_io", "api"),
               os.path.join("k8s_io", "client_go"),
               os.path.join("k8s_io", "klog"), os.path.join("k8s_io", "component_base"),
               os.path.join("k8s_io", "utils", "clock"), os.path.join("k8s_io", "utils", "trace"),
               os.path.join("k8s_io", "utils", "dump"), os.path.join("k8s_io", "utils", "ptr"),
               os.path.join("k8s_io", "utils", "buffer"),
               os.path.join("encoding", "json"),
               os.path.join("github_com", "go_logr"),
               os.path.join("github_com", "spf13"),
               os.path.join("encoding", "base64"), os.path.join("internal", "byteorder"),
               os.path.join("runtime", "trace"),
               os.path.join("github_com", "google"),
               os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "k8s", "etcd3")],
        counted_modules=["k8s.io/apiserver"],
        # (jsonlean, 2026-11-23, mit-pdos/etcd-grove#24) encoding/json from its model
        # (models/encoding/json): the names the main tree's `Code/encoding/json.lean` declares
        # (project k8s-apiserver's, names only) are the model's
        std_models=["encoding/json"],
    ),
    Project(
        name="k8s-daemonset",
        # The model API server of the DaemonSet controller's example (notes/k8s-daemonset-plan.md,
        # D50; notes/k8s-apimodel-goose.md): package `apimodel` of examples/k8s/daemonset, a Go
        # module of its own requiring client-go, apimachinery and k8s.io/api at the pins of
        # examples/k8s/etcd3/go.mod (CLIENT_GO_PINS checks they agree), with bodies. Everything it
        # names outside the package is project k8s-apiserver's translation (the empty root).
        # And (2026-10-27, notes/k8s-daemonset-goose.md) the theorem's program `dsmain.Main` and
        # the DaemonSet controller's closure from k8s.io/kubernetes 878cfa6c4cc7 (the module's
        # go.mod: k8s.io/kubernetes and the staging modules it needs, pinned by `replace`), with
        # bodies, and the k8s.io/kubernetes, component-helpers, controller-manager and
        # apiextensions-apiserver packages they name, names only; client-go, apimachinery,
        # component-base and the rest are project k8s-apiserver's (the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "k8s", "daemonset"),
        lean_roots=["k8s.io=", "github.com/mit-pdos/etcd-grove=", "hash=", "encoding/json=", "os=", "io/fs=",
                    "github.com/go-logr="],
        packages=[
            "./apimodel",
            "./dsmain",
            # with bodies (their .toml)
            "k8s.io/kubernetes/pkg/controller/daemon",
            "k8s.io/kubernetes/pkg/controller/daemon/util",
            "k8s.io/kubernetes/pkg/controller/daemon/metrics",
            "k8s.io/kubernetes/pkg/controller",
            "k8s.io/kubernetes/pkg/api/v1/pod",
            "k8s.io/kubernetes/pkg/apis/core/v1/helper",
            "k8s.io/kubernetes/pkg/util/labels",
            "k8s.io/kubernetes/pkg/util/hash",
            "k8s.io/kubernetes/pkg/features",
            "k8s.io/component-helpers/scheduling/corev1",
            "k8s.io/component-helpers/scheduling/corev1/nodeaffinity",
            # types and names only
            "k8s.io/kubernetes/pkg/apis/core/helper",
            "k8s.io/kubernetes/pkg/apis/core/install",
            "k8s.io/kubernetes/pkg/apis/core/validation",
            "k8s.io/kubernetes/pkg/util/taints",
            "k8s.io/apiextensions-apiserver/pkg/features",
            "k8s.io/controller-manager/pkg/features",
        ],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "k8s", "daemonset"),
               os.path.join("k8s_io", "kubernetes"), os.path.join("k8s_io", "component_helpers"),
               os.path.join("k8s_io", "apiextensions_apiserver"),
               os.path.join("k8s_io", "controller_manager")],
        # (jsonlean, 2026-11-23, mit-pdos/etcd-grove#24) encoding/json from its model
        # (models/encoding/json): the names the main tree's `Code/encoding/json.lean` declares
        # (project k8s-apiserver's, names only) are the model's
        std_models=["encoding/json"],
    ),
    Project(
        name="k8s-compactor",
        # Kubernetes' etcd compactor run as API servers run it (notes/k8s-compactor-plan.md, K3):
        # package `.` of examples/k8s/compactor, a Go module of its own (it requires
        # k8s.io/apiserver and k8s.io/utils at the pins of examples/k8s/etcd3/go.mod,
        # CLIENT_GO_PINS, and the etcd fork at the etcd pin, GO_MOD_PINS), with bodies.
        # Everything it names outside the package is the k8s-apiserver and etcd projects'
        # translations (the empty root): the compactor, the feature gate, k8s.io/utils/clock,
        # etcd's client, examples/lib/etcdstart.
        repo=None,
        rev=None,
        local=os.path.join("examples", "k8s", "compactor"),
        lean_roots=["k8s.io=", "go.etcd.io/etcd=", "github.com/mit-pdos/etcd-grove=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net", "os=", "io/fs="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "k8s", "compactor")],
    ),
    Project(
        name="k8s-authz",
        # Kubernetes' conditional authorization (KEP-5681): k8s.io/apiserver's authorizer package
        # (conditions, conditions maps, the union decision builder, partial evaluation) and union
        # authorizer, with bodies, from the fork github.com/luxas/kubernetes, branch
        # impl-conditional-authz-review (not merged upstream), resolved in the repository's go.work
        # (its staging modules: apimachinery at the fork's commit too, ~2026-11-03, while project
        # k8s-apiserver's apimachinery names are of examples/k8s/etcd3's pin, 2026-10-21). Names only:
        # k8s.io/apiserver/pkg/authentication/user (Code/k8s_io/apiserver/pkg/authentication/user.toml).
        # The rest it names (apimachinery's sets, errors, validation, field, fields, labels, runtime,
        # schema; net/http) is project k8s-apiserver's translation (the empty root). Its driver is
        # project k8s-authz-driver.
        repo="https://github.com/luxas/kubernetes",
        rev="c67a81026c8b193849a47fdc05398baeafdf55e4",
        lean_roots=["k8s.io=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net"],
        packages=[
            # with bodies
            "k8s.io/apiserver/pkg/authorization/authorizer",
            "k8s.io/apiserver/pkg/authorization/union",
            # types and names only
            "k8s.io/apiserver/pkg/authentication/user",
        ],
        owned=[os.path.join("k8s_io", "apiserver", "pkg", "authorization"),
               os.path.join("k8s_io", "apiserver", "pkg", "authentication")],
        counted_modules=["k8s.io/apiserver"],
    ),
    Project(
        name="k8s-authz-driver",
        # The driver of project k8s-authz's conditional authorization: package `.` of
        # examples/k8s/authz, a Go module of its own whose go.mod replaces k8s.io/apiserver and the
        # other staging modules by the fork's subdirectory modules at project k8s-authz's pin
        # (GO_MOD_PINS checks the two agree), with bodies: kube-apiserver's two-phase protocol over a
        # union of leaf authorizers that behave arbitrarily (math/rand, Perennial's). Everything it
        # names outside the package is project k8s-authz's and k8s-apiserver's (the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "k8s", "authz"),
        lean_roots=["k8s.io=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net", "github.com/mit-pdos/etcd-grove="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "k8s", "authz")],
    ),
    Project(
        name="k8s-all",
        # The program of the one closed Kubernetes theorem, k8s_safe (notes/k8s-unified-scope.md):
        # package `.` of examples/k8s/all, a Go module of its own requiring the two drivers' modules
        # (examples/k8s/etcd3, examples/k8s/compactor) by path and everything else at
        # examples/k8s/etcd3/go.mod's pins (CLIENT_GO_PINS, GO_MOD_PINS), with bodies. Everything it
        # names outside the package is the k8s-apiserver, k8s-compactor and etcd projects'
        # translations (the empty root): the drivers are not translated again.
        repo=None,
        rev=None,
        local=os.path.join("examples", "k8s", "all"),
        lean_roots=["k8s.io=", "go.etcd.io/etcd=", "github.com/mit-pdos/etcd-grove=",
                    "go.uber.org=", "google.golang.org=", "net/http=", "net/url=", "net/textproto=", "net/http/httptrace=", "net=Net", "os=", "io/fs="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "k8s", "all")],
    ),
    Project(
        name="kvwitness",
        # The key-value store example (project kv) on the witness raft (project raft-witness):
        # a cluster of two voters and an in-process witness (`StartClusterWitness`, `MainWitness`;
        # notes/raft-witness.md, "W4"). A Go module of its own (not the examples', whose raft is
        # project raft's), whose go.mod replaces go.etcd.io/raft/v3 by the fork at raft-witness's
        # pin (GO_MOD_PINS checks the two agree), and
        # lintest and porcupine by this repository's copies. Translated into RaftWitness, its
        # raft the raft-witness project's, lintest and porcupine the main tree's.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "kvwitness"),
        root="RaftWitness",
        lean_roots=["github.com/mit-pdos/etcd-grove/examples/raft/kvwitness=RaftWitness",
                    "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=RaftWitness",
                    "google.golang.org=", "github.com/anishathalye/porcupine="],
        # the store; not its command (cmd/kvcheck), which only runs it
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvwitness")],
    ),
    Project(
        name="raft-noax",
        # Raft without hand-written axioms (notes/raft-noax-part.md): raft whose `proto` calls are
        # replaced by hand-written raftpb functions, `fmt.Errorf` by `errors.New`, and stepLeader's
        # `DescribeConfChange` dropped, for a closed theorem of kvdurable whose trust base has no
        # axiom of this repository. Translated into the parallel tree RaftNoAx (modules
        # RaftNoAx.Code.go_etcd_io.raft.v3*, ...), which nothing outside it imports; the same packages
        # as project raft, configured by RaftNoAx/Code/**.toml. At the fork's branch
        # raft37-goose-lean-noax (`RAFT_NOAX_REV`, notes/raft-noax.md).
        repo="https://github.com/upamanyus/etcd",
        rev=RAFT_NOAX_REV,
        root="RaftNoAx",
        # raft's `proto` import is the main tree's names-only `Code.google_golang_org.protobuf.proto`
        lean_roots=["go.etcd.io/raft/v3=RaftNoAx", "google.golang.org=", "os=", "io/fs="],
        packages=[
            ".",
            "go.etcd.io/raft/v3/confchange",
            "go.etcd.io/raft/v3/quorum",
            "go.etcd.io/raft/v3/raftpb",
            "go.etcd.io/raft/v3/tracker",
        ],
        owned=[os.path.join("go_etcd_io", "raft")],
        counted_modules=["go.etcd.io/raft/v3"],
        # the same into the part KvNet (notes/kvnet-part.md), where kvnet's proof lives
        parts=[Part(
            root="KvNet",
            lean_roots=["go.etcd.io/raft/v3=KvNet", "google.golang.org=", "os=", "io/fs="],
            packages=[".", "go.etcd.io/raft/v3/confchange", "go.etcd.io/raft/v3/quorum",
                      "go.etcd.io/raft/v3/raftpb", "go.etcd.io/raft/v3/tracker"],
            owned=[os.path.join("go_etcd_io", "raft")])],
    ),
    Project(
        name="kvdurable-noax",
        # The durable key-value store (project kvdurable) on raft-noax's raft, for its closed theorem
        # without hand-written axioms (notes/raft-noax-part.md): `KVDURABLE_NOAX_DIR`, the Go package
        # `KVDURABLE_NOAX_PKG`, translated into RaftNoAx, its raft the raft-noax project's, lintest,
        # porcupine, durable and trusted_proph the main tree's (examples/raft/kvdurablenoax, a Go
        # module of its own whose go.mod replaces raft by `RAFT_NOAX_REV`, GO_MOD_PINS).
        repo=None,
        rev=None,
        local=KVDURABLE_NOAX_DIR,
        root="RaftNoAx",
        lean_roots=[f"{KVDURABLE_NOAX_PKG}=RaftNoAx",
                    "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=RaftNoAx", "google.golang.org=",
                    "github.com/anishathalye/porcupine=", "github.com/mit-pdos/gokv="],
        packages=["."],
        owned=[os.path.join(*KVDURABLE_NOAX_PKG.replace(".", "_").replace("-", "_").split("/"))],
    ),
    Project(
        name="kvnet",
        # The networked key-value store on the axiom-free raft (`examples/raft/kvnet`,
        # notes/kvnet-proof-plan.md): replicas exchange raft's messages over TCP (the net extension's
        # `net`), keep their state in files of the bodied `durable` (over fsExt), and serve clients;
        # kvcheck its linearizability checker over lintest. A Go module of its own, whose go.mod
        # replaces raft by `RAFT_NOAX_REV` (GO_MOD_PINS). Translated into the part KvNet
        # (notes/kvnet-part.md), whose raft, `net` and `durable` are the parts of projects
        # raft-noax, net and durable translated into it; lintest, porcupine and gokv's trusted_proph
        # (kvcheck's `read` resolves its prophecy with `ResolveBytes`) the main tree's.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "kvnet"),
        root="KvNet",
        lean_roots=["github.com/mit-pdos/etcd-grove/examples/raft/kvnet=KvNet",
                    "github.com/mit-pdos/etcd-grove/examples/lib/durable=KvNet",
                    "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=KvNet", "net=KvNet",
                    "google.golang.org=", "github.com/anishathalye/porcupine=",
                    "github.com/mit-pdos/gokv=", "os=", "syscall=",
                    "io/fs=", "internal/poll=", "internal/syscall=", "path/filepath=",
                    "internal/filepathlite="],
        # the store and its checker; not the commands (cmd/, driver/), which only run them
        packages=[".", "./kvcheck"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "kvnet")],
    ),
    Project(
        name="raft-tla",
        # Raft in its `with_tla` build (`state_trace.go`: the trace hooks with their bodies, the
        # `TraceLogger` interface with its `TraceEvent` method, the `Tracing*` types), for raft's
        # TLA+ trace validation (project tracecheck) and nothing else: every other project is on
        # project raft's translation, the build etcd ships (`state_trace_nop.go`). The same source
        # and pin as project raft, loaded with `-tags with_tla`; only raft's own package, into the
        # parallel tree RaftTla (module RaftTla.Code.go_etcd_io.raft.v3): its subpackages, whose
        # files have no build constraint, are the main tree's. RaftTla's specs and proofs of raft
        # are the main tree's, copied by etc/gen-raft-tla.py, but for the few files about the
        # trace hooks' bodies (notes/decisions.md, "One raft proof for both builds").
        repo="https://github.com/upamanyus/etcd",
        rev=RAFT_REV,
        root="RaftTla",
        lean_roots=["go.etcd.io/raft/v3=RaftTla", "go.etcd.io/raft/v3/confchange=",
                    "go.etcd.io/raft/v3/quorum=", "go.etcd.io/raft/v3/raftpb=",
                    "go.etcd.io/raft/v3/tracker=", "google.golang.org=", "os=", "io/fs="],
        packages=["."],
        owned=[os.path.join("go_etcd_io", "raft")],
        counted_modules=[],
        tags=["with_tla"],
    ),
    Project(
        name="tracecheck",
        # Raft's TLA+ trace validation, closed (notes/trace-validation-plan.md): the concurrent
        # harness of raft.Nodes with Main (package tracecheck), and the Go transcription of
        # etcdraft.tla and Traceetcdraft.tla its checker (package etcdraft; not its ndjson reader
        # nor its porcupine model, pmodel, which only cross-check). A Go module of its own, whose
        # go.mod replaces go.etcd.io/raft/v3 by the fork at project raft's pin (GO_MOD_PINS), loaded
        # in the `with_tla` build. The checker (package etcdraft, which does not import raft) is
        # translated into the main tree; the harness (package tracecheck) into RaftTla, on project
        # raft-tla's raft.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "tracecheck"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "google.golang.org=",
                    "github.com/anishathalye/porcupine="],
        packages=["./etcdraft"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "tracecheck",
                            "etcdraft")],
        parts=[Part(
            root="RaftTla",
            lean_roots=["github.com/mit-pdos/etcd-grove/examples/raft/tracecheck=RaftTla",
                        "github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft=",
                        "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=RaftTla",
                        "go.etcd.io/raft/v3/confchange=", "go.etcd.io/raft/v3/quorum=",
                        "go.etcd.io/raft/v3/raftpb=", "go.etcd.io/raft/v3/tracker=",
                        "google.golang.org=", "github.com/anishathalye/porcupine="],
            packages=["."],
            owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft",
                                "tracecheck")])],
        tags=["with_tla"],
    ),
    Project(
        name="antithesis",
        # Raft against Antithesis's TLA+ model (mit-pdos/etcd-grove#33,
        # notes/antithesis-check-design.md): the harness of three RawNodes with Main (package
        # antithesis) and the Go transcription of EtcdRaft.tla and EtcdBinding.tla its checker
        # (package check; not its NDJSON reader, check/ndjson, its command, check/cmd, or the
        # verdict wrapper, check/verdict.go, `!goose`, which only cross-check against TLC). A Go
        # module of its own, whose go.mod replaces go.etcd.io/raft/v3 by the fork at project raft's
        # pin (GO_MOD_PINS), in raft's main build (no tags): both packages translate into the main
        # tree, on project raft's raft.
        repo=None,
        rev=None,
        local=os.path.join("examples", "raft", "antithesis"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=", "google.golang.org="],
        packages=[".", "./check"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "raft", "antithesis")],
    ),
    Project(
        name="bbolt-bank",
        # (Named `bbolt` until 2026-11-05, when the main tree's bbolt (project `bbolt`, the fork's
        # goose-lean-v2) got bodies; the bank test moves onto it in the clean-up after the merge.)
        # bbolt with its bodies, for the top-level test bbolttest: the fork upamanyus/bbolt, branch
        # goose-lean-bank-init-image (first-write recovery on goose-lean, v1.5.0 with the `unsafe` forms of Perennial's byte memory, crash-safe init,
        # the fix of etcd-io/bbolt#1311). Translated into the parallel tree Bbolt (modules
        # Bbolt.Code.go_etcd_io.bbolt*, ...), since project etcd translates go.etcd.io/bbolt (names
        # only) into the main tree; nothing outside Bbolt imports it. Its `os`, `syscall`,
        # `golang.org/x/sys/unix` and `io/fs` are project bboltfs's (the Linux file extension), its
        # `hash/fnv` and `encoding/hex` project etcd's; the rest of the standard library Perennial's.
        repo="https://github.com/upamanyus/bbolt",
        rev="2e1663644f604d5a2c4f040bc744e047cde8fd8e",
        root="Bbolt",
        lean_roots=["go.etcd.io/bbolt=Bbolt", "os=", "syscall=", "golang.org/x/sys=", "io/fs=",
                    "hash=", "encoding/hex="],
        # the database; not its tests, tools (cmd/) or test helpers (internal/btesting, ...)
        packages=[".", "./errors", "./internal/common", "./internal/freelist"],
        owned=[os.path.join("go_etcd_io", "bbolt")],
        counted_modules=["go.etcd.io/bbolt"],
    ),    Project(
        name="bbolttest",
        # The top-level test of bbolt (`examples/bbolt/bank`): a bank whose boot program checks, after
        # any crash, that the balances add up and that every acknowledged transfer survived (against
        # a witness file), then runs concurrent transactions through the lintest driver, whose
        # trace porcupine checks for strict serializability. A Go module of its own, whose go.mod
        # replaces go.etcd.io/bbolt by the fork at project bbolt-bank's pin (GO_MOD_PINS checks the two
        # agree), and lintest and porcupine by this repository's copies. Translated into Bbolt, its
        # bbolt project bbolt-bank's, its file calls project bboltfs's, lintest and porcupine the main
        # tree's.
        repo=None,
        rev=None,
        local=os.path.join("examples", "bbolt", "bank"),
        root="Bbolt",
        lean_roots=["github.com/mit-pdos/etcd-grove/examples/bbolt/bank=Bbolt",
                    "go.etcd.io/bbolt=Bbolt", "github.com/mit-pdos/etcd-grove=",
                    "github.com/anishathalye/porcupine=", "os=", "syscall=", "golang.org/x/sys=",
                    "io/fs=", "hash=", "encoding/hex="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "bbolt", "bank")],
    ),
]


# The dsverify kits (notes/dsv-paxos.md; etc/dsv/README.md): each kit's project is the `GOOSE` dict
# of its own file `etc/dsv/<kit>.py` (the fields of `Project`), so that a kit adds a file instead of
# editing this one. Placed before project models-net, in the files' order.
def dsv_kits():
    """The kit files `etc/dsv/*.py`, loaded, in name order (also read by etc/gen-init.py)."""
    import importlib.util
    d = os.path.join(ROOT, "etc", "dsv")
    out = []
    for f in sorted(os.listdir(d)) if os.path.isdir(d) else []:
        if not f.endswith(".py") or f.startswith("_") or f == "kitgen.py":  # (the generator)
            continue
        spec = importlib.util.spec_from_file_location("dsv_kit_" + f[:-3], os.path.join(d, f))
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        m.KIT = f[:-3]
        out.append(m)
    return out


DSV_KITS = dsv_kits()
_i = next(i for i, p in enumerate(PROJECTS) if p.name == "models-net")
PROJECTS[_i:_i] = [Project(**k.GOOSE) for k in DSV_KITS if hasattr(k, "GOOSE")]



# The Go modules of this repository that build the examples against the forks, and which project's
# pinned `rev` each replaced Go path must be at (a replace's pseudo-version names the commit): the
# examples' module, kvwitness's, whose raft is the witness experiment's, and k8setcd3's. `--check` fails on a
# mismatch, so that a fork-pin bump cannot leave the examples on the old code.
GO_MOD_PINS = {
    os.path.join("examples", "go.mod"): {"go.etcd.io/etcd/": "etcd", "go.etcd.io/raft/v3": "raft",
                                         "go.etcd.io/bbolt": "bbolt"},
    os.path.join("examples", "raft", "kvwitness", "go.mod"): {"go.etcd.io/raft/v3": "raft-witness"},
    os.path.join("examples", "raft", "kvdurablenoax", "go.mod"): {"go.etcd.io/raft/v3": "raft-noax"},
    os.path.join("examples", "raft", "kvnet", "go.mod"): {"go.etcd.io/raft/v3": "raft-noax"},
    os.path.join("examples", "raft", "tracecheck", "go.mod"): {"go.etcd.io/raft/v3": "raft"},
    os.path.join("examples", "raft", "antithesis", "go.mod"): {"go.etcd.io/raft/v3": "raft"},
    os.path.join("examples", "bbolt", "bank", "go.mod"): {"go.etcd.io/bbolt": "bbolt-bank"},
    # the Kubernetes etcd3 store's driver, a module of its own (it requires k8s.io/apiserver)
    os.path.join("examples", "k8s", "etcd3", "go.mod"): {"go.etcd.io/etcd/": "etcd", "go.etcd.io/raft/v3": "raft"},
    # Kubernetes' compactor's example, a module of its own (it requires k8s.io/apiserver)
    os.path.join("examples", "k8s", "compactor", "go.mod"): {"go.etcd.io/etcd/": "etcd", "go.etcd.io/raft/v3": "raft"},
    # conditional authorization's driver: the Kubernetes staging modules, from the fork
    os.path.join("examples", "k8s", "authz", "go.mod"): {"k8s.io/": "k8s-authz"},
    # the one closed Kubernetes theorem's program, a module of its own (it requires both drivers')
    os.path.join("examples", "k8s", "all", "go.mod"): {"go.etcd.io/etcd/": "etcd", "go.etcd.io/raft/v3": "raft"},
    # k8s_safe's program as a distributed deployment (notes/k8s-dist.md), a module of its own (it
    # requires the drivers' modules and etcd-dist's members, with examples/go.mod's bbolt)
    os.path.join("examples", "k8s", "dist", "go.mod"): {"go.etcd.io/etcd/": "etcd", "go.etcd.io/raft/v3": "raft",
                                                         "go.etcd.io/bbolt": "bbolt"},
}


# Go modules of this repository whose Kubernetes requirements must be those of another: the model
# API server's and the DaemonSet controller's module (project k8s-daemonset) names the types,
# interfaces and functions project k8s-apiserver translates from examples/k8s/etcd3's module, so
# both must be at the same versions (examples/k8s/daemonset/go.mod pins the staging ones by
# `replace`).
CLIENT_GO_PINS = {
    os.path.join("examples", "k8s", "daemonset", "go.mod"): (
        os.path.join("examples", "k8s", "etcd3", "go.mod"),
        ["k8s.io/api", "k8s.io/apimachinery", "k8s.io/client-go", "k8s.io/apiserver",
         "k8s.io/component-base", "k8s.io/klog/v2", "k8s.io/utils", "k8s.io/kube-openapi"]),
    os.path.join("examples", "k8s", "compactor", "go.mod"): (
        os.path.join("examples", "k8s", "etcd3", "go.mod"),
        ["k8s.io/api", "k8s.io/apimachinery", "k8s.io/client-go", "k8s.io/apiserver",
         "k8s.io/component-base", "k8s.io/klog/v2", "k8s.io/utils", "k8s.io/kube-openapi"]),
    os.path.join("examples", "k8s", "all", "go.mod"): (
        os.path.join("examples", "k8s", "etcd3", "go.mod"),
        ["k8s.io/api", "k8s.io/apimachinery", "k8s.io/client-go", "k8s.io/apiserver",
         "k8s.io/component-base", "k8s.io/klog/v2", "k8s.io/utils", "k8s.io/kube-openapi"]),    os.path.join("examples", "k8s", "dist", "go.mod"): (
        os.path.join("examples", "k8s", "etcd3", "go.mod"),
        ["k8s.io/api", "k8s.io/apimachinery", "k8s.io/client-go", "k8s.io/apiserver",
         "k8s.io/component-base", "k8s.io/klog/v2", "k8s.io/utils", "k8s.io/kube-openapi"]),
}


def go_mod_requires(f):
    """The versions a go.mod file selects, by module path: its requirements, except that a module
    replaced by the same path at a version (`M => M vX`, as examples/k8s/daemonset/go.mod replaces
    the staging modules k8s.io/kubernetes requires at v0.0.0) is at the replacement's version, and
    one replaced by another path (a fork: `k8s.io/apimachinery => github.com/upamanyus/kubernetes/
    staging/src/k8s.io/apimachinery vX`, real fmt stage 1, 2026-11-24) is `NEW@vX`."""
    text = open(os.path.join(ROOT, f), encoding="utf-8").read()
    reqs = dict(re.findall(r"^\s*(?:require\s+)?(\S+)\s+(v\S+)(?:\s*//.*)?$", text, re.M))
    for old, new, ver in re.findall(r"^\s*(?:replace\s+)?(\S+)\s+=>\s+(\S+)\s+(v\S+)\s*$", text, re.M):
        reqs[old] = ver if old == new else f"{new}@{ver}"
    return reqs


def go_mod_pin_errors():
    """The replaces of GO_MOD_PINS's go.mod files not at their project's pinned revision, and the
    requirements of CLIENT_GO_PINS's that differ from their reference's."""
    revs = {p.name: p.rev for p in PROJECTS}
    errors = []
    for f, (ref, mods) in CLIENT_GO_PINS.items():
        have, want = go_mod_requires(f), go_mod_requires(ref)
        for m in mods:
            if have.get(m) is None or have.get(m) != want.get(m):
                errors.append(f"{f}: {m} {have.get(m)} is not {ref}'s {want.get(m)}")
    for f, pins in GO_MOD_PINS.items():
        text = open(os.path.join(ROOT, f), encoding="utf-8").read()
        found = set()
        # `OLD => NEW VERSION`, in a replace block or a one-line replace
        for old, new, ver in re.findall(r"^\s*(?:replace\s+)?(\S+)(?:\s+\S+)?\s+=>\s+(\S+)\s+(\S+)\s*$",
                                        text, re.M):
            proj = next((pn for prefix, pn in pins.items() if old.startswith(prefix)), None)
            if proj is None:
                continue
            found.add(proj)
            m = re.search(r"-([0-9a-f]{12})$", ver)
            if not m or not revs[proj].startswith(m.group(1)):
                errors.append(f"{f}: {old} => {new} {ver} is not project {proj}'s pinned "
                              f"revision {revs[proj][:12]} (etc/goose.py)")
        for proj in sorted(set(pins.values()) - found):
            errors.append(f"{f}: no replace of {proj}'s Go paths "
                          f"({', '.join(k for k, v in pins.items() if v == proj)})")
    return errors


def run(args, cwd=None, quiet=False, env=None):
    if not quiet:
        print("+ " + " ".join(args), file=sys.stderr)
    subprocess.run(args, cwd=cwd, check=True, env=env)


def host_env():
    """The environment without the target settings (`GOOS`, `GOARCH`, `CGO_ENABLED`, `CC`), for
    building the translator to run on this machine: those settings, when given, are for the
    translation only (the standard library's cgo-processed packages, e.g. `net`, translate
    differently per target; the checked-in translations are linux/amd64's, which `main` makes the
    default target: `GOOS=linux GOARCH=amd64 CGO_ENABLED=1`, and on a host that is not amd64
    `CC=x86_64-linux-gnu-gcc`)."""
    target = {"GOOS", "GOARCH", "CGO_ENABLED", "CC"}
    return {k: v for k, v in os.environ.items() if k not in target}


def git_head(d):
    r = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def git_dirty(d):
    r = subprocess.run(["git", "-C", d, "status", "--porcelain", "--untracked-files=no"],
                       capture_output=True, text=True, check=True)
    return r.stdout.strip() != ""


def checkout(url, rev, d):
    """A checkout of `url` at `rev` in `d` (cloned or fetched as needed)."""
    if git_head(d) == rev:
        return d
    if not os.path.isdir(os.path.join(d, ".git")):
        os.makedirs(d, exist_ok=True)
        run(["git", "init", "-q", d])
        run(["git", "-C", d, "remote", "add", "origin", url])
    try:
        run(["git", "-C", d, "fetch", "-q", "--depth", "1", "origin", rev])
    except subprocess.CalledProcessError:
        sys.exit(f"goose.py: cannot fetch {rev} from {url}; if it is not pushed yet, "
                 f"name a local checkout with --src or ${{NAME}}_SRC")
    run(["git", "-C", d, "checkout", "-q", "--detach", "FETCH_HEAD"])
    if git_head(d) != rev:
        sys.exit(f"goose.py: {url} at {rev}: checked out {git_head(d)} instead")
    return d


def pinned_perennial():
    manifest = json.load(open(os.path.join(ROOT, "lake-manifest.json")))
    (p,) = [p for p in manifest["packages"] if p["name"] == "perennial"]
    lake_dir = os.path.join(ROOT, ".lake", "packages", "perennial")
    if git_head(lake_dir) == p["rev"]:
        return lake_dir, p["rev"]
    return checkout(p["url"], p["rev"], os.path.join(WORK, "perennial")), p["rev"]


def lean_files(d, owned, others=()):
    """The `.lean` files under `d/{Code,GeneratedProof}/` at the paths `owned`, but for those at
    the paths `others` (owned by another translation into the same module root: `net/rpc` of
    project models-net inside project net's `net`)."""
    out = {}
    for sub in ("Code", "GeneratedProof"):
        skip = {os.path.join(d, sub, x) for x in others}
        for o in owned:
            base = os.path.join(d, sub, o)
            paths = [base + ".lean"] if os.path.isfile(base + ".lean") else []
            for dp, _, fs in os.walk(base):
                paths.extend(os.path.join(dp, f) for f in fs if f.endswith(".lean"))
            for path in paths:
                if any(path == x + ".lean" or path.startswith(x + os.sep) for x in skip):
                    continue
                out[os.path.relpath(path, d)] = open(path, encoding="utf-8").read()
    return out


def others_owned(root, owned):
    """The paths other translations into module root `root` own below one of `owned`."""
    out = []
    for p in PROJECTS:
        for r, _, _, o2 in pieces(p):
            if r != root:
                continue
            out.extend(x for x in o2 if x not in owned
                       and any(x.startswith(o + os.sep) for o in owned))
    return out


def std_models_env(proj):
    """The environment goose runs in: for a project with std_models, a GOROOT of links whose
    modelled packages' Go files are the models' (models/goroot.py), made afresh."""
    if not proj.std_models:
        return None
    sys.path.insert(0, os.path.join(ROOT, "models"))
    import goroot
    farm = goroot.make_farm(os.path.join(WORK, "goroot-" + proj.name), proj.std_models)
    return dict(os.environ, GOROOT=farm, GOTOOLCHAIN="local",
                PATH=os.path.join(farm, "bin") + os.pathsep + os.environ.get("PATH", ""))


# The module the generated model files import (`models.lab/jsoncodec`, `models.lab/pbcodec`):
# Project.jsonmodel_roots (and #37's pbmodel_roots).
MODEL_MODULE = ("models.lab", "models")


def model_files_roots(proj):
    """Whether the project has model files over its real packages (`model_overlay`)."""
    return bool(proj.jsonmodel_roots)


def module_models_env(proj, src, env, tmp):
    """`env` with the project's module models put in place (Project.module_models): a copy of
    `src`'s go.work (its paths made absolute) or go.mod, in `tmp`, with a `replace` of each modelled
    module by its model, named by GOWORK or GOFLAGS' -modfile; and, for a project with model files
    (`model_files_roots`), models.lab added (a `use` of models/ in a workspace, else a `require` and
    `replace`). `env` itself if there are none."""
    if not proj.module_models and not model_files_roots(proj):
        return env
    env = dict(os.environ if env is None else env)
    reps = {m: os.path.join(ROOT, d) for m, d in sorted((proj.module_models or {}).items())}
    uses = [os.path.join(ROOT, MODEL_MODULE[1])] if model_files_roots(proj) else []
    if os.path.exists(os.path.join(src, "go.work")):
        j = json.loads(subprocess.run(["go", "work", "edit", "-json", "go.work"], cwd=src,
                                      check=True, capture_output=True, text=True).stdout)
        lines = ["go " + j["Go"]] + (["toolchain " + j["Toolchain"]] if j.get("Toolchain") else [])
        lines += ["use ("] + ["\t" + os.path.normpath(os.path.join(src, u["DiskPath"]))
                              for u in j["Use"]] + ["\t" + u for u in uses] + [")"]
        for r in j.get("Replace") or []:
            if r["Old"]["Path"] in reps:
                continue
            new = r["New"]["Path"]
            if not r["New"].get("Version") and new.startswith("."):
                new = os.path.normpath(os.path.join(src, new))
            old = r["Old"]["Path"] + (" " + r["Old"]["Version"] if r["Old"].get("Version") else "")
            lines.append(f"replace {old} => {new}" +
                         (" " + r["New"]["Version"] if r["New"].get("Version") else ""))
        lines += [f"replace {m} => {d}" for m, d in reps.items()]
        work = os.path.join(tmp, "go.work")
        with open(work, "w") as f:
            f.write("\n".join(lines) + "\n")
        if os.path.exists(os.path.join(src, "go.work.sum")):
            shutil.copyfile(os.path.join(src, "go.work.sum"), work + ".sum")
        env["GOWORK"] = work
        return env
    modfile = os.path.join(tmp, "go.mod")
    shutil.copyfile(os.path.join(src, "go.mod"), modfile)
    if os.path.exists(os.path.join(src, "go.sum")):
        shutil.copyfile(os.path.join(src, "go.sum"), os.path.join(tmp, "go.sum"))
    j = json.loads(subprocess.run(["go", "mod", "edit", "-json", modfile], check=True,
                                  capture_output=True, text=True).stdout)
    edits = []
    for r in j.get("Replace") or []:
        new = r["New"]["Path"]
        if not r["New"].get("Version") and new.startswith(".") and r["Old"]["Path"] not in reps:
            old = r["Old"]["Path"] + ("@" + r["Old"]["Version"] if r["Old"].get("Version") else "")
            edits.append(f"-replace={old}={os.path.normpath(os.path.join(src, new))}")
    edits += [f"-replace={m}={d}" for m, d in reps.items()]
    if uses:
        edits += [f"-require={MODEL_MODULE[0]}@v0.0.0-00010101000000-000000000000",
                  f"-replace={MODEL_MODULE[0]}={uses[0]}"]
    subprocess.run(["go", "mod", "edit"] + edits + [modfile], check=True)
    env["GOFLAGS"] = (env.get("GOFLAGS", "") + " -modfile=" + modfile).strip()
    return env


def jsonmodel_entries(proj, src, env, tmp):
    """Project.jsonmodel_roots: {path in `src`: generated file in `tmp`}, jsongen's same-package
    `json_model_gen.go` of each package of the roots."""
    if not proj.jsonmodel_roots:
        return {}
    sys.path.insert(0, os.path.join(ROOT, "models", "json"))
    import jsongen
    header = (f"// Code generated by jsongen.py (etc/goose.py, project {proj.name}). DO NOT EDIT.\n\n")
    # the dump (reflection) runs on the toolchain's own standard library, not the models' (std_models:
    # the encoding/json model's MarshalIndent is not modelled); the workspace with models.lab
    dtmp = os.path.join(tmp, "jsonmodel-env")
    os.makedirs(dtmp, exist_ok=True)
    denv = module_models_env(proj, src, None, dtmp)
    try:
        out = jsongen.pkgmodel_files(proj.jsonmodel_roots, src, header, denv, test=False)
    except jsongen.InputError as e:
        sys.exit(f"goose.py: {proj.name}: jsongen (same-package mode) failed: {e}")
    except jsongen.jsongen_core.JsonRefused as e:
        sys.exit(f"goose.py: {proj.name}: jsongen refused: {e.reasons}")
    rep = {}
    for home, (pdir, fs) in sorted(out.items()):
        for f, c in fs.items():
            target = os.path.join(pdir, f)
            if os.path.exists(target):
                sys.exit(f"goose.py: {proj.name}: {target} exists in the source (the model files are "
                         "the overlay's only)")
            o = os.path.join(tmp, "jsonmodel", home.replace("/", "_"), f)
            os.makedirs(os.path.dirname(o), exist_ok=True)
            with open(o, "w") as fh:
                fh.write(c)
            rep[target] = o
    return rep


# The generators of model files over real packages, merged into the project's one -overlay
# (`model_overlay`): jsongen's same-package methods here, #37's pbgen pbmodel methods beside them.
MODEL_FILE_GENERATORS = [jsonmodel_entries]


def model_overlay(proj, src, env, tmp):
    """The project's overlay file (goose's and proofgen's `-overlay`, `go build -overlay`'s JSON):
    every model file over its real packages (MODEL_FILE_GENERATORS), merged into one; None if
    there are none. Two generators writing one path is an error."""
    rep = {}
    for gen in MODEL_FILE_GENERATORS:
        for target, f in gen(proj, src, env, tmp).items():
            if target in rep:
                sys.exit(f"goose.py: {proj.name}: two model files at {target}")
            rep[target] = f
    if not rep:
        return None
    overlay = os.path.join(tmp, "model-overlay.json")
    with open(overlay, "w") as f:
        json.dump({"Replace": rep}, f, indent=1, sort_keys=True)
    return overlay


def pieces(proj):
    """The translations of `proj`: (module root, -lean-root arguments, packages, owned)."""
    return [(proj.root, proj.lean_roots, proj.packages, proj.owned)] + [
        (p.root, p.lean_roots, p.packages, p.owned) for p in proj.parts]


def source(proj, local, check):
    """The checkout to translate, and a description of it for the output."""
    if proj.local is not None:
        if local is not None:
            sys.exit(f"goose.py: {proj.name} is translated from {proj.local}; no --src")
        return os.path.join(ROOT, proj.local), proj.local
    if local is None:
        return checkout(proj.repo, proj.rev, os.path.join(WORK, proj.name)), proj.rev[:12]
    local = os.path.abspath(local)
    head, dirty = git_head(local), git_dirty(local)
    print(f"goose.py: {proj.name}: USING THE LOCAL CHECKOUT {local} (HEAD {head}"
          f"{', with uncommitted changes' if dirty else ''}) instead of cloning "
          f"{proj.repo} at {proj.rev}", file=sys.stderr)
    if head != proj.rev or dirty:
        msg = (f"goose.py: {proj.name}: the local checkout is not the pinned revision "
               f"{proj.rev}" + (" (uncommitted changes)" if dirty else ""))
        if check:
            sys.exit(msg + "; --check needs the pinned revision")
        print(msg + "; the output is not what the pin produces", file=sys.stderr)
    return local, f"{proj.rev[:12]} (local checkout {local})"


def with_proph_patches(proj, src, desc):
    """The source to translate: `src`, or a copy with the project's prophecy patches applied
    (`etc/proph-patches/<project>/`, checked by etc/proph_patch.py)."""
    import proph_patch
    n = len(proph_patch.patches(proj.name))
    if n == 0:
        return proj, src, desc
    dest = os.path.join(WORK, proj.name + ".proph")
    return proj, proph_patch.patched_copy(proj.name, src, dest), f"{desc} + {n} prophecy patch(es)"


def expand_comment_tabs(top):
    """Project.expand_comment_tabs: every `.lean` file under `top` with the tabs in its comments
    (`/- … -/`, nested, and `--` to the end of the line) replaced by four spaces; exits on a tab
    elsewhere (in a string literal, or in code)."""
    for d, _, fs in os.walk(top):
        for name in fs:
            if not name.endswith(".lean"):
                continue
            p = os.path.join(d, name)
            with open(p) as f:
                src = f.read()
            if "\t" not in src:
                continue
            out, depth, i, n = [], 0, 0, len(src)
            while i < n:
                if not depth and src[i] == '"':
                    j = i + 1
                    while j < n and src[j] != '"':
                        j += 2 if src[j] == "\\" else 1
                    seg = src[i:j + 1]
                    if "\t" in seg:
                        sys.exit(f"goose.py: a tab in a string literal in {p}")
                    out.append(seg)
                    i = j + 1
                    continue
                if src.startswith("/-", i):
                    depth += 1
                    out.append("/-")
                    i += 2
                    continue
                if depth and src.startswith("-/", i):
                    depth -= 1
                    out.append("-/")
                    i += 2
                    continue
                if not depth and src.startswith("--", i):
                    j = src.find("\n", i)
                    j = n if j < 0 else j
                    out.append(src[i:j].replace("\t", "    "))
                    i = j
                    continue
                c = src[i]
                if c == "\t":
                    if not depth:
                        sys.exit(f"goose.py: a tab outside a comment in {p}")
                    c = "    "
                out.append(c)
                i += 1
            with open(p, "w") as f:
                f.write("".join(out))


def translate(proj, src, bindir, perennial_rev, desc, check):
    """Translate `proj`; return True if the checked-in translation is (now) up to date."""
    out = tempfile.mkdtemp(prefix="goose-", dir=WORK)
    try:
        # path relative to ROOT -> (new content or None, old content or None)
        new, old = {}, {}
        env = module_models_env(proj, src, std_models_env(proj), out)
        overlay = model_overlay(proj, src, env, out)
        for i, (root, lean_roots, packages, owned) in enumerate(pieces(proj)):
            lib_dir = os.path.join(ROOT, root)
            piece_out = os.path.join(out, str(i))
            config = os.path.join(lib_dir, "Code")
            roots = [a for r in lean_roots for a in ("-lean-root", r)]
            if proj.tags:
                roots = ["-tags", ",".join(proj.tags)] + roots
            if overlay and i == 0:
                roots = ["-overlay", overlay] + roots
            for tool, sub in (("goose", "Code"), ("proofgen", "GeneratedProof")):
                run([os.path.join(bindir, tool)] + roots +
                    ["-out", os.path.join(piece_out, sub), "-configdir", config, "-dir", src]
                    + packages, env=env)
            others = others_owned(root, owned)
            if proj.expand_comment_tabs:
                expand_comment_tabs(piece_out)
            for f, c in lean_files(piece_out, owned, others).items():
                new[os.path.join(root, f)] = (c, os.path.join(piece_out, f))
            for f, c in lean_files(lib_dir, owned, others).items():
                old[os.path.join(root, f)] = c
        newc = {f: c for f, (c, _) in new.items()}
        changed = sorted(f for f in newc.keys() | old.keys() if newc.get(f) != old.get(f))
        with PRINT_LOCK:
            return _report(proj, new, newc, old, changed, perennial_rev, desc, check)
    finally:
        shutil.rmtree(out, ignore_errors=True)


PRINT_LOCK = __import__("threading").Lock()


def _report(proj, new, newc, old, changed, perennial_rev, desc, check):
    """`translate`'s verdict on one project, printed under PRINT_LOCK (projects run at once)."""
    if check:
        if not changed:
            print(f"goose.py: the translation of {proj.name} is up to date (Perennial "
                  f"{perennial_rev}, {proj.name} {desc})")
            return True
        for f in changed:
            sys.stdout.writelines(difflib.unified_diff(
                old.get(f, "").splitlines(keepends=True), newc.get(f, "").splitlines(keepends=True),
                "checked-in/" + f, "translator/" + f))
        print(f"goose.py: {len(changed)} file(s) of the translation of {proj.name} differ from what Perennial "
              f"{perennial_rev} produces from {proj.name} {desc}; run etc/goose.py",
              file=sys.stderr)
        return False
    for f in changed:
        dst = os.path.join(ROOT, f)
        if f in new:
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(new[f][1], dst)
        else:
            os.remove(dst)
    print(f"goose.py: {proj.name}: {len(changed)} file(s) updated (Perennial {perennial_rev}, "
          f"{proj.name} {desc})")
    return True


def main():
    names = [p.name for p in PROJECTS]
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--project", action="append", choices=names)
    ap.add_argument("--src", action="append", default=[], metavar="NAME=DIR")
    ap.add_argument("--perennial", default=os.environ.get("PERENNIAL_DIR"))
    args = ap.parse_args()
    os.environ["GOTOOLCHAIN"] = GO_TOOLCHAIN
    # The checked-in translations are linux/amd64's with cgo (the standard library's
    # cgo-processed packages, e.g. `net`, translate differently per target): translate for that
    # target on any host unless told otherwise (an arm64 host needs amd64's C cross-compiler for
    # cgo). host_env() keeps these out of the translator's own build.
    for k, v in (("GOOS", "linux"), ("GOARCH", "amd64"), ("CGO_ENABLED", "1")):
        os.environ.setdefault(k, v)
    if platform.machine() not in ("x86_64", "amd64"):
        os.environ.setdefault("CC", "x86_64-linux-gnu-gcc")

    projects = [p for p in PROJECTS if not args.project or p.name in args.project]
    local = {p.name: os.environ[p.env] for p in PROJECTS if os.environ.get(p.env)}
    for s in args.src:
        name, sep, d = s.partition("=")
        if not sep or name not in names:
            ap.error(f"--src {s}: expected NAME=DIR with NAME one of {', '.join(names)}")
        local[name] = d

    if args.perennial:
        perennial, rev = os.path.abspath(args.perennial), git_head(args.perennial) or "?"
        rev += " (--perennial " + perennial + ")"
    else:
        perennial, rev = pinned_perennial()
    sources = [(p,) + source(p, local.get(p.name), args.check) for p in projects]
    sources = [with_proph_patches(p, src, desc) for p, src, desc in sources]

    bindir = os.path.join(WORK, "bin")
    os.makedirs(bindir, exist_ok=True)
    run(["go", "build", "-o", bindir + os.sep, "./goose/cmd/goose", "./goose/cmd/proofgen"],
        cwd=perennial, env=host_env())

    # the projects at once ($GOOSE_JOBS lanes, default 4): each translation is independent (its
    # own output directory), and Goose loads and type-checks its Go packages on about five cores;
    # one after another, the check took 2.5 minutes of the gates (2026-11-18)
    import concurrent.futures
    jobs = max(1, int(os.environ.get("GOOSE_JOBS") or 4))
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        ok = list(ex.map(lambda a: translate(a[0], a[1], bindir, rev, a[2], args.check), sources))
    pin_errors = go_mod_pin_errors()
    for e in pin_errors:
        print("goose.py: " + e, file=sys.stderr)
    if not all(ok) or (args.check and pin_errors):
        sys.exit(1)


if __name__ == "__main__":
    main()
