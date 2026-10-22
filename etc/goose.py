#!/usr/bin/env python3
"""Regenerate, or check, the Goose translations of raft and etcd (in `Code/`, `GeneratedProof/`).

usage: etc/goose.py [--check] [--project NAME]... [--src NAME=DIR]... [--perennial DIR]

  --check      translate into a scratch directory and compare with the checked-in
               files; exit 1 (printing a diff) if they differ.  A gate for CI: the
               checked-in translation must be exactly what the pinned translator
               produces from the pinned Go source.
  --project    only this project (raft, etcd, kv, putget, putget3, linkv, linkvtxn, porcupine, bridge,
               lintest, raft-witness or kvwitness; repeatable; default: all).
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
Without --check, the generated `.lean` files under `{Code,GeneratedProof}/`
(in the subdirectories the project owns) are replaced by fresh output.  The Goose
configuration (`*.toml`, next to the code) is input and is never touched.

The translator (`goose`, `proofgen`) is built with `go` from Perennial's `goose/`.
The pinned Perennial is `.lake/packages/perennial` when Lake has already checked it
out at the pinned revision, otherwise a clone in `.lake/goose/perennial`.  A
project's source is cloned into `.lake/goose/<name>` at its pinned revision, except
for a project in this repository (`local`), whose source is that directory.
"""

import argparse
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
WORK = os.path.join(ROOT, ".lake", "goose")


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
    # The module root of the translation: "" for `Code/`, `GeneratedProof/`; else
    # `<root>/Code/`, `<root>/GeneratedProof/` (configured by `<root>/Code/**.toml`), for
    # a project whose Go paths another project also translates (raft-witness and kvwitness,
    # the parallel tree `RaftWitness/`; raft v3.7 was one, the parallel tree `Raft37/` the
    # raft proof was ported into).
    root: str = ""

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
        # plus the second fix). (The raft proof was ported to it in a parallel tree, the module root Raft37,
        # stages R0-R5 of notes/raft-retarget-plan.md; stage R6 made it the raft tree, 2026-10-16.)
        # Modules Code.go_etcd_io.raft.v3*, GeneratedProof.go_etcd_io.raft.v3*.
        repo="https://github.com/upamanyus/etcd",
        rev="c8217eb91ae5948182c1035ff0464b1e54b8f1d0",
        # raft's `proto` import is the names-only `Code.google_golang_org.protobuf.proto`
        # of the etcd project (as the protobuf runtime types raftpb's messages hold).
        lean_roots=["go.etcd.io/raft/v3=", "google.golang.org="],
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
        # issues/etcd-watch-sync-ticker-reset-zero.md) and `AuthInfoFromTLS`'s checked assertion
        # as 17c88a667 (issues/etcd-auth-tls-info-assert.md), and the client's
        # `closeRequireLeader` context alignment (a7bd9a16e,
        # issues/etcd-lease-close-require-leader-ctx-misaligned.md) and the retry interceptor's
        # non-repeatable context-error return (8a24be2a3, issues/etcd-client-retry-put-ctx-error.md),
        # and the gRPC quota's current backend (8f793b820,
        # issues/etcd-quota-stale-backend-after-snapshot.md; D22g (A)) and the auth store's move
        # before the old backend's close (d52eec43e,
        # issues/etcd-auth-snapshot-closed-backend-panic.md; D22k (A)), and the merged snapshot
        # sent only at its message's term (de825d8c6, issues/etcd-merged-snapshot-stale-term.md;
        # D22a), and (D25, the watch client's reconnection) the four fixes of branch
        # `watch-resume-fixes` (04375baaa..b3c29bc17, made on 8a24be2a3) cherry-picked on top: a
        # server-canceled substream's id reset (cafce83d8,
        # issues/etcd-watch-resume-stale-canceled-id.md) and no nil channel on `retc`
        # (c15c7dda8, issues/etcd-watch-resume-nil-watch-chan.md) and the resume revision only
        # moving forward (2e2dc077c, issues/etcd-watch-resume-below-start-revision.md) and
        # `waitCancelSubstreams` adding one goroutine at a time to its wait group (2aed163b1,
        # issues/etcd-watch-resume-waitgroup-overflow.md).
        # Branch
        # `goose` (upstream main of 2026-03) stays as it is: the Rocq translations
        # (etcd-grove `main`, Perennial `master`) are regenerated from it by name.
        repo="https://github.com/upamanyus/etcd",
        rev="2aed163b15c64eb415382dcedb6558a09dff203a",
        # go.etcd.io/raft/v3 (etcd's go.mod: v3.7.0) is the raft above (v3.7.0 plus the
        # read-index fix), translated by the raft project: not translated here.
        lean_roots=["go.etcd.io/etcd=", "k8s.io=", "google.golang.org=", "go.uber.org=",
                    "go.etcd.io/bbolt=", "go.opentelemetry.io=",
                    "github.com/dustin/go-humanize=", "github.com/prometheus/client_golang=", "net/http=",
                    "net=",
                    "encoding/hex=", "container/heap=", "unicode/utf8=",
                    "github.com/Masterminds/semver=", "go.etcd.io/raft/v3=",
                    "golang.org/x/time=", "github.com/xiang90/probing=", "crypto/tls=",
                    "github.com/grpc-ecosystem="],
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
            # names only, with the two features the request path reads
            "go.etcd.io/etcd/server/v3/features",
            # with bodies (storage/backend.toml): the backend over bbolt, its buffers and
            # transactions
            "go.etcd.io/etcd/server/v3/storage/backend",
            # types and names only: what the server's types and the apply thread name
            "go.etcd.io/etcd/server/v3/storage",
            "go.etcd.io/etcd/server/v3/storage/mvcc",
            "go.etcd.io/etcd/server/v3/config",
            "go.etcd.io/etcd/server/v3/etcdserver/api/membership",
            "go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp",
            "go.etcd.io/etcd/server/v3/etcdserver/api/snap",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v2stats",
            # names only (D21 M2): `Process`'s `403` errors (`httptypes.NewHTTPError`)
            "go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp/types",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm",
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
            # types only: the lease's protobuf message (the lessor's persistTo, Revoke)
            "go.etcd.io/etcd/server/v3/lease/leasepb",
            "go.etcd.io/etcd/server/v3/auth",
            "go.etcd.io/etcd/pkg/v3/contention",
            "go.etcd.io/etcd/pkg/v3/idutil",
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
            "go.etcd.io/etcd/server/v3/storage/wal",
            "go.etcd.io/etcd/client/pkg/v3/transport",
            "go.etcd.io/etcd/pkg/v3/featuregate",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3discovery",
            "go.etcd.io/bbolt",
            # names only: bbolt's errors (the backend's UnsafeDeleteBucket compares with one)
            "go.etcd.io/bbolt/errors",
            # bbolt's page-id helpers, with bodies (bbolt/internal/common.toml)
            "go.etcd.io/bbolt/internal/common",
            "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc",
            # names only: what mvcc's watchStream.Watch calls (SpanFromContext, Span.End)
            "go.opentelemetry.io/otel/trace",
            # types only: the interfaces trace.Span embeds and the types of its methods' parameters
            # (so that Goose translates Span as an interface)
            "go.opentelemetry.io/otel/trace/embedded",
            "go.opentelemetry.io/otel/codes",
            "go.opentelemetry.io/otel/attribute",
            "google.golang.org/protobuf/proto",
            "google.golang.org/protobuf/reflect/protoreflect",
            "go.uber.org/zap",
            "go.uber.org/zap/zapcore",
            "github.com/dustin/go-humanize",
            # names only: the metrics mvcc's transactions and key index update
            "github.com/prometheus/client_golang/prometheus",
            # standard-library packages Perennial does not translate: their names are here
            # (encoding/hex: the backend's putSeq check formats keys with it)
            "net/http",
            # (net: the interface net.Addr, the type of grpc's peer.Peer's fields; unit P3a)
            "net",
            "encoding/hex",
            # (container/heap: the lessor's expiry notifier pushes and fixes its queue)
            "container/heap",
            # (unicode/utf8: the server's unary interceptor checks the client's API version,
            # unit P3b)
            "unicode/utf8",
            # types and names only (their .toml)
            "go.etcd.io/etcd/client/v3",
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
            "crypto/tls",
            # names only (item 4, the server start): what `v3rpc.Server` names: grpc-prometheus
            # (its server metrics and interceptors), grpc's health service and its protobuf
            # package (the registration, the serving status), grpc's reflection interface
            # (`ServerMetrics.InitializeMetrics`'s parameter)
            "github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus",
            "google.golang.org/grpc/health",
            "google.golang.org/grpc/health/grpc_health_v1",
            "google.golang.org/grpc/reflection",
            # (and go.uber.org/zap, above)
            # names only: the types of rafthttp.Transport's fields, so that its struct is
            # translated (NewServer builds one; unit N4, 2026-10-17)
            "golang.org/x/time/rate",
            "github.com/xiang90/probing",
            # names only: the types of the server's configuration's fields (types.URLs' url.URL,
            # transport.TLSInfo's crypto/tls types, crypto/tls listed above), so that those
            # structs are translated (NewServer splits the configuration; unit N4, 2026-10-17)
            "net/url",
        ],
        owned=[os.path.join("go_etcd_io", "etcd"), os.path.join("go_etcd_io", "bbolt"),
               os.path.join("github_com", "prometheus"),
               os.path.join("github_com", "Masterminds"),
               "k8s_io", "google_golang_org", "go_uber_org", "go_opentelemetry_io",
               "net", os.path.join("encoding", "hex"), os.path.join("crypto", "tls"),
               os.path.join("container", "heap"), os.path.join("unicode", "utf8"),
               os.path.join("github_com", "dustin"), os.path.join("golang_org", "x", "time"),
               os.path.join("github_com", "xiang90"),
               os.path.join("github_com", "grpc_ecosystem")],
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
    ),
    Project(
        name="kv",
        # An example application on raft's Node: a replicated string-to-string key-value
        # store (Put, Get, Append; until 2026-10-19 the replicated string register
        # `examples/register`), with its randomized linearizability test over the lintest
        # driver and porcupine (check.go). A Go module of this repository, whose go.mod requires
        # go.etcd.io/raft/v3 and replaces it by the revision pinned above
        # (`github.com/upamanyus/etcd/v3`, the fork's pseudo-version under a /v3 path, since
        # its go.mod declares go.etcd.io/raft/v3; keep the two in step), and lintest and
        # porcupine by this repository's copies.
        repo=None,
        rev=None,
        local=os.path.join("examples", "kv"),
        # (raft v3.7, stage R6b: the store reaches protobuf-go's `proto`, which the raft
        # tree translates into the root, `Code.google_golang_org.protobuf.proto`; lintest is
        # the lintest project's translation, porcupine the porcupine project's)
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=", "google.golang.org=",
                    "github.com/anishathalye/porcupine="],
        # the store; not its command (cmd/kvcheck), which only runs it
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "kv")],
    ),
    Project(
        name="putget",
        # The adequacy example of etcd's server and client (open-work item 9): one member
        # started in-process, a client's Put and Get of one key. A Go module of this
        # repository whose go.mod replaces etcd's modules by the etcd fork at the etcd pin
        # above and go.etcd.io/raft/v3 by the raft pin (pseudo-versions; keep them in step).
        # Its imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "putget"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "putget")],
    ),
    Project(
        name="linkv",
        # The lintest driver instantiated with etcd (D20): one member started in-process, as
        # in putget, and lintest.Run's clients doing Put and Get through one client, checked
        # by porcupine against a key-value model. A Go module of this repository, with
        # putget's replaces (keep them in step); its imports are the etcd, lintest and
        # porcupine projects' translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "linkv"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "linkv")],
    ),
    Project(
        name="linkvtxn",
        # The lintest driver over etcd's KV API as its robustness tester drives it
        # (notes/linkv-txn-plan.md, stage D): linkv's member and client, and lintest.Run's
        # clients doing gets, lists, puts, deletes and transactions, checked by porcupine against
        # the robustness model's Go form (Model, the Lean TxnModel's). A Go module of this
        # repository, with putget's replaces (keep them in step; its tests' robustness model is
        # etcd's tests/v3, test-only); its imports are the etcd, lintest and porcupine projects'
        # translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "linkvtxn"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "linkvtxn")],
    ),
    Project(
        name="linkv3",
        # linkv over a three-member cluster (D20, D21): three members started in-process as in
        # putget3, a client to the first, and linkv's workload (`linkv.Check`, imported). A Go
        # module of this repository, with putget's replaces (keep them in step); its imports
        # are the etcd, linkv, lintest and porcupine projects' translations (names reached
        # through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "linkv3"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "linkv3")],
    ),
    Project(
        name="linkv3p",
        # linkv3 under network partitions (notes/partition-plan.md): three members started
        # in-process as in putget3, each serving its gRPC API, a client to each, a partitioner
        # goroutine cutting and mending links on `Main`'s schedule (etcd's `CutPeer`/`MendPeer`),
        # and linkvtxn's workload (`Gen`, `Apply`, `Model`, imported; its own `Apply` picks the
        # member; linkv's until 2026-10-20, notes/linkv3p-txn-plan.md). A Go module of this
        # repository, with putget's replaces (keep them in step); its imports are the etcd,
        # linkvtxn, lintest and porcupine projects' translations (names reached through the empty
        # root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "linkv3p"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine=",
                    "go.etcd.io/etcd=", "go.etcd.io/raft/v3=", "go.uber.org=",
                    "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "linkv3p")],
    ),
    Project(
        name="watchkv",
        # The watch example: one member started in-process, as in putget, a prefix watch from
        # revision 1, writer goroutines putting random keys under the prefix, and a check of the
        # watched events against the writes. A Go module of this repository, with putget's
        # replaces (keep them in step); its imports are the etcd project's translations (names
        # reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "watchkv"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "watchkv")],
    ),
    Project(
        name="cachekv",
        # watchkv with the watch read through etcd's cache: one member started in-process, as in
        # putget, a cache of the prefix over the client, a cache watch from revision 2, writer
        # goroutines putting random keys under the prefix, and watchkv's check. A Go module of
        # this repository, with putget's replaces and the cache module's (keep them in step); its
        # imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "cachekv"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "cachekv")],
    ),
    Project(
        name="putget3",
        # putget with three members (D21 stage M5): three members started in-process, each
        # serving its raft handler on its own peer listener, a client's Put and Get through the
        # first. A Go module of this repository, with putget's replaces (keep them in step); its
        # imports are the etcd project's translations (names reached through the empty root).
        repo=None,
        rev=None,
        local=os.path.join("examples", "putget3"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/etcd=", "go.etcd.io/raft/v3=",
                    "go.uber.org=", "google.golang.org=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "putget3")],
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
        name="bridge",
        # etcd's integration tests' TCP bridge between a client and a member (tests/framework/
        # integration/bridge.go at the etcd pin), vendored with an exported constructor
        # (third_party/bridge/UPSTREAM.md): linkv3p's cuts between a client and its member
        # (notes/client-cut-plan.md). Its imports are standard library: io, sync (Perennial's)
        # and net (the etcd project's names, the empty root).
        repo=None,
        rev=None,
        local=os.path.join("third_party", "bridge"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "net="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "third_party")],
    ),
    Project(
        name="lintest",
        # A generic driver over porcupine: clients that run a linearizable library's
        # operations, traced as etcd's robustness tests trace them, then checked.
        repo=None,
        rev=None,
        local=os.path.join("examples", "lintest"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "github.com/anishathalye/porcupine="],
        # the driver, and an instance of it (a counter under a mutex, its model)
        packages=[".", "./counter"],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "lintest")],
    ),
    Project(
        name="raft-witness",
        # The witness experiment (notes/raft-witness.md; a candidate implementation of
        # etcd-io/raft#133, not merged upstream): branch raft-witness-goose-lean of the etcd
        # fork, etcd-io/raft#168 rebased onto raft37-goose-lean-a1 (project raft's pin) with
        # the fixes of notes/raft-witness-vs-pr168.md, at 99cb9e2d9 (a witness shared by both
        # halves of a joint configuration is sent an entry only if both replicate to it;
        # notes/raft-witness-reconfig.md). Translated into the parallel tree RaftWitness
        # (modules RaftWitness.Code.go_etcd_io.raft.v3*, ...), which nothing outside it imports;
        # the same packages as project raft, configured by RaftWitness/Code/**.toml.
        repo="https://github.com/upamanyus/etcd",
        rev="99cb9e2d98d40d423aa7e7ec1f12f0877a45570e",
        root="RaftWitness",
        # raft's `proto` import is the main tree's names-only `Code.google_golang_org.protobuf.proto`
        lean_roots=["go.etcd.io/raft/v3=RaftWitness", "google.golang.org="],
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
        name="kvwitness",
        # The key-value store example (project kv) on the witness raft (project raft-witness):
        # a cluster of two voters and an in-process witness (`StartClusterWitness`, `MainWitness`;
        # notes/raft-witness.md, "W4"). A Go module of this repository whose go.mod replaces
        # go.etcd.io/raft/v3 by the fork at raft-witness's pin (keep the two in step), and
        # lintest and porcupine by this repository's copies. Translated into RaftWitness, its
        # raft the raft-witness project's, lintest and porcupine the main tree's.
        repo=None,
        rev=None,
        local=os.path.join("examples", "kvwitness"),
        root="RaftWitness",
        lean_roots=["github.com/mit-pdos/etcd-grove/examples/kvwitness=RaftWitness",
                    "github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3=RaftWitness",
                    "google.golang.org=", "github.com/anishathalye/porcupine="],
        # the store; not its command (cmd/kvcheck), which only runs it
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove", "examples", "kvwitness")],
    ),
]


def run(args, cwd=None, quiet=False):
    if not quiet:
        print("+ " + " ".join(args), file=sys.stderr)
    subprocess.run(args, cwd=cwd, check=True)


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


def lean_files(d, owned):
    """The `.lean` files under `d/{Code,GeneratedProof}/` at the paths `owned`."""
    out = {}
    for sub in ("Code", "GeneratedProof"):
        for o in owned:
            base = os.path.join(d, sub, o)
            paths = [base + ".lean"] if os.path.isfile(base + ".lean") else []
            for dp, _, fs in os.walk(base):
                paths.extend(os.path.join(dp, f) for f in fs if f.endswith(".lean"))
            for path in paths:
                out[os.path.relpath(path, d)] = open(path, encoding="utf-8").read()
    return out


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


def translate(proj, src, bindir, perennial_rev, desc, check):
    """Translate `proj`; return True if the checked-in translation is (now) up to date."""
    out = tempfile.mkdtemp(prefix="goose-", dir=WORK)
    try:
        # path relative to ROOT -> (new content or None, old content or None)
        new, old = {}, {}
        for i, (root, lean_roots, packages, owned) in enumerate(pieces(proj)):
            lib_dir = os.path.join(ROOT, root)
            piece_out = os.path.join(out, str(i))
            config = os.path.join(lib_dir, "Code")
            roots = [a for r in lean_roots for a in ("-lean-root", r)]
            for tool, sub in (("goose", "Code"), ("proofgen", "GeneratedProof")):
                run([os.path.join(bindir, tool)] + roots +
                    ["-out", os.path.join(piece_out, sub), "-configdir", config, "-dir", src]
                    + packages)
            for f, c in lean_files(piece_out, owned).items():
                new[os.path.join(root, f)] = (c, os.path.join(piece_out, f))
            for f, c in lean_files(lib_dir, owned).items():
                old[os.path.join(root, f)] = c
        newc = {f: c for f, (c, _) in new.items()}
        changed = sorted(f for f in newc.keys() | old.keys() if newc.get(f) != old.get(f))
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
    finally:
        shutil.rmtree(out, ignore_errors=True)


def main():
    names = [p.name for p in PROJECTS]
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--project", action="append", choices=names)
    ap.add_argument("--src", action="append", default=[], metavar="NAME=DIR")
    ap.add_argument("--perennial", default=os.environ.get("PERENNIAL_DIR"))
    args = ap.parse_args()

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

    bindir = os.path.join(WORK, "bin")
    os.makedirs(bindir, exist_ok=True)
    run(["go", "build", "-o", bindir + os.sep, "./goose/cmd/goose", "./goose/cmd/proofgen"],
        cwd=perennial)

    ok = [translate(p, src, bindir, rev, desc, args.check) for p, src, desc in sources]
    if not all(ok):
        sys.exit(1)


if __name__ == "__main__":
    main()
