#!/usr/bin/env python3
"""Generate a package's Link.lean: every proof instantiated with its callees' results.

The result of a function <fn> is its `wp_proof` applied to the callees' results, in the
order of the `wp_proof`'s hypotheses:

    theorem <T>.wp_<M> : <T>.<M>.spec (GF := GF) (hG := hG) := <T>.<M>.wp_proof <callees>

The functions and their callees are listed in a mode's etc/link-lean-first-<mode>.txt, one
per line as `<fn>: <callee> <callee> ...`. (Until stage R6 of the raft v3.7 retarget,
2026-10-16, the raft Link was generated from the Rocq link structure of branch `main`,
spec_<fn>.v/postulates_<fn>.v, with etc/link-lean-first.txt for the Lean-first functions;
the retargeted raft proof is Lean-first throughout.)

The Spec/Proof files of a function are found by its name: `Spec/<pkg>/<fn>.lean`, or
`Spec/<pkg>/<f>.lean` for a name `<last component of pkg>_<f>` (tracker_NewInflights:
Spec/go_etcd_io/raft/v3/tracker/NewInflights.lean).

usage: etc/gen-link.py --raft > Proof/go_etcd_io/raft/v3/Link.lean
       etc/gen-link.py --cache > Proof/go_etcd_io/etcd/cache/v3/Link.lean
       etc/gen-link.py --server > Proof/go_etcd_io/etcd/server/v3/etcdserver/Link.lean
       etc/gen-link.py --concurrency > Proof/go_etcd_io/etcd/client/v3/concurrency/Link.lean
       etc/gen-link.py --leasing > Proof/go_etcd_io/etcd/client/v3/leasing/Link.lean
       etc/gen-link.py --recipes > Proof/go_etcd_io/etcd/client/v3/experimental/recipes/Link.lean
       etc/gen-link.py --v3lock > Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3lock/Link.lean
       etc/gen-link.py --v3election > Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3election/Link.lean
       etc/gen-link.py --kv > Proof/github_com/mit_pdos/etcd_grove/examples/kv/Link.lean
       etc/gen-link.py --raft-witness > RaftWitness/Proof/go_etcd_io/raft/v3/Link.lean
       etc/gen-link.py --kvwitness > RaftWitness/Proof/github_com/mit_pdos/etcd_grove/examples/kvwitness/Link.lean
       etc/gen-link.py --mvcc > Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Link.lean
       etc/gen-link.py --backend > Proof/go_etcd_io/etcd/server/v3/storage/backend/Link.lean
       etc/gen-link.py --adt > Proof/go_etcd_io/etcd/pkg/v3/adt/Link.lean
       etc/gen-link.py --txn > Proof/go_etcd_io/etcd/server/v3/etcdserver/txn/Link.lean
       etc/gen-link.py --apply > Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Link.lean
       etc/gen-link.py --v3rpc > Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Link.lean
       etc/gen-link.py --fmt > Proof/fmt/Link.lean
       etc/gen-link.py --context > Proof/context/Link.lean
       etc/gen-link.py --read > Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Link.lean
       etc/gen-link.py --client > Proof/go_etcd_io/etcd/client/v3/Link.lean
       etc/gen-link.py --porcupine > Proof/github_com/anishathalye/porcupine/Link.lean
       etc/gen-link.py --lintest > Proof/github_com/mit_pdos/etcd_grove/examples/lintest/Link.lean
       etc/gen-link.py --lintest-counter > Proof/github_com/mit_pdos/etcd_grove/examples/lintest/counter/Link.lean
       etc/gen-link.py --lintest-logkv > Proof/github_com/mit_pdos/etcd_grove/examples/lintest/logkv/Link.lean
       etc/gen-link.py --linkvtxn > Proof/github_com/mit_pdos/etcd_grove/examples/linkvtxn/Link.lean
       etc/gen-link.py --linkv3p > Proof/github_com/mit_pdos/etcd_grove/examples/linkv3p/Link.lean
       etc/gen-link.py --watchkv > Proof/github_com/mit_pdos/etcd_grove/examples/watchkv/Link.lean
       etc/gen-link.py --cachekv > Proof/github_com/mit_pdos/etcd_grove/examples/cachekv/Link.lean
       etc/gen-link.py --authkv > Proof/github_com/mit_pdos/etcd_grove/examples/authkv/Link.lean
       etc/gen-link.py --k8s > Proof/go_etcd_io/etcd/client/v3/kubernetes/Link.lean
       etc/gen-link.py --k8s-etcd3 > Proof/k8s_io/apiserver/pkg/storage/etcd3/Link.lean
       etc/gen-link.py --cacher > Proof/k8s_io/apiserver/pkg/storage/cacher/Link.lean
       etc/gen-link.py --k8setcd3 > Proof/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Link.lean
       etc/gen-link.py --common > Proof/github_com/mit_pdos/etcd_grove/examples/common/Link.lean

`--cache` links the proofs of etcd's `cache` package (`Proof/go_etcd_io/etcd/cache/v3/` and
the specs and proofs of its functions), which are all
Lean-first: they are read from etc/link-lean-first-cache.txt alone, with no Rocq side.
`--server` likewise links the proofs of etcd's server (the consistent index and the apply
thread, `Proof/go_etcd_io/etcd/server/v3/etcdserver/`), from etc/link-lean-first-server.txt
(raft's functions it calls, the raftpb getters, `IsEmptySnap`, ..., are `@` callees since stage
R6 of the raft v3.7 retarget, linked in raft's `Link.lean`; before, `EtcdDeps/Spec/`'s, etcd's own
raft dependency names-only).
`--concurrency` links the proofs of `client/v3/concurrency` (`Session`) and of the clientv3
functions they and the next recipes use, from etc/link-lean-first-concurrency.txt, under the
concurrency package's assumptions. Its results are in the namespace `concurrency`, a clientv3
function's with the prefix `v3.` (`concurrency.v3.wp_OpPut`), and the specs are referred to by
their full names below `EtcdGrove`: the cache's Link links some of the same clientv3 functions
(under the cache's assumptions), and concurrency's `WithLease` shares its name with clientv3's.
`--leasing` links the proofs of `client/v3/leasing` (the lease cache) and of the clientv3,
etcdserverpb and standard-library functions they call, from etc/link-lean-first-leasing.txt,
under the leasing package's assumptions; as `--concurrency`, its results are in a namespace of
their own (`leasing`), a clientv3 function's with the prefix `v3.`.
`--recipes` links the proofs of `client/v3/experimental/recipes` (barrier, double barrier, queue,
priority queue, RWMutex) and of the clientv3 and concurrency functions they call, from
etc/link-lean-first-recipes.txt, under the recipes package's assumptions; as `--leasing`, its
results are in a namespace of their own (`recipes`), a clientv3 function's with the prefix `v3.`
and concurrency's with the prefix `concurrency.` (its specs' own namespace,
`recipes.concurrency.Session.wp_Client`).
A callee list `?` (`fn: ?`) marks a function specified but not proved yet (a later unit's): its
spec is a hypothesis (`h_<fn>`, `section links_pending`) of every result that reaches it.
`--mvcc` links the proofs of the KV core of etcd's `server/v3/storage/mvcc`
(`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`), from etc/link-lean-first-mvcc.txt.
`--backend` links the proofs of etcd's backend (`server/v3/storage/backend`: the buffers, the
read and batch transactions), from etc/link-lean-first-backend.txt; bbolt's key-value contract
(`Spec/go_etcd_io/bbolt/*_kv*.lean`, axioms) is its trust boundary. As `--recipes`, its results are
in a namespace of their own (`backend`).
`--adt` links the proofs of etcd's interval tree (`pkg/v3/adt`, `Proof/go_etcd_io/etcd/pkg/v3/adt/`),
from etc/link-lean-first-adt.txt: the tree's contract pending (`?`), the comparisons proved.
`--txn` links the proofs of etcd's server `txn` package (`server/v3/etcdserver/txn`: `Range`,
`Put`, `DeleteRange`, `Txn` over the mvcc core) and of the trust-boundary functions they call,
from etc/link-lean-first-txn.txt, under the txn package's assumptions; as `--recipes`, its
results are in a namespace of their own (`txn`: `txn.traceutil.wp_EnsureTrace`), and mvcc's
functions are `@` callees, linked in mvcc's `Link.lean`.
`--apply` links the proofs of etcd's server `apply` package (`server/v3/etcdserver/apply`: the
applier chain between the apply thread and the txn package) and of the trust-boundary functions
they call, from etc/link-lean-first-apply.txt, under the apply package's assumptions; as `--txn`,
its results are in a namespace of their own (`apply`), and the txn package's and mvcc's functions
are `@` callees, linked in their `Link.lean`s.
`--v3rpc` links the proofs of etcd's gRPC KV service (`server/v3/etcdserver/api/v3rpc`: the
handlers, the request checks, the response header, `togRPCError`) and of the trust-boundary
functions they call, from etc/link-lean-first-v3rpc.txt, under the package's assumptions (which
include the server's); as `--apply`, its results are in a namespace
of their own (`v3rpc`), and the server's, the txn package's and the interval tree's functions are
`@` callees, linked in their `Link.lean`s.
`--read` links the proofs of etcd's linearizable read loop (`server/v3/etcdserver/read`:
`NewRead`, `LinearizableReadNotify`, `LinearizableReadLoop`, over the contracts of its `server` and
`raftInterface`) and of the trust-boundary functions they call, from etc/link-lean-first-read.txt,
under the read package's assumptions; as `--txn`, its results are in a namespace of their own
(`read`).
`--client` links the proofs of the client's KV path over gRPC (unit C1: `NewKV`, `kv.Put`,
`kv.Get`, `kv.Do`, `ContextError`, the retry client, the generated stub `etcdserverpb.kVClient`)
and the trust boundary they rest on (grpc's `ClientConn.Invoke`, an axiom), from
etc/link-lean-first-client.txt, under clientv3's assumptions; as `--leasing`, its results are in
a namespace of their own (`client`), a clientv3 function's with the prefix `v3.`.
`--fmt` and `--context` link etcd-grove's trust boundary of the standard library's `fmt`
(`Errorf`, `Printf`) and `context` (the `Error()` of `Err()`'s error), from
etc/link-lean-first-fmt.txt and etc/link-lean-first-context.txt, under those packages' own
assumptions, so that Links of unrelated packages (the cache's, mvcc's) take them as `@` callees
instead of each defining the same result.
**Reuse** (2026-10-12): a callee whose result a Link this one imports already defines, under the
same name, is imported, not redefined: two Links defining one theorem cannot be imported
together (the trust report runs Lean on the roots a group of parts reaches together: the
server's Link with the apply package's, which imports mvcc's). The
Links searched are those of the `@` callees' packages and those a mode declares it imports
(`REUSES`: the server's imports mvcc's, which defines encoding/binary's and zap's `Error` too).
`--skip-unproved` (after the mode) leaves out the listed functions with no proof file yet (no
spec, or no `Proof/` file: a later unit's) and every function that reaches one, and names them
in the header: a package proved in units links what is done, from the full list.
The clients' modes (`--cache`, `--concurrency`, `--leasing`, `--recipes`) state their links over
the clients' model of etcd: their sections take `[EM : EtcdModel GF]` (the class of
`cache/v3/EtcdModel.lean`, which the server instantiates; the vertical slice's unit V1).
`--raft` links the Raft proof (raft v3.7 plus the read-index fix, `Code/go_etcd_io/raft/`;
`notes/raft-retarget-plan.md`) and the trust-boundary axioms of protobuf-go's `proto` it rests
on, from etc/link-lean-first-raft.txt (the mode was `--raft37`, into the parallel tree `Raft37/`,
until stage R6 swapped the trees).
`--kv` links the key-value store example's proofs (`examples/kv`; until 2026-10-19 the register
example, `--register`), from etc/link-lean-first-kv.txt; raft's, the porcupine driver's and
porcupine's functions it calls are `@` callees, linked in their `Link.lean`s, and its specs'
`[KVStor GF]` (the storage registry) is passed on.
`--raft-witness` and `--kvwitness` link the same in the parallel tree `RaftWitness/` (raft's
witness experiment, `notes/raft-witness.md`), from etc/link-lean-first-raft-witness.txt and
etc/link-lean-first-kvwitness.txt: their specs are searched in the main tree and in
`RaftWitness/`, the part's spec of a function taking the place of the main tree's.
"""
import os
import re
import sys
import textwrap

# The v3rpc package's assumptions (the server's model, `v3rpc.etcdModelOfServer`), which the
# client's watch specs take besides the client's (the watch slice's unit W-C).
SRV_ASSUMPTIONS = "go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions"

# **Semantic premises**: hypothesis classes on the semantics in use, as Perennial's `go.Semantics`,
# for what Perennial's semantics or a translation lacks (`notes/decisions.md`, "`int64(f)`: a
# hypothesis class"). A proof that needs one takes it as an instance argument of its `wp_proof`
# (written `[<name as here>]` in its file); its result takes it too, and so does every result
# linking one that does, here or in an imported Link (its `theorem` line).
SEM_PREMISES = [
    # `int64(f)` of a `float64` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/FloatToInt.lean`)
    "EtcdGrove.Float64ToInt64Semantics",
    # `(*Client).dialWithBalancer`'s body, which the translator cannot produce
    # (`Proof/go_etcd_io/etcd/client/v3/DialWithBalancerBody.lean`)
    "go_etcd_io.etcd.client.v3.DialWithBalancerBody",
    # (rafthttp stage 6f) `*errors.errorString` a leaf error without `Is` (`Proof/errors/NewVar.lean`)
    "EtcdGrove.ErrorStringLeaf",
    # (rafthttp stage 6f) a `*errorString` not a `writerToResponse` (`rafthttp/Pipe.lean`)
    "EtcdGrove.ErrorStringNotWriter",
]

# The Lean-first links: (callee list, what the links open, the package assumptions they
# are stated under, a description for the header, the module roots holding their specs).
LEAN_FIRST = {
    "--cache": ("link-lean-first-cache.txt", "go_etcd_io.etcd.cache.v3",
                "go_etcd_io.etcd.cache.v3.Assumptions", "The `cache` package's proofs", [""]),
    # etcdserver's assumptions include those of every package it imports (instances):
    # cindex's, schema's, raft v3.7's raftpb's, zap's, ..., which the other specs use
    "--server": ("link-lean-first-server.txt",
                 "go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage "
                 "go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 "
                 "go_etcd_io.etcd.pkg.v3 go_uber_org go_etcd_io.raft.v3",
                 "go_etcd_io.etcd.server.v3.etcdserver.Assumptions",
                 "The etcd server's proofs (the consistent index and the apply thread)",
                 [""]),
    "--concurrency": ("link-lean-first-concurrency.txt",
                      "go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3",
                      "go_etcd_io.etcd.client.v3.concurrency.Assumptions",
                      "The `client/v3/concurrency` package's proofs (`Session`) and the clientv3 "
                      "functions they and the next recipes use", [""]),
    "--leasing": ("link-lean-first-leasing.txt",
                  "go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3",
                  "go_etcd_io.etcd.client.v3.leasing.Assumptions",
                  "The `client/v3/leasing` package's proofs (the lease cache) and the functions "
                  "they call", [""]),
    # the mvcc KV core (etcd's server/v3/storage/mvcc)
    "--mvcc": ("link-lean-first-mvcc.txt", "go_etcd_io.etcd.server.v3.storage.mvcc",
               "go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions",
               "The mvcc KV core's proofs (etcd's `server/v3/storage/mvcc`)", [""]),
    # etcd's backend (server/v3/storage/backend) over bbolt's key-value contract
    "--backend": ("link-lean-first-backend.txt", "go_etcd_io.etcd.server.v3.storage.backend",
                  "go_etcd_io.etcd.server.v3.storage.backend.Assumptions",
                  "The backend's proofs (etcd's `server/v3/storage/backend`) and the trust "
                  "boundary they rest on (bbolt's key-value contract)", [""]),
    # the interval tree (etcd's pkg/v3/adt), the watchable store's
    "--adt": ("link-lean-first-adt.txt", "go_etcd_io.etcd.pkg.v3.adt",
              "go_etcd_io.etcd.pkg.v3.adt.Assumptions",
              "The interval tree's proofs (etcd's `pkg/v3/adt`)", [""]),
    # the server's txn package (etcd's server/v3/etcdserver/txn), over the mvcc core
    "--txn": ("link-lean-first-txn.txt",
              "go_etcd_io.etcd.server.v3.etcdserver.txn go_etcd_io.etcd.server.v3.storage.mvcc "
              "go_etcd_io.etcd.api.v3",
              "go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions",
              "The server's `txn` package's proofs (etcd's `server/v3/etcdserver/txn`) and the "
              "functions they call", [""]),
    # the server's apply package (etcd's server/v3/etcdserver/apply), over the txn package
    "--apply": ("link-lean-first-apply.txt",
                "go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.server.v3.etcdserver.txn "
                "go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3 go_etcd_io.etcd.pkg.v3 "
                "go_uber_org",
                "go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions",
                "The server's `apply` package's proofs (etcd's `server/v3/etcdserver/apply`) and the "
                "functions they call", [""]),
    # the gRPC KV service (etcd's server/v3/etcdserver/api/v3rpc), over the server's request
    # path; its assumptions include the server's
    "--v3rpc": ("link-lean-first-v3rpc.txt",
                "go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc go_etcd_io.etcd.server.v3.etcdserver "
                "go_etcd_io.etcd.api.v3 go_etcd_io.etcd.pkg.v3",
                "go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions",
                "The gRPC KV service's proofs (etcd's `server/v3/etcdserver/api/v3rpc`) and the "
                "functions they call", [""]),
    # the client's KV path over gRPC (unit C1, the client meets the server)
    "--client": ("link-lean-first-client.txt", "go_etcd_io.etcd.client.v3 go_etcd_io.etcd.api.v3",
                 "go_etcd_io.etcd.client.v3.Assumptions",
                 "The client's KV path over gRPC (`client/v3`'s `NewKV`, `kv.Put`, `kv.Get`, `kv.Do`, the "
                 "retry client, the generated stub) and the trust boundary it rests on (grpc's "
                 "`ClientConn.Invoke`)", [""]),
    "--recipes": ("link-lean-first-recipes.txt",
                  "go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3",
                  "go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions",
                  "The `client/v3/experimental/recipes` package's proofs and the functions they "
                  "call", [""]),
    # the Lock and Election services' servers (etcd's server/v3/etcdserver/api/v3lock,
    # v3election; the auth plan's A3c), over the client's concurrency package (`@`) and the
    # server's client as contracts
    "--v3lock": ("link-lean-first-v3lock.txt",
                 "go_etcd_io.etcd.server.v3.etcdserver.api.v3lock go_etcd_io.etcd.client.v3.concurrency",
                 "go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions",
                 "The Lock service's server's proofs (`server/v3/etcdserver/api/v3lock`)", [""]),
    "--v3election": ("link-lean-first-v3election.txt",
                     "go_etcd_io.etcd.server.v3.etcdserver.api.v3election go_etcd_io.etcd.client.v3.concurrency",
                     "go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions",
                     "The Election service's server's proofs (`server/v3/etcdserver/api/v3election`)", [""]),
    # etcd's linearizable read loop (etcd's server/v3/etcdserver/read), over its contracts
    "--read": ("link-lean-first-read.txt", "go_etcd_io.etcd.server.v3.etcdserver.read",
               "go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions",
               "The linearizable read loop's proofs (etcd's `server/v3/etcdserver/read`) and the "
               "functions they call", [""]),
    # etcd-grove's trust boundary of `fmt` and `context`, shared by unrelated Links (`@`)
    "--fmt": ("link-lean-first-fmt.txt", "", "_root_.Perennial.fmt.Assumptions",
              "etcd-grove's trust boundary of `fmt` (axioms)", [""]),
    "--context": ("link-lean-first-context.txt", "", "_root_.Perennial.context.Assumptions",
                  "etcd-grove's trust boundary of `context` (axioms)", [""]),
    # the key-value store example (examples/kv): its proofs, over raft's and the porcupine
    # driver's (linked in their `Link.lean`s, the `@` callees) and the storage model `KVStor`
    # gives
    "--kv": ("link-lean-first-kv.txt",
             "github_com.mit_pdos.etcd_grove.examples.kv go_etcd_io.raft.v3 "
             "github_com.mit_pdos.etcd_grove.examples.lintest github_com.anishathalye.porcupine",
             "github_com.mit_pdos.etcd_grove.examples.kv.Assumptions",
             "The key-value store example's proofs (`examples/kv`)", [""]),
    # the Raft proof (raft v3.7 plus the read-index fix, project raft of etc/goose.py) and the
    # trust boundary of protobuf-go it rests on (Spec/google_golang_org/protobuf/proto/, stage R1)
    "--raft": ("link-lean-first-raft.txt", "go_etcd_io.raft.v3",
               "go_etcd_io.raft.v3.Assumptions",
               "The Raft proof (raft v3.7 plus the read-index fix)", [""]),
    # the witness experiment (the parallel tree RaftWitness/, project raft-witness of
    # etc/goose.py): its Raft proof, and the key-value store on it (project kvwitness). A spec
    # of the part (`RaftWitness/Spec/`) is linked in place of the main tree's of the same
    # function (its copies of `slices.Sort`, the `proto` axioms, ...); the other callees (`fmt`'s,
    # lintest's, porcupine's) are the main tree's.
    "--raft-witness": ("link-lean-first-raft-witness.txt", "go_etcd_io.raft.v3",
                       "go_etcd_io.raft.v3.Assumptions",
                       "The Raft proof of the witness experiment (raft v3.7 plus the read-index "
                       "fix and witness support, `RaftWitness/`)", ["", "RaftWitness"]),
    "--kvwitness": ("link-lean-first-kvwitness.txt",
                    "github_com.mit_pdos.etcd_grove.examples.kvwitness go_etcd_io.raft.v3 "
                    "github_com.mit_pdos.etcd_grove.examples.lintest github_com.anishathalye.porcupine",
                    "github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions",
                    "The key-value store example's proofs on the witness raft (`examples/kvwitness`, "
                    "`RaftWitness/`)", ["", "RaftWitness"]),
    # porcupine (third_party/porcupine), the linearizability checker of etcd's robustness tests
    "--porcupine": ("link-lean-first-porcupine.txt", "github_com.anishathalye.porcupine",
                    "github_com.anishathalye.porcupine.Assumptions",
                    "Porcupine's proofs (`third_party/porcupine`: the checker, its entry points)",
                    [""]),
    # the generic driver over porcupine (examples/lintest), over porcupine's (`@`)
    "--lintest": ("link-lean-first-lintest.txt",
                  "github_com.mit_pdos.etcd_grove.examples.lintest github_com.anishathalye.porcupine",
                  "github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions",
                  "The porcupine driver's proofs (`examples/lintest`)", [""]),
    # its instance, a counter under a mutex (examples/lintest/counter), over the driver's (`@`)
    "--lintest-counter": ("link-lean-first-lintest-counter.txt",
                          "github_com.mit_pdos.etcd_grove.examples.lintest.counter "
                          "github_com.mit_pdos.etcd_grove.examples.lintest "
                          "github_com.anishathalye.porcupine",
                          "github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions",
                          "The porcupine driver's instance's proofs (`examples/lintest/counter`)",
                          [""]),
    # the log-applied register (examples/lintest/logkv): writes take effect in the apply
    # goroutine; over the driver's (`@`)
    "--lintest-logkv": ("link-lean-first-lintest-logkv.txt",
                        "github_com.mit_pdos.etcd_grove.examples.lintest.logkv "
                        "github_com.mit_pdos.etcd_grove.examples.lintest "
                        "github_com.anishathalye.porcupine",
                        "github_com.mit_pdos.etcd_grove.examples.lintest.logkv.Assumptions",
                        "The log-applied register's proofs (`examples/lintest/logkv`)",
                        [""]),
    # the linearizability instance over the robustness tester's KV workload (examples/linkvtxn,
    # notes/linkv-txn-plan.md): its porcupine model (stage E), `Apply` (stage F), its generator,
    # `Check` (over the driver's, `@`) and `Main` (over the server's, v3rpc's and the client's, `@`;
    # stage G)
    "--linkvtxn": ("link-lean-first-linkvtxn.txt",
                   "github_com.mit_pdos.etcd_grove.examples.linkvtxn "
                   "github_com.mit_pdos.etcd_grove.examples.lintest "
                   "github_com.anishathalye.porcupine",
                   "github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions",
                   "The KV-workload linearizability instance's proofs (`examples/linkvtxn`)", [""]),
    # the three-member instance under network partitions (examples/linkv3p, notes/partition-plan.md):
    # its `startMember` (putget3's plus the member's gRPC server, over the server's, v3rpc's and
    # grpc's, `@`), `newClient` (over the client's `New`, `@`), `partitioner` (over the server's
    # `MemberID`/`CutPeer`/`MendPeer`, `@`), `Apply` (over linkvtxn's `Apply`, `@`), `Check` (over
    # the driver's and linkvtxn's, `@`; notes/linkv3p-txn-plan.md) and `Main`
    "--linkv3p": ("link-lean-first-linkv3p.txt",
                  "github_com.mit_pdos.etcd_grove.examples.linkv3p "
                  "github_com.mit_pdos.etcd_grove.examples.linkvtxn "
                  "github_com.mit_pdos.etcd_grove.examples.lintest "
                  "github_com.anishathalye.porcupine",
                  "github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions",
                  "The partitioned three-member instance's proofs (`examples/linkv3p`)", [""]),
    # the watch example (examples/watchkv, D23): its functions, the watch's options, and `Main`
    # (over the server's, v3rpc's, the client's and `context`'s, `@`)
    "--watchkv": ("link-lean-first-watchkv.txt",
                  "github_com.mit_pdos.etcd_grove.examples.watchkv",
                  "github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions",
                  "The watch example's proofs (`examples/watchkv`)", [""]),
    # the authentication example (examples/authkv, the auth plan's E2b): its pure checks and
    # `Main` (not proved yet)
    "--authkv": ("link-lean-first-authkv.txt",
                 "github_com.mit_pdos.etcd_grove.examples.authkv",
                 "github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions",
                 "The authentication example's proofs (`examples/authkv`)", [""]),
    # the cache watch example (examples/cachekv): watchkv's functions, the cache watch's options,
    # and `Main` (over the server's, v3rpc's, the client's, `context`'s and the cache's, `@`)
    "--cachekv": ("link-lean-first-cachekv.txt",
                  "github_com.mit_pdos.etcd_grove.examples.cachekv",
                  "github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions",
                  "The cache watch example's proofs (`examples/cachekv`)", [""]),
    # the client Kubernetes' etcd3 store calls (client/v3/kubernetes, notes/k8s-etcd3-plan.md
    # phase 3), with the clientv3 functions it calls (as linkvtxn's, under its assumptions)
    "--k8s": ("link-lean-first-k8s.txt",
              "go_etcd_io.etcd.client.v3.kubernetes",
              "go_etcd_io.etcd.client.v3.kubernetes.Assumptions",
              "The Kubernetes client's proofs (`client/v3/kubernetes`)", [""]),
    # the Kubernetes etcd3 store's linearizability driver (examples/k8setcd3,
    # notes/k8s-etcd3-plan.md phase 6): its Go model of the store and porcupine model, its codec,
    # `Apply` (over the store's, `@`), its generator, `Check` (over the porcupine driver's, `@`),
    # the seeding and `Main` (over the shared start's, the clients' and the store's, `@`)
    "--k8setcd3": ("link-lean-first-k8setcd3.txt",
                   "github_com.mit_pdos.etcd_grove.examples.k8setcd3 "
                   "github_com.mit_pdos.etcd_grove.examples.lintest "
                   "github_com.anishathalye.porcupine",
                   "github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions",
                   "The Kubernetes etcd3 store's linearizability driver's proofs (`examples/k8setcd3`)", [""]),
    # the Kubernetes etcd3 store (k8s.io/apiserver/pkg/storage/etcd3 and storage,
    # notes/k8s-etcd3-plan.md phases 1 and 4), over the kubernetes client (`@`)
    "--k8s-etcd3": ("link-lean-first-k8s-etcd3.txt",
                    "k8s_io.apiserver.pkg.storage.etcd3 k8s_io.apiserver.pkg.storage",
                    "k8s_io.apiserver.pkg.storage.etcd3.Assumptions",
                    "The Kubernetes etcd3 store's proofs (`k8s.io/apiserver/pkg/storage/etcd3`)", [""]),
    # the Kubernetes watch cache's reads (k8s.io/apiserver/pkg/storage/cacher, its store and
    # progress requester; KEP-6404, notes/kep-6404-plan.md), over the B-tree's (`@`)
    "--cacher": ("link-lean-first-cacher.txt",
                 "k8s_io.apiserver.pkg.storage.cacher k8s_io.apiserver.pkg.storage.cacher.store "
                 "k8s_io.apiserver.pkg.storage.cacher.progress",
                 "k8s_io.apiserver.pkg.storage.cacher.Assumptions",
                 "The Kubernetes watch cache's proofs (`k8s.io/apiserver/pkg/storage/cacher`)", [""]),
    # the examples' shared start (examples/common, D33): a member's configuration and server
    # (over the server's, `@`), its gRPC service (over v3rpc's, `@`) and a client (over the
    # client's `New`, `@`), which the examples' Links take as `@` callees
    "--common": ("link-lean-first-common.txt",
                 "github_com.mit_pdos.etcd_grove.examples.common",
                 "github_com.mit_pdos.etcd_grove.examples.common.Assumptions",
                 "The examples' shared start's proofs (`examples/common`)", [""]),
}
# The mode whose results are put in a namespace of their own (see the docstring).
NAMESPACED = {"--backend": "backend", "--client": "client", "--concurrency": "concurrency", "--leasing": "leasing", "--recipes": "recipes", "--v3lock": "v3lock", "--v3election": "v3election",
              "--txn": "txn", "--porcupine": "porcupine", "--lintest": "lintest",
              "--lintest-counter": "lintest", "--lintest-logkv": "lintest", "--linkv3p": "linkv3p", "--linkvtxn": "linkvtxn", "--watchkv": "watchkv", "--authkv": "authkv", "--cachekv": "cachekv", "--common": "common", "--k8s": "kubernetes", "--k8s-etcd3": "k8s", "--cacher": "cacher", "--k8setcd3": "k8setcd3", "--apply": "apply", "--v3rpc": "v3rpc", "--read": "read"}
# The Links a mode imports for the callees' results they already define (see "Reuse" above), by
# their module below `Proof/`, beside those of its `@` callees.
REUSES = {"--server": ["Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Link"]}
# The modules a mode imports beside its proofs (its package's translation, through its `Base`,
# while no proof of the package is linked yet: the v3rpc package's unit 0).
EXTRA_IMPORTS = {"--v3rpc": ["Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base"],
                 # (rafthttp stage 6f) the HTTP boundary's axioms and Perennial's linked results
                 # rafthttp's proofs take as terms (`=` callees)
                 "--server": ["Proof.net.http.Axioms", "Perennial.Proof.time.Link",
                              "Perennial.Proof.sync.Link", "Perennial.Proof.context.Link",
                              "Perennial.Proof.strings.Link",
                              "Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Lemmas",
                              # (rafthttp stage 7d) the snapshot sender's: `bytes.Buffer.Write`'s
                              # axiom, net/http's errors not `errMemberRemoved`
                              "Proof.bytes.Buffer__Write",
                              "Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NetErr",
                              # (2026-10-27) the node API's results at the server's storage model
                              # (`=srvApi_wp_*` callees)
                              "Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeApiLink"]}
# The modes whose specs are stated over the clients' model of etcd (the class `EtcdModel`,
# `cache/v3/EtcdModel.lean`, the vertical slice's unit V1): their sections take it as a variable.
EM_MODES = {"--cache", "--concurrency", "--leasing", "--recipes", "--v3lock", "--v3election"}
mode = LEAN_FIRST.get(sys.argv[1]) if len(sys.argv) > 1 else None
if mode is None:
    sys.exit(f"usage: etc/gen-link.py MODE [--skip-unproved] (modes: {' '.join(LEAN_FIRST)})")
# The modes whose results rest on porcupine's `checkSingle`, which shares the model's state values
# in non-atomic invariants (`Shared.lean`) of iris-lean's camera `NaInvG GF`, not yet in
# Perennial's `allG`: their sections assume the instance (`notes/STATUS.md`, "Porcupine").
NA_MODES = {"--porcupine", "--lintest", "--lintest-counter", "--lintest-logkv", "--kv", "--linkv3p",
            "--linkvtxn", "--kvwitness", "--k8setcd3"}
em = (("variable [EM : EtcdModel GF]\n" if sys.argv[1] in EM_MODES else "")
      + ("variable [NaInvG GF]\n" if sys.argv[1] in NA_MODES else ""))
cache = mode is not None
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.normpath(os.path.join(here, ".."))

# function name -> the module path below Spec/ and Proof/ (`go_etcd_io.raft.v3.tracker.NewInflights`)
# (a bare `<fn>` shared by two packages, as `Error` of `rpctypes` and `status`, is
# ambiguous: such a function is named `<last component of pkg>_<fn>` only; and if two packages
# share their last component too, as `cache/v3` and `client/v3` for `New`,
# `<last two components>_<fn>`)
# (`prefix`: the module root of a spec outside `Spec/`, a part's; none now)
where, prefix, ambiguous = {}, {}, set()
# every package's spec of a bare `<fn>` (module path, root prefix): an ambiguous bare name in a
# mode's list is the one of the mode's own packages (below)
candidates = {}
for mroot in (mode[4] if cache else [""]):
    spec_dir = os.path.join(root, mroot, "Spec")
    for dp, _, fs in os.walk(spec_dir):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), spec_dir)[:-len(".lean")]
                *pkg, stem = rel.split(os.sep)
                candidates.setdefault(stem, []).append(
                    (".".join(pkg + [stem]), mroot + "." if mroot else ""))
                qual = pkg[-1] + "_" + stem
                if qual in where and where[qual] == ".".join(pkg + [stem]) and prefix[qual] == "":
                    # the same Go function in a later root (a part's, as the server's
                    # `EtcdDeps` was, etcd's raft v3.7 under the verified raft's Go path): the
                    # later root's spec is the one this mode links
                    prefix[qual] = prefix[stem] = mroot + "."
                    continue
                if qual in where and where[qual] != ".".join(pkg + [stem]):
                    # two packages with the same last component (`cache/v3` and `client/v3`
                    # both have a `New`): each is named `<last two components>_<fn>`
                    # (`cache_v3_New`, `client_v3_New`), and `<last component>_<fn>` by neither
                    other = where[qual].split(".")
                    for opkg, ostem, oprefix in ((other[:-1], other[-1], prefix[qual]),
                                                 (pkg, stem, mroot + "." if mroot else "")):
                        q2 = opkg[-2] + "_" + opkg[-1] + "_" + ostem
                        where[q2], prefix[q2] = ".".join(opkg + [ostem]), oprefix
                    ambiguous.add(qual)
                    ambiguous.add(stem)
                    continue
                assert qual not in where, f"two specs for {qual}"
                where[qual] = ".".join(pkg + [stem])
                prefix[qual] = mroot + "." if mroot else ""
                if stem in where:
                    ambiguous.add(stem)
                where[stem], prefix[stem] = where[qual], prefix[qual]
for name in ambiguous:
    del where[name]
# An ambiguous bare `<fn>` in a mode's list (the apply package's `Apply`, which linkvtxn's `Apply`
# shares) is the function of the mode's own packages (`LEAN_FIRST`'s opens) if exactly one
# candidate is in one of them: the qualified names stay the only ones elsewhere.
own_pkgs = set((mode[1] if cache else "").split())
for name in ambiguous:
    own = [c for c in candidates.get(name, [])
           if ".".join(c[0].split(".")[:-1]) in own_pkgs]
    if len({c[0] for c in own}) == 1:
        where[name], prefix[name] = own[-1]


def spec_file(fn):
    return os.path.join(root, prefix[fn].rstrip("."), "Spec", *where[fn].split(".")) + ".lean"


def proof_module(fn):
    return f"{prefix[fn]}Proof.{where[fn]}"

fns, callees, external, pending = [], {}, set(), set()
# the mode's functions and their callees (`etc/link-lean-first-<mode>.txt`)
with open(os.path.join(here, mode[0])) as f:
    for line in f:
        line = line.split("#")[0].strip()
        if not line:
            continue
        fn, _, cs = line.partition(":")
        fn = fn.strip()
        if fn not in callees:
            fns.append(fn)
        if cs.strip() == "@":
            # linked in its own package's `Link.lean` (the btree): imported, not emitted
            external.add(fn)
            cs = ""
        if cs.strip() == "?":
            # specified, not proved yet (a later unit's): a hypothesis of the results that
            # reach it (`section links_pending`)
            pending.add(fn)
            cs = ""
        callees[fn] = cs.split()
fns.sort()

# `--skip-unproved`: leave out the functions with no proof file yet, and those reaching one
skipped = set()
if cache and "--skip-unproved" in sys.argv[2:]:
    def proved(fn):
        return fn in where and os.path.exists(
            os.path.join(root, prefix[fn].rstrip("."), "Proof", *where[fn].split(".")) + ".lean")
    skipped = {fn for fn in fns if not proved(fn)}
    changed = True
    while changed:
        changed = False
        for fn in fns:
            if fn not in skipped and any(c in skipped for c in callees[fn]):
                skipped.add(fn)
                changed = True
    fns = [fn for fn in fns if fn not in skipped]

spec = {}
for fn in fns:
    src = open(spec_file(fn)).read()
    m = re.search(r"^abbrev ([\w.«»']+)\.spec\b", src, re.M)
    # the namespaces below `EtcdGrove` the spec is declared in (`btree` for the btree's)
    nss = re.findall(r"^namespace (\S+)", src, re.M)
    inner = nss[nss.index("EtcdGrove") + 1:] if "EtcdGrove" in nss else []
    spec[fn] = ".".join(inner + [m.group(1)])

# The specs stated at `HeapGS HasLC.hasLC GF` (the ghost state holds an invariant).
haslc = {fn for fn in fns
         if "HeapGS HasLC.hasLC" in open(spec_file(fn)).read()}


nsd = NAMESPACED.get(sys.argv[1])


def result(fn):
    """`a.b.M` ↦ `a.b.wp_M`, `F` ↦ `wp_F` (in a namespaced mode: relative to its namespace, a
    clientv3 function's with the prefix `v3.`)."""
    parts = spec[fn].split(".")
    last = parts[-1].strip("«»")
    if nsd:
        if parts[0] == nsd:
            parts = parts[1:]
        elif where[fn].split(".")[:-1] == ["go_etcd_io", "etcd", "client", "v3"]:
            parts = ["v3"] + parts
    return ".".join(parts[:-1] + [f"wp_{last}"])


def specref(fn):
    """The spec's name as the Link refers to it: in a namespaced mode, below `EtcdGrove`."""
    return f"EtcdGrove.{spec[fn]}" if nsd else spec[fn]


def external_link(fn):
    """The `Link` module that links the external callee `fn`: its package's, or the nearest
    enclosing package's that has one (raft's `Link.lean` links `raftpb`'s functions too), in the
    module root of its spec (a part's, `RaftWitness/`)."""
    parts = where[fn].split(".")[:-1]
    pre = prefix[fn]
    while parts:
        if os.path.exists(os.path.join(root, pre.rstrip("."), "Proof", *parts, "Link.lean")):
            return pre + "Proof." + ".".join(parts + ["Link"])
        parts = parts[:-1]
    return pre + "Proof." + ".".join(where[fn].split(".")[:-1] + ["Link"])

# **Reuse**: the callees whose result a Link this one imports already defines (same full name):
# imported from there (`reused`: fn -> the Link's module), not emitted.
reused = {}
if cache:
    def link_file(mod):
        return os.path.join(root, *mod.split(".")) + ".lean"

    def link_namespace(src):
        nss = re.findall(r"^namespace (\S+)", src, re.M)
        inner = nss[nss.index("EtcdGrove") + 1:] if "EtcdGrove" in nss else []
        return ".".join(["EtcdGrove"] + inner)

    todo = sorted({external_link(fn) for fn in external}
                  | set(REUSES.get(sys.argv[1], [])))
    links, seen_links = [], set()
    while todo:
        mod = todo.pop(0)
        if mod in seen_links or not os.path.exists(link_file(mod)):
            continue
        seen_links.add(mod)
        src = open(link_file(mod)).read()
        links.append((mod, link_namespace(src), set(re.findall(r"^theorem (\S+)", src, re.M))))
        todo.extend(re.findall(r"^public import ((?:RaftWitness\.)?Proof\.\S+\.Link)$", src, re.M))
    here_ns = "EtcdGrove" + (f".{nsd}" if nsd else "")
    # an `@` callee's result named, in its Link, by the name `result` gives but in another
    # namespace than this one's (the client's `v3.clientv3.wp_New`, in `EtcdGrove.client`, called
    # from linkvtxn's): referred to with that namespace (`client.v3.clientv3.wp_New`)
    ext_ref = {}
    for fn in external:
        mod = external_link(fn)
        if not os.path.exists(link_file(mod)):
            continue
        src = open(link_file(mod)).read()
        ns = link_namespace(src)
        rel = ns[len("EtcdGrove."):] if ns.startswith("EtcdGrove.") else ""
        if (ns != here_ns and rel and result(fn) in re.findall(r"^theorem (\S+)", src, re.M)
                and not result(fn).startswith(rel + ".")):
            ext_ref[fn] = f"{rel}.{result(fn)}"
    for fn in fns:
        if fn in external or fn in pending:
            continue
        full = f"{here_ns}.{result(fn)}"
        for mod, ns, thms in links:
            if any(f"{ns}.{t}" == full for t in thms):
                reused[fn] = mod
                break

order, seen = [], set()


def visit(fn):
    if fn in seen:
        return
    seen.add(fn)
    for c in callees[fn]:
        if c.startswith("="):
            continue
        visit(c)
    order.append(fn)


for fn in fns:
    visit(fn)

if cache:
    listfile, opens, assumptions, what, _ = mode
    out = [f"""/-
{what}, every proof instantiated with its
callees' results. All of them are Lean-first, listed with their callees in
`etc/{listfile}`. Generated by `etc/gen-link.py {sys.argv[1]}` -- do not edit by
hand.

`#print axioms` on a result is its trust base.""" + ("\n\n" + textwrap.fill(
        "Generated with `--skip-unproved`: not linked yet (no proof file, or reaching such a "
        "function): " + ", ".join(f"`{fn}`" for fn in sorted(skipped)) + ".", 96,
        break_on_hyphens=False) if skipped else "") + """
-/""", "module", ""]
    out.extend(f"public import {proof_module(fn)}" for fn in fns
               if fn not in external and fn not in pending and fn not in reused)
    out.extend(f"public import {m}" for m in EXTRA_IMPORTS.get(sys.argv[1], []))
    out.extend(f"public import {prefix[fn]}Spec.{where[fn]}" for fn in fns if fn in pending)
    # an `@` callee whose package has no `Link.lean` of its own is linked by one of the other
    # imported Links (raft's links protobuf-go's `proto` axioms, which the store names)
    out.extend(sorted({"public import " + external_link(fn) for fn in external
                       if os.path.exists(os.path.join(root, *external_link(fn).split(".")) + ".lean")}
                      | {f"public import {mod}" for mod in reused.values()}))
    out.append(f"""
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
""" + (f"namespace {nsd}\n" if nsd else "") + f"""
open Iris Iris.BI{(' ' + opens) if opens else ''}
""")
    out.append(f"""section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {{hlc : HasLC}} {{GF : BundledGFunctors}} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : {assumptions}]
{em}""")
    def hyp(fn):
        return "h_" + fn

    def arg(fn, c):
        if c.startswith("="):
            # a term given as is (`=http.respWrite_ok`): a boundary statement's axiom, or another
            # library's linked result, which no spec file of a mode names
            return c[1:]
        if c in pending:
            return hyp(c)
        if c in blocked:
            # a result of `links_pending`: applied to the pending hypotheses (section variables
            # are not applied automatically)
            return "(" + result(c) + " " + " ".join(hyp(p) for p in sorted(pending)) + ")"
        # a callee's result named like the theorem's last component (`leaseCache.wp_evalCmp`
        # calling `wp_evalCmp`; `bootstrappedRaft.wp_newRaftNode` calling `wp_newRaftNode`,
        # 2026-10-16) would resolve to the theorem itself: qualify it
        r = result(c)
        if c in ext_ref:
            return ext_ref[c]
        if "." in result(fn) and r == result(fn).split(".")[-1]:
            return f"EtcdGrove.{nsd}.{r}" if nsd else f"EtcdGrove.{r}"
        return r

    def emit_cache(fn):
        args = " ".join(arg(fn, c) for c in callees[fn])
        body = f"{specref(fn)}.wp_proof" + (f" {args}" if args else "")
        # the specs with ghost state (the store's) take `[AllG GF]`
        src = open(spec_file(fn)).read()
        allg = " [AllG GF]" if "[AllG GF]" in src and fn not in blocked else ""
        # the key-value store's specs take its storage registry
        allg += " [KVStor GF]" if "[KVStor GF]" in src else ""
        # mvcc's index specs use the btree through the cache's interface (its assumptions), and
        # so does every result that links one of them
        allg += " [go_etcd_io.etcd.cache.v3.Assumptions]" if fn in cache_assumptions else ""
        # the client's watch specs are stated at the server's model (the watch slice's unit W-C:
        # `v3rpc.etcdModelOfServer`), under the v3rpc package's assumptions too
        allg += f" [{SRV_ASSUMPTIONS}]" if fn in srv_assumptions else ""
        # ... or, stated over any raft storage model, that (the store's transport)
        if "[KVStor GF]" not in src and "[StorageModel GF]" in src:
            allg += " [StorageModel GF]"
        # ... or over the `MemoryStorage` registry (the server's `NewServer`, 2026-10-16: its raft
        # storage is a `MemoryStorage`, `memStorageModel` under the registry's name)
        elif "[MemStorReg GF]" in src:
            allg += " [MemStorReg GF]"
        allg += "".join(" " + premise_binder(p) for p in SEM_PREMISES if p in premises[fn])
        return (f"theorem {result(fn)}{allg} :\n    {specref(fn)}.spec (GF := GF) (hG := hG) :=\n"
                f"  {body}\n")

    cache_assumptions = set()
    for fn in order:
        if fn in reused:
            # a callee whose result an imported Link defines: as an `@` callee, the cache's
            # assumptions if that result takes them
            if re.search(r"^theorem " + re.escape(result(fn)) +
                         r" \[go_etcd_io\.etcd\.cache\.v3\.Assumptions\]",
                         open(link_file(reused[fn])).read(), re.M):
                cache_assumptions.add(fn)
            continue
        if fn in external:
            # an `@` callee whose result (in its own package's `Link.lean`) takes the cache's
            # assumptions (mvcc's range read and write path, through the index's btree): so does
            # every result linking it
            link = os.path.join(root, prefix[fn].rstrip("."), "Proof",
                                *where[fn].split(".")[:-1], "Link.lean")
            # the result as that Link names it: in its own namespace (the txn package's
            # `wp_Txn`, which a namespaced mode calls `txn.wp_Txn`)
            names = {result(fn), result(fn).split(".", 1)[-1]}
            if os.path.exists(link) and any(re.search(
                    r"^theorem " + re.escape(n) +
                    r" \[go_etcd_io\.etcd\.cache\.v3\.Assumptions\]", open(link).read(), re.M)
                    for n in names):
                cache_assumptions.add(fn)
            continue
        if ("variable [go_etcd_io.etcd.cache.v3.Assumptions]" in open(spec_file(fn)).read()
                or any(c in cache_assumptions for c in callees[fn])):
            cache_assumptions.add(fn)

    # the semantic premises each result takes (`SEM_PREMISES`): its proof's, or a callee's
    def proof_file(fn):
        return os.path.join(root, prefix[fn].rstrip("."), "Proof", *where[fn].split(".")) + ".lean"

    def premise_binder(p):
        return "[" + p + "]"

    premises = {}
    for fn in order:
        ps = set()
        if fn in reused or fn in external:
            link = (link_file(reused[fn]) if fn in reused else
                    os.path.join(root, *external_link(fn).split(".")) + ".lean")
            names = {result(fn), result(fn).split(".", 1)[-1]}
            if os.path.exists(link):
                src = open(link).read()
                for n in names:
                    m = re.search(r"^theorem " + re.escape(n) + r"( \[[^:]*):", src, re.M)
                    if m:
                        ps |= {p for p in SEM_PREMISES if premise_binder(p) in m.group(1)}
        else:
            if fn not in pending and os.path.exists(proof_file(fn)):
                src = open(proof_file(fn)).read()
                ps |= {p for p in SEM_PREMISES
                       if premise_binder(p.split(".")[-1]) in src or premise_binder(p) in src}
            for c in callees[fn]:
                ps |= premises.get(c, set())
        premises[fn] = ps

    # the results whose specs take the v3rpc package's assumptions besides the mode's (the
    # client's watch specs, at the server's model), and every result linking one of them
    srv_assumptions = set()
    if assumptions != SRV_ASSUMPTIONS:
        for fn in order:
            if fn in reused or fn in external:
                continue
            if (f"variable [srv_sem : {SRV_ASSUMPTIONS}]" in open(spec_file(fn)).read()
                    or any(c in srv_assumptions for c in callees[fn])):
                srv_assumptions.add(fn)

    # the results that reach a pending function, and the pending functions themselves: emitted
    # last, with the pending specs as hypotheses
    blocked = set(pending)
    for fn in order:
        if any(c in blocked for c in callees[fn]):
            blocked.add(fn)
    generic = [fn for fn in order if fn not in haslc and fn not in external and fn not in blocked
               and fn not in reused]
    special = [fn for fn in order if fn in haslc and fn not in external and fn not in blocked
               and fn not in reused]
    assert all(c not in haslc for fn in generic for c in callees[fn])
    out.extend(emit_cache(fn) for fn in generic)
    out.append("end links\n")
    if special:
        out.append(f"""/-! The specs stated at `HeapGS HasLC.hasLC GF`: those using channels, `sync.Once` or
`context` (Perennial states them there: their invariants need later credits). -/
section links_hasLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : {assumptions}]
{em}""")
        out.extend(emit_cache(fn) for fn in special)
        out.append("end links_hasLC\n")
    later = [fn for fn in order if fn in blocked and fn not in pending]
    if later:
        hyps = "\n".join(f"variable ({hyp(fn)} : {specref(fn)}.spec (GF := GF) (hG := hG))"
                         for fn in sorted(pending))
        names = " ".join(hyp(fn) for fn in sorted(pending))
        out.append(f"""/-! The results that reach a function specified but not proved yet (a later unit's):
its spec is a hypothesis (`h_<fn>`) of each of them. -/
section links_pending
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : {assumptions}]
{em}{hyps}
include {names}
""")
        out.extend(emit_cache(fn) for fn in later)
        out.append("end links_pending\n")
    out.append((f"end {nsd}\n" if nsd else "") + "end EtcdGrove\nend Perennial")
    print("\n".join(out))
    sys.exit(0)
