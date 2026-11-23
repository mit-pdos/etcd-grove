/-
**The address part, restored for the single-process theorems** (2026-11-23, etcd-grove#28,
`notes/single-process-restore.md`): removed at the net swap (etcd-dist D2, 2026-11-22), when its only users,
the single-process closed theorems, retired; restored, narrowed, for them (`etcd_safe_single_process`,
`k8s_safe_single_process`, `etcd_leaseexpiryN_safe_single_process`). Since the swap `net` is the part
`Net/`'s, over the net extension, and `netAddrFree a` a definition: `addrClaim a` (axiomatized), the net
extension's listening token `netLisTok a` and `addrOk a` (`Proof/net/InvNet.lean`). Program start now hands
out, for each address of `As`, only the two axiomatized rights nothing else produces: `addrClaim a` (where it
handed out `netAddrFree a`) and `httpProtoFree a`, as before. The listening token is never this axiom's: it
is the net extension's, from its start resources (`extsGlobalStart`, `netStart`), so the axiom and the
extension hand out disjoint rights. Below, "`netAddrFree a`" handed out by start reads `addrClaim a`.

Program start's rights (decision D19d, 2026-10-18): the right to register each of some metric
names with prometheus's default registry (`prometheus.nameFree`, D16) and to listen on each of
some network addresses (`netAddrFree`, item 4). Both are abstract exclusive resources the
program's specs consume (`MustRegister.spec`, `Listen.spec`) and that nothing in the logic
produces: in Go they hold because the program starts with an empty registry (but for what its
unverified code registers) and owns its addresses, a fact of the initial world. Perennial's
adequacy theorem gives a proof only the extensions' start resources, the package-state map and the main
thread's token, and no extension here models the registry or the network, so the rights cannot be
allocated in the logic. A hypothesis `⊢ |==> nameFree n` of a closed theorem could be used twice
(and two registrations of one name would then not panic: false of Go, the theorem vacuous,
D19a).

**The trust boundary: `goose_adequacy_start`.** Perennial's `goose_adequacy`, whose WP proof
also receives, once, `nameFree n` for each name of `Ns` and `netAddrFree a` for each address of
`As` (distinct), for a program `e` of which `namesUnclaimed e Ns` and `addrsUnclaimed e As` hold.
Why it is true of Go: in a run of `e`, every registration of a name of `Ns` and every listen on
an address of `As` is made by code whose spec consumes the right (`namesUnclaimed`,
`addrsUnclaimed`: nothing else registers or binds them), each right exists once in the proof (the
premise receives one of each), and each consumption is one registration (one listen); so no name
of `Ns` is registered twice and no address of `As` bound twice, and (prometheus-id-collision,
2026-11-20) since the label-free descriptor IDs of the names of `Ns` are pairwise distinct
(`hNsIds`: `prometheus.descIdsDistinct Ns`, decided by the kernel for each program's names),
registering one name of `Ns` registers no other's ID, which is what `MustRegister`'s and
`Listen`'s specs need. The rest is `goose_adequacy`. (Until then the axiom took any distinct names,
and was false: two names can share an ID, and the registry refuses the second,
`notes/axiom-review/prometheus-id-collision.md`.)

(D39a, 2026-10-23) It also receives `httpProtoFree a` for each address of `As`: a purely ghost
right, the only source of an address's HTTP protocol (`http.reserve`), so each address's protocol
is fixed once in a run (the model of `http.register`'s D38c: a global ghost map from addresses to
saved protocols, now set by `reserve`). No Go operation is involved: nothing to check of `e`.
(2026-11-03, the WAL's API; sweep repairs 1, W3/W4, 2026-11-07) It also receives `dataDirFresh dd`
for each data directory of `Ds`, for a program of which `dataDirsAbsent e Ds` holds: the
directories are one directory each for the whole run and reached only through their strings, absent
or empty at start, pairwise disjoint, and touched only by the operations whose specs state their
effects. The verified code's first `bootstrap` of `dd` consumes the right. So each data directory
of `Ds` is bootstrapped fresh at most once in a run, over an empty backend, which `bootstrap`'s
contract needs (`wal.Exist(dir)` false: `bootstrapNewWAL`; no backend file: `HD`, `HmEmpty`).
(Sweep repairs 1, W5) The addresses of `As` are numeric loopback literals (`hAsLit`, decidable; loopback since 2026-11-14, so no proxy), so each
names one socket and the per-string rights are per-socket. (Sweep repairs 1, B4) For a program of
which `verifyEnvOff e` holds (`ETCD_VERIFY` off for the run), it also receives `envVerifyOff`,
which the backend's lock checks and `VerifyBackendConsistency` take.
Why it is once only: nothing else produces `nameFree`, `netAddrFree` or `httpProtoFree` (axiomatized
predicates, `Registry.lean`, `InvNet.lean`; no axiom or definition gives one), so the rights exist
only where this axiom's premise hands them out: once, to the one WP proof of one execution, under
the ghost state `goose_init` allocates for it. The axiom is about executions (its conclusion is
`goose_adequacy`'s), not an entailment: it cannot be applied inside a proof to obtain rights.

Satisfiable whatever the semantics: with `nameFree`, `netAddrFree` and `httpProtoFree` read as `True` (no axiom
says either is exclusive) and the names-only `MustRegister` and `Listen` as diverging functions,
the premise is `goose_adequacy`'s premise and the conclusion its conclusion.

`namesUnclaimed` and `addrsUnclaimed` are axiomatized propositions (facts of the Go program and of
its environment that the model cannot state, hypotheses of a closed theorem: pure, D19a); the
adequacy example's are checked from the Go source (`notes/decisions.md`, D19d).

(2026-11-08 to 2026-11-17) It also received `fileHolds f ∅` for fresh database files
(`goose_adequacy_start_files`, with the premise `dbFilesAbsent`): removed in S3e, when the backend's
`fileHolds` became concrete file-extension ghost state (the claim on the file's name in the tree's
shared mode), which an axiom must not hand out beside the tree `extsLocalStart` gives; the fresh files
are derived from the tree (`Proof/runtime/StartFiles.lean`, `goose_adequacy_start_files`, a theorem).

A design choice D19d leaves to the user: the alternative is an extension whose initial world holds
the free addresses and the empty registry (`extsGlobalStart` the rights, `nameFree`/`netAddrFree` its
ghost state, `MustRegister`/`Listen` its operations), a Perennial change proposed in
`notes/decisions.md`, D19d; with it this axiom goes.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.AdequacyAlong
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.net.InvNet
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDir
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

/-- **The name `n` is the verified code's to register** (`prometheus.namesUnclaimed`'s claim of one
name). -/
axiom prometheus.nameUnclaimed [GooseExts] (e : Expr) (n : GoString) : Prop

/-- **The names `Ns` are the verified code's to register** (a fact of the Go program `e`
translates, checked from its source): no collector the default registry holds at start
(client_golang's `go_*` and `process_*`), and no code of the program whose behaviour this
repository does not verify (an untranslated initializer, a names-only function, the runtime),
registers with prometheus's default registry a collector with a descriptor named `n ∈ Ns`, or
with `n`'s label-free descriptor's ID, or with that collector ID. (2026-11-08: stated name by name,
`prometheus.nameUnclaimed`, the same claim, so that a program with no names has it; until then an
axiomatized proposition of the list.) -/
def prometheus.namesUnclaimed [GooseExts] (e : Expr) (Ns : List GoString) : Prop :=
  ∀ n ∈ Ns, prometheus.nameUnclaimed e n

/-- **The data directory `d` is the program's, fresh, and untouched by anything else**
(`dataDirsAbsent`'s clauses 1-3 of one directory; 2026-11-08, stated directory by directory, so that
a program with no data directory has `dataDirsAbsent`). -/
axiom dataDirAbsent [GooseExts] (e : Expr) (d : GoString) : Prop

/-- **The data directories `d` and `d'` are disjoint**: neither is inside the other
(`dataDirsAbsent`'s clause 4 of two directories). -/
axiom dataDirsApart (d d' : GoString) : Prop

/-- **The data directories `Ds` are the program's, fresh, and untouched by anything else** (a fact
of the environment a run of `e` is in, and of `e`'s unverified code; sweep repairs 1, W3/W4, the
user's decision via etcd-grove-82, 2026-11-07):
1. each string `d` of `Ds` names, from when that directory exists, one and the same directory for
   the rest of the run. The working directory does not change. Every path by which the program
   reaches a file in that directory is lexically under `d` or under `filepath.Abs(d)` after
   `filepath.Clean`, with no `..` component escaping it. No other path reaches it: no symbolic
   link, alias spelling, `/proc` link or bind mount;
2. when `e` starts, each `d` is absent, or an empty directory;
3. no other process, and no code of `e` beyond the operations with trust-boundary specs here (the
   `wal`, `snap`, backend/bbolt and `storage` operations, `EtcdServer.purgeFile`, the bootstrap
   (`bootstrapContract`, `bootstrapRestartContract`) and the `fileutil` helpers they run:
   `TouchDirAll`, `IsDirWriteable`, `RemoveMatchFile` (`bootstrap.go:219-240`), the `PurgeFile*`
   goroutines), opens, writes, truncates, locks, links, renames, removes or changes the mode of a
   file inside a directory of `Ds`, by any path. The files the specs model change only as the specs
   say; the other files those operations create (`.touch`, `0.tmp`, `wal.tmp`, the db temp file,
   `.broken`) are their own scratch;
4. the directories of `Ds` are pairwise disjoint: none is inside another.
(2026-11-08) Clauses 1-3 for each directory (`dataDirAbsent`), clause 4 for each pair
(`dataDirsApart`): the same claim, so that `dataDirsAbsent e []` holds.

Until sweep repairs 1 this was `walDirsAbsent e Ds`, over the members' WAL directories: distinct
only as strings (`/proc/self/cwd` aliases, `notes/axiom-review/wal-tokens.md`), silent on a stale
backend file (`bootstrap` with no WAL opens whatever `member/snap/db` is there), and its "no
unverified code creates a WAL there" false of every run (the names-only WAL creates it). Go
evidence: `examples/sweeprepairs/wal` (`TestW3Counterexample`, `TestW4StaleBackend`,
`TestW3W4Examples`). -/
def dataDirsAbsent [GooseExts] (e : Expr) (Ds : List GoString) : Prop :=
  (∀ d ∈ Ds, dataDirAbsent e d) ∧ Ds.Pairwise dataDirsApart

/-- **The address `a` is the program's** (`addrsUnclaimed`'s claim of one address: no other
process binds it or connects to it, and the program's own connections to it are the ones
`addrsUnclaimed` lists). (Removed at the net swap, 2026-11-22; restored 2026-11-23 for the single-process
theorems, `notes/single-process-restore.md`.) -/
axiom addrUnclaimed [GooseExts] (e : Expr) (a : GoString) : Prop

/-- **The addresses `As` are the program's** (a fact of the environment a run of `e` is in, and
of `e`'s unverified code): while `e` runs, no other process binds an address of `As`, nor a socket
overlapping one (a wildcard bind of its port, `0.0.0.0:p` or `[::]:p`), and no code of `e` whose
behaviour this repository does not verify binds one. (2026-11-14, the network fault review; the
connect clause reworded after the independent review the same day) Two parts:
(a) **the world assumption** (the user accepted it, 2026-11-14): no other process connects to an
address of `As` (a local process can dial `127.0.0.1:p` and send requests,
`examples/premisefix/foreignconn`). (2026-11-23) Still needed over the net extension: the gRPC and
HTTP traffic of the programs' models (grpc's `ClientConn`, `http.Transport`) does not go through the
extension (`grpc.start`, `http.register` rest on `addrClaim` until phase 7's S2/S5), so the extension's
closed network does not exclude a foreign connection to a gRPC or HTTP listener;
(b) **what `e` itself does** (a fact of its code, checked against the source): every connection to
an address of `As` is made by `e`, and its requests are either sent through operations this
repository verifies or specifies at a trust boundary (clientv3 over grpc's `ClientConn`, rafthttp's
pipeline, stream and snapshot senders over `http.Transport`, `http.roundTripperOk`; the cluster
programs' bridge, `bridge.New`'s spec), or are etcd's own names-only peer requests: the prober's
`GET /raft/probing` (`probing.NewProber`, rafthttp `transport.go:146-147`), the version monitor's
`GET /version` (`cluster_util.go:257`), bootstrap's `GET /members` (`cluster_util.go:81`), and
leasehttp's forwarded `POST /leases` and `POST /leases/internal` (a follower's `RenewHTTP` and
`TimeToLiveHTTP` to the leader, `v3_server.go:553,682`), at the pinned etcd. Those reach no handler
whose protocol needs knowledge: the peer port's handler is
the `RaftHandler` mux (`EtcdServer.RaftHandler`, `server.go:646`), which routes only `/raft`,
`/raft/stream/`, `/raft/snapshot` and `/raft/probing` (`transport.go:163-166`), so it answers
`/version`, `/members`, `/leases` and `/leases/internal` with `404` (`http.mux_handlerOk_spec`),
and the raft protocol's request knowledge holds of all of them with no premise (`raftProto.req`, `Proof/go_etcd_io/etcd/server/v3/
etcdserver/api/rafthttp/Stream.lean`: its premises are only on `POST /raft`, `POST
/raft/snapshot` and `GET`s under `/raft/stream/`); the `GET`s' handler runs get no ticket
(`http.reqTicketOnce`), and the lease `POST`s' runs, which do (`onceOnly`, a ticket no `RoundTrip`
minted), reach only the mux's `404`, which takes no ticket. `examples/premisefix/peerreqs` records them in a three-member cluster.
(b) is what `addrClaim a` stands for (`InvNet.lean`), which program start hands out on its strength.
The boundaries' closed world (`InvNet.lean`) rests on (a) and (b). (Sweep repairs 1, W5) `As`'s
strings are
numeric loopback literals (`netAddrLit`, `goose_adequacy_start`'s `hAsLit`; loopback since
2026-11-14: never proxied), so "an address of `As`" is the
one socket the literal names. (2026-11-08: stated address by address, `addrUnclaimed`, the same
claim; until then an axiomatized proposition of the list.) -/
def addrsUnclaimed [GooseExts] (e : Expr) (As : List GoString) : Prop := ∀ a ∈ As, addrUnclaimed e a

/-- The rights program start gives: the right to register each name of `Ns`, and for each address
of `As` the program's claim on it (`addrClaim`; until the net swap, 2026-11-22, `netAddrFree`, whose
listening token is now the net extension's) and the right to fix its HTTP protocol (`httpProtoFree`,
D39a, 2026-10-23; the address part removed at the swap and restored 2026-11-23 for the single-process
theorems); and (2026-11-03; sweep repairs 1, W3/W4) each data directory of `Ds` fresh
(`dataDirFresh`), which a member's first start consumes; and (sweep repairs 1, B4) `ETCD_VERIFY` off
for the run (`envVerifyOff`, persistent). -/
def startRights {GF : BundledGFunctors} [GooseExts] (Ns As Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, addrClaim a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    envVerifyOff)

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The trust boundary: program start owns the free names and the addresses' claims, once** (see the
file header). `goose_adequacy`, with the WP proof also given `startRights Ns As Ds`. (S3e, 2026-11-17:
the axiom again; from 2026-11-08 a corollary of `goose_adequacy_start_files`, which also handed out
`fileHolds f ∅` for fresh database files: since `fileHolds` is the concrete claim on a name in the
tree's shared mode, an axiom handing it out beside `extsLocalStart`'s tree could contradict the
tree's ownership; the files are now derived from the tree, `Proof/runtime/StartFiles.lean`.)
(2026-11-20) `goose_adequacy_below`'s premises, with the WP proof also given the rights: the
thread bound is one of this execution (`RealNstepsBelow T n`), not of every execution of `n` steps
(`RealThreadsBelow`), as Perennial's `goose_adequacy` became `goose_adequacy_below`
(`AdequacyAlong.lean`), whose proof shows the bound was only ever used along the given
execution; the satisfiability argument of the file header carries over (rights read as `True`:
`goose_adequacy_below`, a theorem). The previous statement is `goose_adequacy_start_all`. -/
axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ns As Ds : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns As Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

/-- **`goose_adequacy_start` with `goose_adequacy`'s thread premise** (its statement until
2026-11-20): every real execution of `n` steps stays below `T` threads. -/
theorem goose_adequacy_start_all [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ns As Ds : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns As Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState)))
    (hNsIds : prometheus.descIdsDistinct Ns := by decide +kernel) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  goose_adequacy_start N T e σ g φ hφ Hinitg Hinit Ns As Ds hNs hAs hDs hAsLit hNsFree hAsFree
    hDsFree hEnv Hwp n κs t2 σ2 (RealNstepsBelow.of_threadsBelow Hsteps Hlive) Hbound Hthreads

end adequacy

end EtcdGrove
end Perennial
