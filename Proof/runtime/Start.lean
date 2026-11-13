/-
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
of `Ns` is registered twice and no address of `As` bound twice, which is what `MustRegister`'s and
`Listen`'s specs need. The rest is `goose_adequacy`.

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
(Sweep repairs 1, W5) The addresses of `As` are numeric literals (`hAsLit`, decidable), so each
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

(2026-11-08, mvccrand's closed theorem, the user's decision) It also receives `fileHolds f ∅`, the
backend's database file at `f` holding nothing, for each path of `Fs` (`goose_adequacy_start_files`;
`goose_adequacy_start` is the case `Fs = []`), for a program of which `dbFilesAbsent e Fs` holds: the
paths name one file each for the run, absent at start, touched only through the backend's and
bbolt's operations with trust-boundary specs. So each is opened fresh by the verified code at most
once in a run, which `backend.New`'s `fileHolds path ∅` premise needs (bbolt's `Open` creates the
file and writes an empty database). Once only, as the other rights: `fileHolds` of an absent file
is handed out only here (the backend's other producers of `fileHolds` give back a file the program
opened, `backend.Close`, or one it wrote, the snapshot's), once per path, to the one WP proof.

A design choice D19d leaves to the user: the alternative is an extension whose initial world holds
the free addresses and the empty registry (`extsGlobalStart` the rights, `nameFree`/`netAddrFree` its
ghost state, `MustRegister`/`Listen` its operations), a Perennial change proposed in
`notes/decisions.md`, D19d; with it this axiom goes.
-/
module

public import Perennial.GooseLang.Adequacy
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

/-- **The address `a` is the program's** (`addrsUnclaimed`'s claim of one address). -/
axiom addrUnclaimed [GooseExts] (e : Expr) (a : GoString) : Prop

/-- **The addresses `As` are the program's** (a fact of the environment a run of `e` is in, and
of `e`'s unverified code): while `e` runs, no other process binds an address of `As`, nor a socket
overlapping one (a wildcard bind of its port, `0.0.0.0:p` or `[::]:p`), and no code of `e` whose
behaviour this repository does not verify binds one. (Sweep repairs 1, W5) `As`'s strings are
numeric literals (`netAddrLit`, `goose_adequacy_start`'s `hAsLit`), so "an address of `As`" is the
one socket the literal names. (2026-11-08: stated address by address, `addrUnclaimed`, the same
claim; until then an axiomatized proposition of the list.) -/
def addrsUnclaimed [GooseExts] (e : Expr) (As : List GoString) : Prop := ∀ a ∈ As, addrUnclaimed e a

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

/-- **The path `f` is a fresh database file of the program** (a fact of the environment a run of `e`
is in, and of `e`'s unverified code; 2026-11-08, the user's decision for mvccrand's closed theorem),
as `dataDirsAbsent`'s clauses for a file:
1. the string `f` names, from when that file exists, one and the same file for the rest of the run.
   The working directory does not change. The program reaches the file only by the path `f` (no
   symbolic link, alias spelling, `/proc` link, hard link or bind mount reaches it), and the
   directory holding it exists;
2. when `e` starts, no file is at `f`;
3. no other process, and no code of `e` beyond the backend's and bbolt's operations with
   trust-boundary specs here (`backend.New`'s `bolt.Open`, the backend's commits, `Close`), opens,
   writes, truncates, locks, links, renames, removes or changes the mode of the file at `f`, by any
   path;
4. `f` is inside no data directory of the run's (`dataDirsAbsent`), and the paths of `Fs` are
   distinct files (`dbFilesAbsent`, with `Fs.Nodup`). -/
axiom dbFileAbsent [GooseExts] (e : Expr) (f : GoString) : Prop

/-- **The paths `Fs` are fresh database files of the program** (`dbFileAbsent` of each). -/
def dbFilesAbsent [GooseExts] (e : Expr) (Fs : List GoString) : Prop := ∀ f ∈ Fs, dbFileAbsent e f

/-- The rights program start gives: the right to register each name of `Ns` and to listen on
each address of `As`, and (D39a, 2026-10-23) to fix each address's HTTP protocol
(`httpProtoFree`); and (2026-11-03; sweep repairs 1, W3/W4) each data directory of `Ds` fresh
(`dataDirFresh`), which a member's first start consumes; and (sweep repairs 1, B4) `ETCD_VERIFY` off
for the run (`envVerifyOff`, persistent). -/
def startRights {GF : BundledGFunctors} [GooseExts] (Ns As Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, netAddrFree a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    envVerifyOff)

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The trust boundary: program start owns the free names, addresses and fresh files, once**
(see the file header). `goose_adequacy`, with the WP proof also given `startRights Ns As Ds` and
(2026-11-08) `fileHolds f ∅` for each fresh database file `f` of `Fs`. -/
axiom goose_adequacy_start_files [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ns As Ds Fs : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hFs : Fs.Nodup)
    (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As)
    (hDsFree : dataDirsAbsent e Ds) (hFsFree : dbFilesAbsent e Fs) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns As Ds -∗
        ([∗list] f ∈ Fs, backend.fileHolds (GF := GF) f ∅) ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

/-- **Program start owns the free names and addresses, once** (`goose_adequacy_start_files` with
no fresh file; until 2026-11-08 the axiom itself): `goose_adequacy`, with the WP proof also given
`startRights Ns As Ds`. -/
theorem goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
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
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy_start_files (GF := GF) N T e σ g φ hφ Hinitg Hinit Ns As Ds [] hNs hAs hDs
    List.nodup_nil hAsLit hNsFree hAsFree hDsFree (fun _ h => absurd h List.not_mem_nil) hEnv
    ?_ n κs t2 σ2 Hsteps Hbound Hthreads Hlive
  intro hG HN HT HL
  iintro Hg Hl Hgs Htok Hr -
  iapply (Hwp HN HT HL) $$ Hg Hl Hgs Htok Hr

end adequacy

end EtcdGrove
end Perennial
