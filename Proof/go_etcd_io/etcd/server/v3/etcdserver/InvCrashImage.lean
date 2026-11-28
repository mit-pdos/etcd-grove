/-
**A member's data directory after a machine crash: the server's vocabulary** (etcd-dist D6, spec
phase, 2026-11-24; `notes/etcd-dist-d6.md`). Lean-first (no Rocq counterpart). Statements only: the
definitions here are what `NewServer.specC` (`Spec/.../etcdserver/NewServerCrash.lean`) and the
member's generation (`dist/crash/MemberGen.lean`) are written in; nothing here is proved yet.

The graceful restart's image (`srvDiskImageAt`, `InvRestart.lean`) is what a stop in the same process
leaves. A crash leaves a different one, in four ways (each a row of `notes/etcd-dist-d6.md` §2):

* **The consistent index may be above the WAL's commit** (`restart-vs-crash.md`, Q1(c)): the apply
  thread commits the backend (synced) in parallel with the raft loop's `Save`, and a commit-only
  `Save` is not synced. So `i ≤ σ.commit` (`wal.stopImage`'s) is dropped, and `i` is bounded by the
  cluster's committed log instead (the image's `srvRLogLb ρ.rd.raft A` with `uint.Z i = ai0 + |A|`, as
  in the graceful image). (T10 restatement, 2026-11-25, approved by coordinator-E on #50, comment
  2026-11-25T15:22:46Z, item 2; ledger 2026-11-25 "T10" and "`srvCrashImageAt` misses three crash images")
  `σ.b ≤ i` is dropped too (the received-snapshot window, `snapRowB2`), and so is `bootLen ≤ i` (a
  backend commit inside the bootstrap batch, or none yet).
* **The stored `confState` may be one conf change ahead** of the stored index (`confRowW`: a timer
  commit between a conf change's `SetConfState` and its `LockInsideApply`).
* **The WAL's read facts are carried, not trusted**: `walReadFacts σ` (I1-I4, trusted inside
  `bootstrapRestartContract` until the WAL's C6) is a fact of the crash image (`wal.crashImageR`), which
  the crash lemma derives from the WAL's crash image (`walImg`), so the contract below takes it as a
  premise instead of promising it.
* **The id's vacancy is unarmed** (`nodeVacant`, what raft's `nodeCrash`/`readyCrashEnter` give back),
  where the graceful stop leaves it armed (`nodeVacantA`); `nodeVacant_arm` re-arms it at the boot.
* **The storage registry is the new generation's** (any `M`, in practice `∅` at a fresh registry
  name: the old generation's `MemoryStorage` locations died with its heap).

The rest is `srvDiskImageAt`'s: the backend's image of a committed prefix, the membership at `i`,
the files (`srvFilesC`, `SrvCrash.lean`: since P8, 2026-11-25, the WAL's files as a crash leaves them,
`walFilesC`, `srvFiles` without the WAL's synced mark, which a crash does not raise; the graceful
`srvFiles` gives it, `srvFiles_srvFilesC`; the bbolt file; made by the crash lemma from the
file extension's crash rest), and the snapshot directory's invariant at the new generation, with its
crash token (`snapDirKeep`, D-T7-2), which `NewServer.specC` returns for the generation's next crash.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The WAL's slot of a crash image** (D6; `wal.stopImage` without `σ.b ≤ i ≤ σ.commit`, with the
WAL's read facts): the records `σ` hold the durable state `S` (`StorageHolds`), they meet the WAL
interface's I1-I4 (`walReadFacts`), the records' snapshot certificate, and a committed log reaching
the records' base that the durable state's log agrees with. (T10, 2026-11-25: `wal.crashImage` until
then, with `σ.b ≤ i`; the snapshot's position relative to the backend's index is `snapRowB2`'s.) -/
def wal.crashImageR (cl : Cluster) (S : RaftState) (σ : StorContents) : IProp GF :=
  iprop(⌜StorageHolds S σ ∧ walReadFacts σ⌝ ∗ walSnapCert cl σ ∗
    (∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝))

/-- **The membership row of a crash image** (T10, 2026-11-25; ledger "the backend's stored `confState`
can be one conf change ahead of its stored index"): the backend's stored `confState` is the
configuration at the stored index `i`, or at `i + 1` (a conf change's `SetConfState` runs before the
change's `LockInsideApply` moves the consistent index; a commit in between, from the backend's timer,
stores the new `confState` with the old index; `nonissues/etcd-confstate-ahead-of-consistent-index.md`). -/
def confRowW (cl : Cluster) (i : w64) (D : backend.Data) (m : Membership) : IProp GF :=
  iprop(⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝ ∨
    ∃ m' : Membership, confAt cl (uint.nat i + 1) m' ∗ ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m'⌝)

/-- **The snapshot row of a crash image** (T10, 2026-11-25, B2: the received-snapshot window): the WAL's
snapshot is at or below the backend's index `i`, with the removal counter `c` at most one past it; or it
is above it (index `j`), its `.snap.db` was saved (durably) in the member's snapshot directory
(`snapSaved`), and either the install has not taken it (`c ≤ j`: the directory's invariant still holds
it) or the install took it and the crash undid the rename (`c = j + 1`; the rename onto `db` and its
directory sync not durable): the file, back under its name, is an image at `j` (`fileAt`, with its
certificate). (The fork syncs the directory before it opens the new backend, so nothing has committed
to the snapshot's file in that window.)

The `.snap.db` case of `bootstrapCrashContract` needs, beside this row (review
`notes/axiom-review/c-i2-snapdb.md`, the caller's obligations): (1) in the `c ≤ σ.b` branch, the file itself,
which the directory's invariant (`snapDirKeep`'s body `snapDirBody`) still holds: `j` is saved (`E`) and its
removal fact `Rm j = monoNatLbOwn γm (j + 1)` is refuted by the counter's authority at `c ≤ j`, so `j ∈ M`, a file
with its image; the restart takes it out (`snapDir_take`) as `fileAt`. Nothing removes it in between: the
fork's `purgeFile` no longer purges `.snap.db` files (`a4d2bb172`, in the pin's history;
`nonissues/etcd-purge-snapdb-unopened.md`), `ReleaseSnapDBs` removes only below the released index (and then
gives `Rm`). (2) The file's stored index is `j` exactly: the image certificate `srvImageM … j Ds` (the
invariant's `img`, and this row's `□ srvImageM`) has `imageRestAt … j …`, the receiver's save gives it. -/
def snapRowB2 (γ : SrvRaft) (dd : GoString) (σ : StorContents) (i : w64) (γd : GName) (c : Nat) :
    IProp GF :=
  iprop(⌜σ.b ≤ uint.nat i ∧ c ≤ uint.nat i + 1⌝ ∨
    ∃ j : w64, ⌜uint.nat j = σ.b ∧ uint.nat i < σ.b⌝ ∗ snapSaved γd j ∗
      (⌜c ≤ σ.b⌝ ∨ ⌜c = σ.b + 1⌝ ∗ ∃ Ds : backend.Data,
        backend.fileAt (snap.snapDBPath (config.snapDirOf dd) j) Ds ∗ □ srvImageM γ.authOn γ j Ds))

/-- **Member `id`'s data directory after a crash, at the request names `ρ` of the incarnation that
wrote it** (D6; see the file header): `srvDiskImageAt` with the id's vacancy unarmed, the WAL's slot
`wal.crashImageR` (no `σ.b ≤ i ≤ σ.commit`; the read facts carried), any storage registry `M`, and
(T10, 2026-11-25) no `bootLen ≤ i`, the membership row `confRowW` and the snapshot row `snapRowB2`; and
(D-T7-2, 2026-11-25, approved by coordinator-E on #50, 15:22:46Z items 3-5; ledger "`srvCrashImageAt` misses
three crash images and drops a crash token") the snapshot directory's invariant with its crash token
(`snapDirKeep`, not only the handle `snapDirInvH`), which the next generation's crash law needs. -/
def srvCrashImageAt (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) (S : RaftState)
    (σ : StorContents) (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership)
    (M : GMap Loc MemStorNamesRec) : IProp GF :=
  iprop(nodeVacant γ.cl id ∗ raftState γ.cl id S ∗
    ⌜ρ.rd.raft.raft = γ ∧ ρ.rd.kv.c0 = W64 0⌝ ∗ srvRLogLb ρ.rd.raft A ∗
    ⌜uint.Z i = uint.Z ρ.rd.raft.ai0 + A.length ∧
      imageRestAt ρ.rd.kv γ.boot i (ρ.rd.raft.pre ++ A) D ∧
      imageStOk (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A)⌝ ∗
    (∃ u : Bool, mvcc.api.mvccImage D (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A) u) ∗
    -- (keepfix (c) step 1, 2026-11-28) the stored pair is a committed entry, or the index 0 (`srvDiskImageAt`'s
    -- row; from the backend image's `bkTermRow` and the committed prefix, `srvRLogLb_ciPair`)
    (⌜i = W64 0⌝ ∨ srvCIPair γ.cl i (metaTermOf D)) ∗
    confAt γ.cl (uint.nat i) m ∗ confRowW γ.cl i D m ∗
    wal.crashImageR γ.cl S σ ∗
    (letI : MemStorReg GF := ⟨γ.reg⟩; memStorRegAuth M) ∗
    srvFilesC dd id σ D ∗
    (∃ (γd γm : GName) (c : Nat),
      ⌜γ.snapLoc id = some γd⌝ ∗ snapRowB2 γ dd σ i γd c ∗
      snapDirKeep (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
        (fun j => monoNatLbOwn γm (uint.nat j + 1)) ∗
      monoNatAuthOwn γm 1 c))

/-- **The snapshot directory's invariant with its crash token, as a restart returns it** (D-T7-2,
2026-11-25): `srvCrashImageAt`'s `snapDirKeep`, at the member's directory names `γd` and some removal
counter `γm`; `NewServer.specC`'s post gives it back (the server keeps only the handle), for the
generation's crash frame (`memberCrash.memberSnapKeep`). -/
def srvSnapKeep (γ : SrvRaft) (id : w64) (dd : GoString) : IProp GF :=
  iprop(∃ γd γm : GName, ⌜γ.snapLoc id = some γd⌝ ∗
    snapDirKeep (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
      (fun j => monoNatLbOwn γm (uint.nat j + 1)))

/-- **Member `id`'s data directory after a crash** (`srvCrashImageAt` at some witnesses). -/
def srvCrashImage (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) : IProp GF :=
  iprop(∃ (S : RaftState) (σ : StorContents) (i : w64) (A : List EntryModel)
      (D : backend.Data) (m : Membership) (M : GMap Loc MemStorNamesRec),
    srvCrashImageAt γ ρ id dd S σ i A D m M)

end defs

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`bootstrap`'s contract on a data directory a crash left** (D6; a premise until #34's stage 5
proves it, `notes/etcd-dist-d6.md` §2): `bootstrapRestartContract` with the crash image's changes, in two
cases (conjuncts):

* **The backend kept** (`σ.b ≤ i`): the backend's index `i` need not be at or below the WAL's commit,
  and the WAL's read facts `walReadFacts σ` are the caller's premise (carried by the crash image)
  instead of a promise of the contract. (C-I2 review, 2026-11-24) And the WAL's commit at least the
  bootstrap log's length (`γ.cl.bootLen ≤ σ.commit`): every completed `Save` of the fork's fixed WAL has
  it, and it excludes the unsaved WALs `wal.Discard` removes (Go then takes the first-start branch,
  which `bootOkR` does not describe). (T10, 2026-11-25) No `bootLen ≤ i`: a backend commit can fall
  inside the bootstrap batch, or none have happened (`i = 0`; `imageRestAt` accepts the meta keys absent
  there, `encMeta 0 = none`).
* **The `.snap.db` recovery** (T10, 2026-11-25, B2: `i < σ.b`, the received-snapshot window):
  `recoverSnapshot` finds the backend's stored index `i` below the WAL's snapshot `j = σ.b` and opens
  `<j>.snap.db` in its place (`OpenSnapshotBackend`), so the caller gives that file too (holding `Ds`,
  an image at `j` of the log `Ls`), and the post is at `(j, Ls, Ds)`.

Everything else (the configurations covered, the write budget, the static membership, the cluster
version's log, the image's store part, the files, the post `bootOkR`) is the graceful contract's. The
graceful contract is the first case's instance `i ≤ σ.commit` (with the read facts its own trusted
promise), so a proof of this one (stage 5's `bootstrapRestartContract_holds`, generalized) gives
both. -/
def bootstrapCrashContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) : IProp GF :=
  iprop((□ ∀ (σ : StorContents) (i : w64) (L : List EntryModel) (D : backend.Data)
      (M : GMap Loc MemStorNamesRec),
    ⌜σ.b ≤ uint.nat i ∧ walReadFacts σ ∧ γ.cl.bootLen ≤ σ.commit ∧
      bootCfgOk cfg ∧ cfg.ForceNewCluster' = false ∧ cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir' ∧
      storage.dbOpensOk ∧
      N + 7 + bootWB ≤ backend.wbInit ∧
      (∀ f, ((restModel (W64 0) γ.boot L).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.boot).lookup f).map apply.MemberM.peerURLs) ∧
      clusterVerLogOk L⌝ -∗
    (∃ (γk : KVNames) (A : List EntryModel) (u : Bool),
      ⌜γk.c0 = W64 0 ∧ imageRestAt γk γ.boot i L D ∧ imageStOk (kvModel γk A) (crevOf γk A)⌝ ∗
      mvcc.api.mvccImage D (kvModel γk A) (crevOf γk A) u) -∗
    -- (keepfix-d) the stored term is the committed term of the stored index (T10's `bkTermRow`)
    (⌜i = W64 0⌝ ∨ srvCIPair γ.cl i (metaTermOf D)) -∗
    {{ zapLoggerOk cfg.Logger' ∗
        (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
        ⌜EtcdVerifyOff⌝ ∗
        bootCfgRO cfg U ∗ memStorRegAuth M ∗
        srvFilesC cfg.DataDir' id σ D }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOkR cfg γ id N dir σ i L D M b }}) ∗
  (□ ∀ (σ : StorContents) (i : w64) (D : backend.Data) (j : w64) (Ls : List EntryModel)
      (Ds : backend.Data) (M : GMap Loc MemStorNamesRec),
    ⌜uint.nat i < σ.b ∧ uint.nat j = σ.b ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta i ∧
      walReadFacts σ ∧ γ.cl.bootLen ≤ σ.commit ∧
      bootCfgOk cfg ∧ cfg.ForceNewCluster' = false ∧ cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir' ∧
      storage.dbOpensOk ∧
      N + 7 + bootWB ≤ backend.wbInit ∧
      (∀ f, ((restModel (W64 0) γ.boot Ls).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.boot).lookup f).map apply.MemberM.peerURLs) ∧
      clusterVerLogOk Ls⌝ -∗
    (∃ (γk : KVNames) (A : List EntryModel) (u : Bool),
      ⌜γk.c0 = W64 0 ∧ imageRestAt γk γ.boot j Ls Ds ∧ imageStOk (kvModel γk A) (crevOf γk A)⌝ ∗
      mvcc.api.mvccImage Ds (kvModel γk A) (crevOf γk A) u) -∗
    -- (keepfix-d) the snapshot file's stored term is the committed term of its index (its image
    -- certificate's row, `srvImage`)
    (⌜j = W64 0⌝ ∨ srvCIPair γ.cl j (metaTermOf Ds)) -∗
    {{ zapLoggerOk cfg.Logger' ∗
        (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
        ⌜EtcdVerifyOff⌝ ∗
        bootCfgRO cfg U ∗ memStorRegAuth M ∗
        srvFilesC cfg.DataDir' id σ D ∗
        backend.fileAt (snap.snapDBPath (config.snapDirOf cfg.DataDir') j) Ds }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOkR cfg γ id N dir σ j Ls Ds M b }}))

end boot

end EtcdGrove
end Perennial
