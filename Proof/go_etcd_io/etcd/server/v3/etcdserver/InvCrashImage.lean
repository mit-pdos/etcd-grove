/-
**A member's data directory after a machine crash: the server's vocabulary** (etcd-dist D6, spec
phase, 2026-11-24; `notes/etcd-dist-d6.md`). Lean-first (no Rocq counterpart). Statements only: the
definitions here are what `NewServer.specC` (`Spec/.../etcdserver/NewServerCrash.lean`) and the
member's generation (`dist/crash/MemberGen.lean`) are written in; nothing here is proved yet.

The graceful restart's image (`srvDiskImageAt`, `InvRestart.lean`) is what a stop in the same process
leaves. A crash leaves a different one, in four ways (each a row of `notes/etcd-dist-d6.md` §2):

* **The consistent index may be above the WAL's commit** (`restart-vs-crash.md`, Q1(c)): the apply
  thread commits the backend (synced) in parallel with the raft loop's `Save`, and a commit-only
  `Save` is not synced. So `i ≤ σ.commit` (`wal.stopImage`'s) is dropped: the crash image keeps only
  `σ.b ≤ i` (`wal.crashImage`), and `i` is bounded by the cluster's committed log instead (the image's
  `srvRLogLb ρ.rd.raft A` with `uint.Z i = ai0 + |A|`, as in the graceful image).
* **The WAL's read facts are carried, not trusted**: `walReadFacts σ` (I1-I4, trusted inside
  `bootstrapRestartContract` until the WAL's C6) is a fact of the crash image (`wal.crashImage`), which
  the crash lemma derives from the WAL's crash image (`walImg`), so the contract below takes it as a
  premise instead of promising it.
* **The id's vacancy is unarmed** (`nodeVacant`, what raft's `nodeCrash`/`readyCrashEnter` give back),
  where the graceful stop leaves it armed (`nodeVacantA`); `nodeVacant_arm` re-arms it at the boot.
* **The storage registry is the new generation's** (any `M`, in practice `∅` at a fresh registry
  name: the old generation's `MemoryStorage` locations died with its heap).

The rest is `srvDiskImageAt`'s: the backend's image of a committed prefix, the membership at `i`,
the files (`srvFiles`: the closed WAL's files and the bbolt file, now made by the crash lemma from the
file extension's crash rest), and the snapshot directory's invariant at the new generation.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

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

/-- **The WAL's slot of a crash image** (D6; `wal.stopImage` without `i ≤ σ.commit`, with the WAL's
read facts): the records `σ` hold the durable state `S` (`StorageHolds`), they meet the WAL
interface's I1-I4 (`walReadFacts`), their snapshot is at or below the backend's index `i` (so that
`bootstrap` keeps the backend file: `recoverSnapshot` opens a `.snap.db` only when the file's index
is below the snapshot's; the received-snapshot case where the backend is behind the WAL's snapshot is
open, `notes/etcd-dist-d6.md` Q3), the records' snapshot certificate, and a committed log reaching
the records' base that the durable state's log agrees with. -/
def wal.crashImage (cl : Cluster) (S : RaftState) (σ : StorContents) (i : w64) : IProp GF :=
  iprop(⌜StorageHolds S σ ∧ walReadFacts σ ∧ σ.b ≤ uint.nat i⌝ ∗ walSnapCert cl σ ∗
    (∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝))

/-- **Member `id`'s data directory after a crash, at the request names `ρ` of the incarnation that
wrote it** (D6; see the file header): `srvDiskImageAt` with the id's vacancy unarmed, the WAL's slot
`wal.crashImage` (no `i ≤ σ.commit`; the read facts carried) and any storage registry `M`. -/
def srvCrashImageAt (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) (S : RaftState)
    (σ : StorContents) (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership)
    (M : GMap Loc MemStorNamesRec) : IProp GF :=
  iprop(nodeVacant γ.cl id ∗ raftState γ.cl id S ∗
    ⌜ρ.rd.raft.raft = γ ∧ ρ.rd.kv.c0 = W64 0⌝ ∗ srvRLogLb ρ.rd.raft A ∗
    ⌜uint.Z i = uint.Z ρ.rd.raft.ai0 + A.length ∧
      imageRestAt ρ.rd.kv γ.boot i (ρ.rd.raft.pre ++ A) D ∧
      imageStOk (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A)⌝ ∗
    (∃ u : Bool, mvcc.api.mvccImage D (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A) u) ∗
    ⌜γ.cl.bootLen ≤ uint.nat i⌝ ∗
    confAt γ.cl (uint.nat i) m ∗ ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝ ∗
    wal.crashImage γ.cl S σ i ∗
    (letI : MemStorReg GF := ⟨γ.reg⟩; memStorRegAuth M) ∗
    srvFiles dd id σ D ∗
    (∃ (γd γm : GName) (c : Nat),
      ⌜γ.snapLoc id = some γd ∧ c ≤ uint.nat i + 1⌝ ∗
      inv snapDirN (snapDirInv (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
        (fun j => monoNatLbOwn γm (uint.nat j + 1))) ∗
      monoNatAuthOwn γm 1 c))

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
proves it, `notes/etcd-dist-d6.md` §2): `bootstrapRestartContract` with two changes, the crash
image's: the backend's index `i` need not be at or below the WAL's commit (only `σ.b ≤ i`), and the
WAL's read facts `walReadFacts σ` are the caller's premise (carried by the crash image) instead of a
promise of the contract. Everything else (the configurations covered, the write budget, the static
membership, the cluster version's log, the image's store part, the files, the post `bootOkR`) is the
graceful contract's. (C-I2 review, 2026-11-24) And the WAL's commit at least the bootstrap log's length
(`γ.cl.bootLen ≤ σ.commit`): every completed `Save` of the fork's fixed WAL has it, and it excludes the
unsaved WALs `DiscardUnsaved` removes (Go then takes the first-start branch, which `bootOkR` does not
describe). The graceful contract is the instance `i ≤ σ.commit` (with the read facts its own
trusted promise), so a proof of this one (stage 5's `bootstrapRestartContract_holds`, generalized)
gives both. -/
def bootstrapCrashContract (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
    (γ : SrvRaft) (id : w64) (N : Nat) (dir : w64 → List GoString) : IProp GF :=
  iprop(□ ∀ (σ : StorContents) (i : w64) (L : List EntryModel) (D : backend.Data)
      (M : GMap Loc MemStorNamesRec),
    ⌜σ.b ≤ uint.nat i ∧ walReadFacts σ ∧ γ.cl.bootLen ≤ uint.nat i ∧ γ.cl.bootLen ≤ σ.commit ∧
      bootCfgOk cfg ∧ cfg.ForceNewCluster' = false ∧ cfg.DedicatedWALDir' = srvWalDirOf cfg.DataDir' ∧
      storage.dbOpensOk ∧
      N + 7 + bootWB ≤ backend.wbInit ∧
      (∀ f, ((restModel (W64 0) γ.boot L).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.boot).lookup f).map apply.MemberM.peerURLs) ∧
      clusterVerLogOk L⌝ -∗
    (∃ (γk : KVNames) (A : List EntryModel) (u : Bool),
      ⌜γk.c0 = W64 0 ∧ imageRestAt γk γ.boot i L D ∧ imageStOk (kvModel γk A) (crevOf γk A)⌝ ∗
      mvcc.api.mvccImage D (kvModel γk A) (crevOf γk A) u) -∗
    {{ zapLoggerOk cfg.Logger' ∗
        (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
        ⌜EtcdVerifyOff⌝ ∗
        bootCfgRO cfg U ∗ memStorRegAuth M ∗
        srvFiles cfg.DataDir' id σ D }}
      (App (Val (@! bootstrap)) (Val #cfg))
    {{ (b : Loc) (err : GoInterface), RET (PairV #b #err);
        ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ bootOkR cfg γ id N dir σ i L D M b }})

end boot

end EtcdGrove
end Perennial
