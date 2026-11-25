/- Lean-first (no Rocq counterpart).

# The server's crash-aware durability invariant (etcd-dist D6, task T2, 2026-11-24)

`notes/etcd-dist-d6.md` §3 and §10 (this task). The graceful invariant `rnDurInv` (`InvWal.lean`) ties
the raft loop's view of the WAL to the records; raft's durable state `raftState` is the loop's own
(`rnDrv`), so a crash, which destroys the loop's resources, loses it. This module states the
per-generation replacement, `rnDurInvK`, as kvnet's `kdFileInvK` does for its one file
(`KvNet/.../kvnet/Defs.lean`), and what the raft loop and the apply thread do to it (statements, as
`abbrev <name>.law : Prop`, `notes/decisions.md`, "Import tiers: a proof takes a linked lemma as a law").

**What a crash can leave.** By the WAL fork fix (`walSaveAtomic.law`, `storage/WalRecsH.lean`), the
restart reads a *complete* prefix `Hs.take j` of the WAL's history, at or past the synced mark. Every
`Save` that must sync (`walMustSync`: entries, or a new term or vote) syncs before it returns; a
commit-only `Save` does not, and a `SaveSnap` always syncs. So at any instant the prefixes `j` with
`n ≤ j ≤ |Hs|` (`n` a synced lower bound, `walSyncedLb`) are what a crash can leave, and the invariant
says what each reads as (`CrashReadsHold`): records holding raft's durable state, or, while a batch is
saved and not yet entered, the state the batch enters (`crashOk`). A commit-only batch moves only the
commit (`RaftState.next`: `wcommit` kept), so the older prefixes still hold the entered state; a batch
that must sync is entered after its sync, when only its own prefix is left.

**The invariant** (`rnDurInvK`): the graceful invariant's rows (the loop's view, half here; the handed
log's authority; the records as the view says, with their snapshot certificate), the records' history
(`walRecsH`), a synced lower bound, every snapshot record of the history certified
(`walHistCerts`), the handed logs committed, the pure crash facts; and, unless a crash took them
(`crashed ∗ token νk.tk`, kvnet's pattern), raft's durable state `raftState (durOf vk)` and the
pending batch's *enter* (`rnPendK`). The WAL rows stay outside the crashed side: the WAL contract's
atomic updates fire inside the WAL's steps without `notCrashed`, so they must work on either side
(on the crashed side, a `Save`'s deposit of its batch is dropped). The stop's taken state is
`rnDurInv`'s.

**The steps** (laws below): allocation at a start or restart (`rnDurK_alloc.law`); the loop's `Save`,
which deposits the batch's *enter* (`rnDurK_save.law`); the received snapshot's `SaveSnap`
(`rnDurK_saveSnap.law`); the loop's *enter* after the `Save` returned, with the sync's lower bound or
the batch commit-only (`rnDurK_enter.law`); the apply thread's own `SaveSnap` (`rnDurK_ownSnap.law`);
the stop's take (`rnDurK_take.law`); and the crash (`rnDurK_crash.law`): from the generation's
`crashed`, its token and raft's crash token, whatever prefix the WAL's crash reads, raft's state that
the prefix holds and the id's vacancy (raft's `nodeCrash` or `readyCrashEnter`). The WAL side of the
`Save`/`SaveSnap` steps needs the server's WAL contract to name the history and the sync's lower bound
(`walSaveH.law`, `walSaveSnapH.law`: `storage.Save.spec`'s post already has the latter).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvCrash
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsH
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Perennial.Ghost.SavedProp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The pure crash facts -/

section pure
variable [GooseExts]

/-- **The crash-aware view**: the loop's view (`WalView`, as `rnDurInv`'s), and the batch saved and
not yet entered, if any: the view before it (its durable state is raft's, `durOf`, its handed log the
one the older prefixes are within), the name of its *enter*'s saved record, and the position of its
`Save`'s record in the history (the prefixes up to it hold the state before the batch, those past it
the view's). -/
abbrev WalViewK : Type := WalView × Option (WalView × GName × Nat)

/-- **Raft's durable state** (`raftState`'s) at the crash-aware view: the view's, or the pending
batch's starting one. -/
def durOf (vk : WalViewK) : RaftState :=
  match vk.2 with
  | none => vk.1.S
  | some (v0, _, _) => v0.S

/-- **Records `σ` a restart may start node of durable state `S` from, with the handed log `l`**: they
hold `S` (`StorageHolds`) and their base is within `l` (`wal.crashImage`'s committed-log row). -/
def ImgOk (S : RaftState) (l : List LogEntry) (σ : StorContents) : Prop :=
  StorageHolds S σ ∧ σ.b ≤ l.length

/-- **What the crash image of prefix `j` holds at the view `vk`**: the view's durable state within its
handed log; while a batch whose `Save` is record `pos` is pending, the state before it for the
prefixes up to `pos`. -/
def crashOk (vk : WalViewK) (j : Nat) (σ : StorContents) : Prop :=
  match vk.2 with
  | none => ImgOk vk.1.S vk.1.l σ
  | some (v0, _, pos) => if j ≤ pos then ImgOk v0.S v0.l σ else ImgOk vk.1.S vk.1.l σ

/-- **Every complete prefix a crash can leave reads as records `P` accepts**: the prefixes `j` of
the history `Hs` from the synced lower bound `n` on (`walSaveAtomic.law`), each read (`walRead`) some
records, accepted by `P`. (A restart reads from a purge position `k`, `walReadCut`; that it reads the
same records is the WAL's: `walReadCut_eq`, task T5.) -/
def CrashReadsHold (Hs : WalHist) (n : Nat) (P : Nat → StorContents → Prop) : Prop :=
  ∀ j, n ≤ j → j ≤ Hs.length → ∃ σ, walRead (Hs.take j) = some σ ∧ P j σ

/-- **The history's read conditions** (P8, 2026-11-25; T5's proposal (3), `notes/wal-p8-handoff.md`):
every index within raft's room (`walIdxLe (2^61 - 1)`), and every complete prefix a crash can leave
reads with raft's `committed ≤ lastIndex` along its fold (`walCommitLe`). With them a crash's read meets
the WAL interface's I1-I4 (`walReadFacts_of_read`, `SrvCrash.lean`). Stated per prefix rather than as
`walCommitLeFrom walFresh Hs` of the eager fold: a received snapshot's `SaveSnap` precedes the `Save`
of the commit that covers it, so the eager fold's base is above its commit between the two, where
`walCommitLe_take` does not apply; the reader drops that record (`walKeep`), and `walCommitLe` is over
the reader's fold. -/
def HistReadOk (Hs : WalHist) (n : Nat) : Prop :=
  walIdxLe (2 ^ 61 - 1) Hs ∧ ∀ j, n ≤ j → j ≤ Hs.length → walCommitLe (Hs.take j)

/-- **The pending batch's facts**: the durable log before it agreeing with its handed log (as
`ViewOk`'s). (P5, 2026-11-25: no longer "at no pending received snapshot": the `Save` after a received
snapshot's `SaveSnap` starts from the view with that snapshot pending.) -/
def PendOkK (vk : WalViewK) : Prop :=
  ∀ v0 γb pos, vk.2 = some (v0, γb, pos) → DurAgrees v0.S v0.l

/-- **The pending batch's `Save` record is in the history.** -/
def PosOkK (vk : WalViewK) (Hs : WalHist) : Prop :=
  ∀ v0 γb pos, vk.2 = some (v0, γb, pos) → pos < Hs.length

/-- **The history's crash facts** (the body's pure row besides the view's): the synced mark within the
history, the pending `Save` record in it, every crash prefix reading as the view says, the read
conditions, and the eager fold's `committed ≤ lastIndex`. -/
def HistOkK (vk : WalViewK) (Hs : WalHist) (n : Nat) : Prop :=
  n ≤ Hs.length ∧ PosOkK vk Hs ∧ CrashReadsHold Hs n (crashOk vk) ∧ HistReadOk Hs n ∧
    walCommitLeFrom walFresh Hs


end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The ghost names of the crash-aware durability**: `rnDurInv`'s (`ν`; its `view` here at
`WalViewK`), the crash token `tk` (the crash obligation's: it takes raft's side with it), and the arm
`x` raft's node of the generation was started from (`nodeVacant_arm`'s; the crash obligation keeps
its `nodeCrashTok`). -/
structure WalNamesK (GF : BundledGFunctors) where
  ν : WalNames GF
  tk : GName
  x : CrashNames
  /-- the stop's mark: whole (`own 1`) in the live body, discarded once the stop took the records -/
  tkn : GName
  /-- (T6's input, `notes/etcd-dist-d6.md` §T6) **the snapshot directory's durable indices**: `sd i`
  says the `.snap.db` of index `i` and its directory entry are synced (T6's `snapDurable γd i`,
  abstract here: the WAL names a snapshot index only after `SaveDBFrom` returned, so after a crash
  the snapshot the WAL points at is present) -/
  sd : w64 → IProp GF

/-- **Every snapshot record of the history `Hs` is certified** (persistent): valid in the cluster
`cl` (`snapshotValid` of the snapshot of no data, as `walSnapCert`) and its index durable in the
snapshot directory (`sd`, `WalNamesK.sd`), so that the snapshot of every prefix's read is
(`walSnapCert` and `walSnapDur` of the crash image). -/
def walOpCert (cl : Cluster) (sd : w64 → IProp GF) : WalOp → IProp GF
  | .snap m _ => iprop(snapshotValid cl (SnapshotM.mk [] m) ∗ □ sd m.Index')
  | .save _ _ => iprop(True)

instance walOpCert_persistent (cl : Cluster) (sd : w64 → IProp GF) (o : WalOp) :
    Persistent (walOpCert (GF := GF) cl sd o) := by
  cases o <;> unfold walOpCert <;> infer_instance

def walHistCerts (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) : IProp GF :=
  iprop([∗list] o ∈ Hs, walOpCert cl sd o)

instance walHistCerts_persistent (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) :
    Persistent (walHistCerts (GF := GF) cl sd Hs) := by
  unfold walHistCerts; infer_instance

/-- **The pending batch's *enter*, as the loop received it** (kvnet's `kdBatchRec`): node `n` of the
server's cluster `γn`, started from arm `x`, its *enter* from the driver's state `st` (durable state
`S`) to `st'` (durable state `S2`) with the messages `ms`, and the share `q` of its liveness that waits
with it (`readyCrashEnter` takes it). -/
def rnPendRec (γn : SrvRaft) (id : w64) (x : CrashNames) (S S2 : RaftState) (n : NodeH)
    (st st' : NodeDriverState) (ms : List QMsg) (q : Qp) : IProp GF :=
  letI := srvStor (GF := GF) γn
  iprop(nodeArm n γn.cl x ∗ readyEnter n γn.cl srvClusterN id st st' ms ∗
    nodeRunning n γn.cl srvClusterN q ∗ ⌜st.durable = S ∧ st'.durable = S2⌝)

/-- **The pending batch at the view `vk`**: none, or a record of its *enter* from the state before
it to the view's, saved at `γb` (the loop holds the same saved proposition and recognizes its own
record by it: `rnDurK_enter.law`). -/
def rnPendK (γn : SrvRaft) (id : w64) (x : CrashNames) (vk : WalViewK) : IProp GF :=
  match vk.2 with
  | none => iprop(True)
  | some (v0, γb, _) => iprop(∃ (n : NodeH) (st st' : NodeDriverState) (ms : List QMsg) (q : Qp),
      savedPropOwn γb DFrac.discard (rnPendRec γn id x v0.S vk.1.S n st st' ms q) ∗
      rnPendRec γn id x v0.S vk.1.S n st st' ms q)

/-- **The records' snapshot is durable in the snapshot directory** (persistent): none, or its index
`sd`-durable (`WalNamesK.sd`). -/
def walSnapDur (sd : w64 → IProp GF) (σ : StorContents) : IProp GF :=
  iprop(⌜σ.snap = none⌝ ∨ ∃ m : SnapshotMetadataM, ⌜σ.snap = some (SnapshotM.mk [] m)⌝ ∗ □ sd m.Index')

instance walSnapDur_persistent (sd : w64 → IProp GF) (σ : StorContents) :
    Persistent (walSnapDur (GF := GF) sd σ) := by
  unfold walSnapDur; infer_instance

/-- The handed logs a crash image may be within, committed: the view's, and the pending batch's
starting one. -/
def rnLogLbsK (cl : Cluster) (vk : WalViewK) : IProp GF :=
  iprop(isCommittedLogLb cl vk.1.l ∗
    match vk.2 with
    | none => iprop(True)
    | some (v0, _, _) => isCommittedLogLb cl v0.l)

instance rnLogLbsK_persistent (cl : Cluster) (vk : WalViewK) :
    Persistent (rnLogLbsK (GF := GF) cl vk) := by
  unfold rnLogLbsK; rcases vk with ⟨v, _ | ⟨v0, γb, pos⟩⟩ <;> infer_instance

/-- The namespace of the crash-aware durability invariant. -/
def rnDurKN : Namespace := nroot.@"rnDurK"

/-- The crash-aware durability invariant is in the WAL's client update mask (`WalFs.walAuMask`): the WAL
contract's atomic updates open it (`rnDurN_sub_walAuMask`'s). -/
theorem rnDurKN_sub_walAuMask : (↑rnDurKN : CoPset) ⊆ WalFs.walAuMask := by
  have h1 : (↑rnDurKN : CoPset) ## ↑Fs.osN := ndot_ne_disjoint nroot (by decide)
  have h2 : (↑rnDurKN : CoPset) ## ↑Fs.osShN := ndot_ne_disjoint nroot (by decide)
  have h3 : (↑rnDurKN : CoPset) ## ↑WalFs.walN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact Iris.Std.LawfulSet.mem_diff.2 ⟨Iris.Std.LawfulSet.mem_diff.2
    ⟨Iris.Std.LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h1 p ⟨hp, hn⟩⟩, fun hn => h2 p ⟨hp, hn⟩⟩,
    fun hn => h3 p ⟨hp, hn⟩⟩

/-- **The live body** (see the file header) at the WAL `h`: the crash-aware view `vk` (half; the
other the loop's), the handed log's authority, the records the view describes (`recsOf`, `ViewOk`,
the certificate) at the history `Hs`, a synced lower bound `n`, the history's certificates, the
handed logs committed, the pure crash facts; and raft's side, or the crash's. -/
def rnDurBodyK (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) : IProp GF :=
  iprop(∃ (vk : WalViewK) (σ : StorContents) (Hs : WalHist) (n : Nat),
    ghostVar νk.ν.view (1 : Qp).half vk ∗ monoListAuthOwn νk.ν.cm 1 vk.1.l ∗
    dghostVar νk.tkn (DFrac.own 1) () ∗ walRecsH h (recsOf vk.1 σ) Hs true ∗ walSnapCert γn.cl (recsOf vk.1 σ) ∗
    (letI := h.W; WalFs.walSyncedLb h.dir n) ∗ walHistCerts γn.cl νk.sd Hs ∗ rnLogLbsK γn.cl vk ∗
    ⌜ViewOk vk.1 σ ∧ PendOkK vk ∧ HistOkK vk Hs n⌝ ∗
    ((raftState γn.cl id (durOf vk) ∗ rnPendK γn id νk.x vk) ∨ (crashed ∗ token νk.tk)))

/-- **The crash-aware durability invariant** of the raft wrapper's WAL `h` for member `id` of the
server's cluster `γn` (see the file header): the live body, or the stop's taken state
(`rnDurInv`'s: the stop's claim, the apply thread's and the loop's tokens; and the stop's mark,
persistent: `rnTakenK`). -/
def rnDurInvK (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) : IProp GF :=
  iprop(⌜νk.ν.h = h⌝ ∗ inv rnDurKN iprop(rnDurBodyK γn id νk h ∨
    (token νk.ν.stop ∗ token νk.ν.app ∗ token νk.ν.ok ∗ dghostVar νk.tkn DFrac.discard ())))

/-- **The stop took the records** (persistent): the stop's mark discarded (`rnDurK_take.law`). It
contradicts the live body. -/
def rnTakenK (νk : WalNamesK GF) : IProp GF := dghostVar νk.tkn DFrac.discard ()

instance rnDurInvK_persistent (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) :
    Persistent (rnDurInvK (GF := GF) γn id νk h) := by
  unfold rnDurInvK; infer_instance

/-- The loop's half of the crash-aware view, with its "not stopped" token (`rnWalView`'s). -/
def rnWalViewK (νk : WalNamesK GF) (vk : WalViewK) : IProp GF :=
  iprop(ghostVar νk.ν.view (1 : Qp).half vk ∗ token νk.ν.ok)

/-! ## The WAL contract with the history (statements) -/

/-- **The contract's `Save`, with the history** (to be proved in the contract, from
`storage.Save.spec`, whose post has the sync's lower bound, and `walRecs_saveAU`, which appends the
record): `walSaveSized_spec` with the atomic update over `walRecsH` (the history grows by the
`Save`), committing at the history `Hs`, and on success the sync's lower bound when the batch must
sync (`walMustSync`). -/
abbrev walSaveH.law : Prop :=
  ∀ (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk), st = GoInterface.ok si →
    ∀ (sized : Bool) (q : Qp) (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc)
      (cs : List EntryC) (Q : WalHist → IProp GF),
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
          ([∗list] l; c ∈ esL; cs, entRoC l c) ∗ ⌜∀ c ∈ cs, walSaveEntOk sized c⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }> }}
        (App (App (Val #(methods si.ty go!"Save" si.v)) (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗ ∃ Hs : WalHist, Q Hs ∗
            (⌜walMustSync Hs hs (cs.map EntryC.model)⌝ -∗
              (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)))) ∨
          (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < (cs.map (fun c => entrySize c + 64)).sum⌝ ∗
            storage.walOpen h q ∗ walStorRd st h ∗
            AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                  ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
              @ WalFs.walAuMask, ∅
              <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                  (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }>) }}

/-- **The contract's `SaveSnap`, with the history** (to be proved in the contract, as
`walSaveH.law`): `walSaveSnap_spec` with the atomic update over `walRecsH` (the snapshot record
appended), committing at the history `Hs`, and the record synced (`SaveSnapshot` always syncs). -/
abbrev walSaveSnapH.law : Prop :=
  ∀ (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk), st = GoInterface.ok si →
    ∀ (sized : Bool) (q : Qp) (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al : Bool)
      (Q : WalHist → IProp GF),
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
          ⌜m.index.isSome ∧ m.term.isSome ∧ storage.metaWalC m = walSnapCanon m.model al⌝ ∗
          ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗
          ⌜uint.nat m.model.Index' < 2 ^ 64 - 1 ∧ (walSrvMr.encSnap m.model al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSaveSnap σ m.model) (Hs ++ [WalOpG.snap m.model al]) sized,
              COMM Q Hs }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          ∃ Hs : WalHist, Q Hs ∗ (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)) ∗
            walSnapRec h Hs.length m.model }}

/-! ## The invariant's steps (statements) -/

/-- **Allocation** (a first start: `walFresh`, the empty history, `walView0`, raft's state
`RaftState.init`; a restart: the records the new generation's WAL holds, all synced, at a view
`ViewOk` describes): from the records with their history, every complete prefix from the synced
lower bound `n` reading records that hold the view's state, the history's certificates, the handed
log committed and raft's durable state at the view's, the invariant, the loop's half of the view
(nothing pending) with its token, the stop's claim, the apply thread's token, the handed log's lower
bound, and the crash token. -/
abbrev rnDurK_alloc.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (x : CrashNames) (sd : w64 → IProp GF) (h : WalH GF) (σ : StorContents)
    (Hs : WalHist) (n : Nat) (v : WalView),
    ViewOk v σ → v.pend = none → DurAgrees v.S v.l →
    HistOkK (v, none) Hs n →
    ⊢ walRecsH h σ Hs true -∗ walSnapCert γn.cl σ -∗ (letI := h.W; WalFs.walSyncedLb h.dir n) -∗
      walHistCerts γn.cl sd Hs -∗ isCommittedLogLb γn.cl v.l -∗ raftState γn.cl id v.S ={⊤}=∗
      ∃ νk : WalNamesK GF, ⌜νk.x = x ∧ νk.sd = sd⌝ ∗ rnDurInvK γn id νk h ∗ rnWalViewK νk (v, none) ∗
        token νk.ν.stop ∗ token νk.ν.app ∗ walCommitLb νk.ν v.l ∗ token νk.tk

/-- **The loop's `Save` of a batch without a snapshot** (`rnDur_save_au` with the crash side): from
the loop's half at the idle view `(v, none)`, a `Save` step to `v'` (`WalSaveStep`), the new prefix
reading the saved records (`walRead_of_fold`: their base at or below their commit) and the batch's
*enter* record saved at `γb` (`rnPendRec`, the loop keeping the saved proposition): at the commit,
the batch pending at its record's position `|Hs|` (`(v', some (v, γb, |Hs|))`), its record deposited (dropped on the crashed side), the
handed log committed (`isCommittedLogLb`), and the history `Hs` the `Save` committed at given to the
loop (`walSaveH.law`'s `Q`), with the handed log's lower bound. -/
abbrev rnDurK_save.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (v v' : WalView) (hs : HardStateM)
    (es : List EntryM) (γb : GName) (n : NodeH) (st st' : NodeDriverState) (ms : List QMsg) (q : Qp),
    WalSaveStep v v' hs es → DurAgrees v.S v.l →
    (∀ e ∈ es, uint.nat e.Index' ≤ 2 ^ 61 - 1) → uint.nat v'.S.commit ≤ v'.S.last →
    ⊢ rnDurInvK γn id νk h -∗ rnWalViewK νk (v, none) -∗ isCommittedLogLb γn.cl v'.l -∗
      savedPropOwn γb DFrac.discard (rnPendRec γn id νk.x v.S v'.S n st st' ms q) -∗
      rnPendRec γn id νk.x v.S v'.S n st st' ms q -∗
      AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs true ∗ ⌜WalSaveOk σ es⌝ }>
        @ WalFs.walAuMask, ∅
        <{ walRecsH h (walSave σ hs es) (Hs ++ [WalOpG.save hs es]) true,
          COMM rnWalViewK νk (v', some (v, γb, Hs.length)) ∗ walCommitLb νk.ν v'.l ∗
            ⌜∃ σ', walRead (Hs ++ [WalOpG.save hs es]) = some σ'⌝ }>

/-- **The received snapshot's `SaveSnap`** (`rnDur_saveSnap_au` with the crash side): the view's
snapshot pending; the new prefix reads as the one before (its snapshot record is above the last
saved commit, `walKeep`), so the crash facts are kept; the record synced. -/
abbrev rnDurK_saveSnap.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (v : WalView) (m : SnapshotMetadataM)
    (al : Bool),
    WalSnapStep v m → uint.nat m.Index' ≤ 2 ^ 61 - 1 →
    ⊢ rnDurInvK γn id νk h -∗ rnWalViewK νk (v, none) -∗ snapshotValid γn.cl (SnapshotM.mk [] m) -∗
      □ νk.sd m.Index' -∗
      AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs true ∗
            ⌜uint.nat m.Index' = σ.b → m.Term' = σ.base.term'⌝ }> @ WalFs.walAuMask, ∅
        <{ walRecsH h (walSaveSnap σ m) (Hs ++ [WalOpG.snap m al]) true,
          COMM rnWalViewK νk ({ v with pend := some m }, none) ∗ walBaseLb h (uint.nat m.Index') }>

/-- **The loop's *enter*, after its `Save` returned** (`rn_enter` with the crash side): with
`notCrashed` (which refutes the crashed side), the loop's half at the pending view `(v', some (v,
γb, pos))`, its saved proposition at `γb`, two later credits (the body's later and the record's
agreement), and either the sync's
lower bound past the `Save`'s record `pos` (`walSaveH.law`'s post) or a
commit-only batch (every record that held `v.S` within `v.l` holds `v'.S` within `v'.l`:
`RaftState.next` keeps `wcommit`): raft enters the batch (`readyEnterLive`), the durable state moves
to `v'.S`, nothing pending; the loop gets the busy driver's state, the messages' sends and the share
`q` of the liveness it deposited back. -/
abbrev rnDurK_enter.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (v v' : WalView) (γb : GName)
    (pos : Nat) (n : NodeH) (st st' : NodeDriverState) (ms : List QMsg) (q : Qp),
    letI := srvStor (GF := GF) γn;
    (⊢ rnDurInvK γn id νk h -∗ notCrashed -∗ £ 1 -∗ £ 1 -∗ rnWalViewK νk (v', some (v, γb, pos)) -∗
      savedPropOwn γb DFrac.discard (rnPendRec γn id νk.x v.S v'.S n st st' ms q) -∗
      ((letI := h.W; WalFs.walSyncedLb h.dir (pos + 1)) ∨
        ⌜∀ σ, ImgOk v.S v.l σ → ImgOk v'.S v'.l σ⌝) ={⊤}=∗
      notCrashed ∗ rnWalViewK νk (v', none) ∗ nodeDriver n γn.cl srvClusterN st' ∗
        readyMsgs γn.cl srvClusterN id ms ∗ nodeRunning n γn.cl srvClusterN q)

/-- **The apply thread's own `SaveSnap`** (`rnDur_ownSnap_au` with the crash side): at an index of a
handed log `l` it learned, at the term `l` has there; every complete prefix keeps holding the state
it held (`walOwnSnap_holds`, for the pending batch's states too). -/
abbrev rnDurK_ownSnap.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (md : SnapshotMetadataM)
    (l : List LogEntry) (e : LogEntry) (al : Bool),
    0 < uint.nat md.Index' → l[uint.nat md.Index' - 1]? = some e → e.term = md.Term' →
    uint.nat md.Index' ≤ 2 ^ 61 - 1 →
    ⊢ rnDurInvK γn id νk h -∗ token νk.ν.app -∗ walCommitLb νk.ν l -∗
      snapshotValid γn.cl (SnapshotM.mk [] md) -∗ □ νk.sd md.Index' -∗
      AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs true ∗
            ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }> @ WalFs.walAuMask, ∅
        <{ walRecsH h (walSaveSnap σ md) (Hs ++ [WalOpG.snap md al]) true,
          COMM token νk.ν.app ∗ walBaseLb h (uint.nat md.Index') }>

/-- **The stop takes the records and raft's state out** (`rnDur_take` with raft's state: the stop's
image holds it), the loop idle at the view `(v, none)`, with `notCrashed` and a later credit (raft's
state is under the invariant's later). -/
abbrev rnDurK_take.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (v : WalView),
    v.pend = none →
    ⊢ rnDurInvK γn id νk h -∗ notCrashed -∗ £ 1 -∗ token νk.ν.stop -∗ token νk.ν.app -∗
      rnWalViewK νk (v, none) ={⊤}=∗
      notCrashed ∗ rnTakenK νk ∗ raftState γn.cl id v.S ∗ ∃ σ : StorContents, walRecs h σ true ∗
        ⌜StorageHolds v.S σ ∧ σ.b ≤ v.l.length ∧ v.l.length ≤ σ.commit ∧ σ.hs = v.hs ∧
          DurAgrees v.S v.l⌝ ∗ walSnapCert γn.cl σ

/-- **The crash** (the deliverable for T7, `notes/etcd-dist-d6.md` §10): after the crash of the
generation (`crashed`), with the invariant's crash token and raft's crash token of the arm `νk.x`,
the WAL's crash `Φ` runs with the records borrowed (`walRecsH` at the history `Hs`, the synced lower
bound `n`: T5's lemma with `walSaveAtomic.law`, which turns the image into a complete prefix `j`, `n ≤
j ≤ |Hs|`, read as `σ`); then raft's durable state is one that `σ` holds (the pending batch entered
by `readyCrashEnter` or dropped by `nodeCrash`), with the id's vacancy, the image's snapshot
certificate and a committed log the state agrees with, within which the image's base lies
(`wal.crashImage`'s rows but the read facts and the backend's index). Or the stop had taken the
records (`rnTakenK`: the graceful stop's image, `rnDurK_take.law`, is the stopped server's, not the
crash's; a member that never stops its server excludes it).

(P8, 2026-11-25; T5's proposal (3), `notes/wal-p8-handoff.md`) The WAL's crash gives the prefix `j` and
`Φ` of whatever it reads (`walRecsH_crash`, `WalRecsH.lean`: whether the read succeeds is not the WAL's
but this invariant's, `CrashReadsHold`), and the image's read facts `walReadFacts σ` come from the
invariant's `HistReadOk` (`walReadFacts_of_read`). -/
abbrev rnDurK_crash.law : Prop :=
  ∀ (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (E : CoPset) (Φ : StorContents → IProp GF),
    ↑rnDurKN ⊆ E → ↑srvClusterN ⊆ E \ ↑rnDurKN →
    letI := srvStor (GF := GF) γn;
    (⊢ rnDurInvK γn id νk h -∗ isCluster γn.cl srvClusterN -∗ £ 1 -∗ crashed -∗ token νk.tk -∗
      nodeCrashTok γn.cl id νk.x -∗
      (∀ (σr : StorContents) (Hs : WalHist) (n : Nat),
        walRecsH h σr Hs true -∗ (letI := h.W; WalFs.walSyncedLb h.dir n) ={E \ ↑rnDurKN}=∗
          walRecsH h σr Hs true ∗
          ∃ j : Nat, ⌜n ≤ j ∧ j ≤ Hs.length⌝ ∗
            ∀ σ : StorContents, ⌜walRead (Hs.take j) = some σ⌝ -∗ Φ σ) ={E}=∗
      (∃ (S : RaftState) (σ : StorContents) (l : List LogEntry), Φ σ ∗
        raftState γn.cl id S ∗ nodeVacant γn.cl id ∗
        ⌜StorageHolds S σ ∧ σ.b ≤ l.length ∧ DurAgrees S l ∧ walReadFacts σ⌝ ∗ walSnapCert γn.cl σ ∗
        walSnapDur νk.sd σ ∗
        isCommittedLogLb γn.cl l) ∨
      rnTakenK νk)

end defs

end EtcdGrove
end Perennial
