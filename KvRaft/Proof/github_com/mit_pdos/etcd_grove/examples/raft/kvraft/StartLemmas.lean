/-
# kvraft's start: `RestartNode`'s update over the generation's file invariant (2026-11-22)

`notes/kvraft-part.md`, "`StartNode` and the crash frame". kvdurable's `kd_restartAu` over kvraft's file
invariant (`kdFileInvK`, allocated at the generation's boot with a crashed side): `RestartNode` lends its
update the generation's `notCrashed` (ledger 2026-11-22, raft's `RestartNode`), which refutes that side.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.BootLemmas
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.KdStorageApi
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.QLogger
public import KvRaft.Proof.go_etcd_io.raft.v3.InvLogger
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Debugf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Errorf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Infof
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Warningf

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **The update `RestartNode` takes** (kvdurable's `kd_restartAu`): over the durable state in the
generation's file invariant, opened inside the update with the crash token `RestartNode` lends it
(refuting the invariant's crashed side); the writer's half pins the state at `S`, which the storage `σ`
holds. It gives the writer's half back, with the fact that the state is `S`. -/
theorem kv_restartAu (γ : KdNames) (id : w64) (fl : KdFileNames) (σ : StorContents) (S : RaftState)
    (o : Option StorFile) (Hσ : StorageHolds S σ) :
    kdFileInvK (GF := GF) γ id fl ∗ kdWriter fl S o ⊢
      (notCrashed -∗
        AU <{ ∃∃ (S' : RaftState), ▷ raftState γ.r.cluster id S' ∗ ⌜StorageHolds S' σ⌝ }>
           @ ⊤ \ ↑kdRaftN, ∅
           <{ raftState γ.r.cluster id S',
              COMM notCrashed ∗ (fun S' => iprop(kdWriter fl S o ∗ ⌜S' = S⌝)) S' }>) := by
  have : Inhabited RaftState := ⟨RaftState.init⟩
  iintro ⟨#Hinv, Hwr⟩ Hnc
  iauintro
  unfold atomic_acc
  iunfold kdFileInvK at Hinv
  iinv Hinv with HI Hclose
  · exact kdRepN_raft id
  iunfold kdFileBody at HI
  imod later_exists_except0 $$ HI with ⟨%S0, HI⟩
  imod later_exists_except0 $$ HI with ⟨%s0, HI⟩
  imod later_exists_except0 $$ HI with ⟨%pb0, HI⟩
  icases HI with ⟨Hds, Hwv, Hb⟩
  imod Hwv
  iunfold kdWriter at Hwr
  ihave %Hag := ghostVar_agree fl.wr _ _ _ _ $$ Hwr Hwv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  imod notCrashed_or_crashed $$ [$Hnc $Hb] with ⟨Hnc, Hb⟩
  icases Hb with ⟨HrS, Hfs⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kdRaftN) \ ↑(kdRepN .@ uint.nat id) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
  iframe HrS
  isplitr
  · ipureintro; exact Hσ
  isplit
  · iintro ⟨HrS, -⟩
    imod Hclose2 with -
    imod Hclose $$ [HrS Hds Hwv Hfs] with -
    · inext
      iunfold kdFileBody
      iexists S, ⟨kdFileVal o, none⟩, none
      iframe Hds Hwv
      ileft
      iframe
    imodintro
    iframe Hnc
    unfold kdWriter
    iexact Hwr
  · iintro HrS
    imod Hclose2 with -
    imod Hclose $$ [HrS Hds Hwv Hfs] with -
    · inext
      iunfold kdFileBody
      iexists S, ⟨kdFileVal o, none⟩, none
      iframe Hds Hwv
      ileft
      iframe
    imodintro
    iframe Hnc
    unfold kdWriter
    iframe Hwr
    ipureintro; rfl

end start

/-! ## The storage `StartNode` restarts from (kvdurable's `Cluster.start`'s) -/

section stor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

attribute [local instance] kdStorageModel

/-- `StartNode`'s tick, `(1 + below(4))` milliseconds, is positive. -/
theorem tick_pos (rt : w64) (h : uint.Z rt < uint.Z (W64 4)) : 0 < sint.Z ((W64 1 + rt) * W64 1000000) := by
  have h4 : uint.Z rt < 4 := by word
  have h1 : uint.Z (W64 1 + rt) = 1 + uint.Z rt := by word
  have h2 : uint.Z ((W64 1 + rt) * W64 1000000) = (1 + uint.Z rt) * 1000000 := by
    rw [word.unsigned_mul_nowrap, h1] <;> word
  word

/-- The file's contents, or the empty image if there is no file. -/
def kdImgOf (o : Option StorFile) : StorFile := o.getD imgEmpty

/-- The stored snapshot's index is the file's snapshot's (the empty one's `0` at index `0`). -/
theorem kdFreshSnap_index (f : StorFile) :
    (kdFreshSnap f).Metadata'.Index' = f.snap.Metadata'.Index' := by
  unfold kdFreshSnap
  by_cases h : f.snap.Metadata'.Index' = W64 0
  · rw [if_pos h, h]; rfl
  · rw [if_neg h]

/-- No file restores the empty image's contents. -/
theorem kdContents_none : kdContents none = kdContents (some imgEmpty) := by
  simp [kdContents, kdEmpty, imgEmpty, memSnapEmpty]

/-- The empty image passes `openStorage`'s checks. -/
theorem kdFileOk_imgEmpty : KdFileOk imgEmpty := by
  simp [KdFileOk, StorWf, SnapWf, ConfWf, imgEmpty, memSnapEmpty, KdSnapTermOk, imgTermAt]
  word

/-- **A frozen prefix cut shorter**: the entries of `xs.take n` from `k` frozen give those of
`xs.take m`, for `m ≤ n`. -/
theorem memLog_take_le (γs : MemStorNames) (k : Nat) (xs : List EntryM) (m n : Nat) (h : m ≤ n) :
    memLog (GF := GF) γs k DFrac.discard (xs.take n) ⊢ memLog γs k DFrac.discard (xs.take m) := by
  have e : xs.take n = xs.take m ++ (xs.take n).drop m := by
    conv => lhs; rw [← List.take_append_drop m (xs.take n)]
    rw [List.take_take, Nat.min_eq_left h]
  rw [e]
  iintro H
  icases (memLog_app γs k DFrac.discard _ _).1 $$ H with ⟨H, -⟩
  iexact H

/-- **The storage of the contents `F`, detached** (`openStorage`'s post, or `newStorage`'s for no
file): the variable `st` holding it, its log split at the stored snapshot's index. -/
def startStor (stp bp : Loc) (boot : ConfStateM) (F : StorFile) : IProp GF :=
  iprop(∃ (s ms ip : Loc) (γs : MemStorNames) (e0 : EntryM),
    stp ↦ s ∗ kdStorRec s ms γs ∗ kdStorBoot s bp boot ∗ memStorLock ms γs ∗
    memStorFresh ms γs (uint.nat F.prev) (kdFreshSnap F) ∗ memStorMeta ms γs F.hs ∗
    s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip F ∗ ⌜e0.Term' = F.prevTerm⌝ ∗
    memLog γs (uint.nat F.prev) DFrac.discard [e0] ∗
    memLog γs (uint.nat F.prev + 1) DFrac.discard
      (F.ents.take (uint.nat F.snap.Metadata'.Index' - uint.nat F.prev)) ∗
    memLog γs (uint.nat F.snap.Metadata'.Index' + 1) (DFrac.own 1)
      (F.ents.drop (uint.nat F.snap.Metadata'.Index' - uint.nat F.prev)) ∗
    memEnd γs (uint.nat F.prev + F.ents.length + 1) ∗
    memCompacted γs (uint.nat F.prev) ∗ memSnapLb γs (uint.nat F.snap.Metadata'.Index'))

/-- **A configuration of node `id` on the store's storage `st`, restarted at `applied`** (kvdurable's
`kdCfgOk`): what `RestartNode.spec` asks of it, with its node id, storage, logger and applied index. -/
def kvCfgOk (id : w64) (st : Loc) (applied : w64) (cv : Config) : Prop :=
  cv.ID' = id ∧ cv.Storage' = kdStorIface st ∧ cv.Logger' = GoInterface.ok qLogger ∧
  ConfigValid cv ∧ sint.Z cv.MaxInflightMsgs' < 2 ^ 62 ∧ cv.DisableProposalForwarding' = false ∧
  cv.ReadOnlyOption' = W64 0 ∧ cv.DisableConfChangeValidation' = false ∧
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) ∧
  cv.AsyncStorageWrites' = false ∧ cv.Applied' = applied ∧ TraceLoggerOk cv.TraceLogger'

/-- `quietLogger{}` is a raft `Logger` (kvdurable's `qLogger_isLogger`). -/
theorem qLogger_isLogger
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    ⊢ isLogger (GF := GF) qLogger := by
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Infof format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Debugf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Warningf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Errorf format args) $$ [] HΦ
    itrivial

end stor

end kvraft
end EtcdGrove
end Perennial
