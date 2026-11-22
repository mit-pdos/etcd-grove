/-
# kvnet's start: `RestartNode`'s update over the generation's file invariant (2026-11-22)

`notes/kvnet-part.md`, "`StartNode` and the crash frame". kvdurable's `kd_restartAu` over kvnet's file
invariant (`kdFileInvK`, allocated at the generation's boot with a crashed side): `RestartNode` lends its
update the generation's `notCrashed` (ledger 2026-11-22, raft's `RestartNode`), which refutes that side.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.BootLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
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

end raft_kvnet
end EtcdGrove
end Perennial
