/-
`member.sync.wp_proof` (W4c U5): `Sync`, then `storeOracle` of the synced oracle, whose `tRelI` is the
candidate's (`tMemOk_candOk`) with `Sync`'s `walSyncedLb` at the whole history. Lean-first (no Rocq
counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOpsLemmas
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SnapPure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__syncLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem member.sync.wp_proof
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_Sync : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.spec (W := W) (Sio := ioNone) (walRaftP (GF := GF))
        walRaftMr) :
    member.sync.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc hf hok hsm hcwf
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Hpath, Hw, Hov, Hrep, Ho, Hwo, #Harea, Hwf,
    #Hlen, #Hnm⟩
  wp_auto
  -- the member's handle, shared for the call (the tester assumes nothing of I/O errors: `ioNone`) and taken
  -- back after it
  iapply fupd_wp
  imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ 0 $$ [Hwf]
    with ⟨%γs, Hws, %hγ0⟩
  · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ 0 walCov_ioNone $$ Hwf
  rcases γs with ⟨γs1, γs2, γsi⟩; dsimp only at hγ0; subst hγ0
  let γs : WalShN := ⟨γs1, γs2, 0⟩
  imodintro
  wp_apply (lc := 1) (wp_Sync W e.R e.jr (e.area) w (tWalDir e.area) γs 1 d.H.length) $$ [Hws]
    as %err Hr
  · iframe; iframe #; ipureintro; exact Or.inr rfl
  icases Hr with (⟨%Herr, Hws, #Hsl⟩ | %Herr)
  · subst Herr
    iapply fupd_wp
    imod walOpenWS_reclaim (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) γs $$ [Hws Hlc1]
      with Hwf
    · iframe Hws Hlc1
    imodintro
    ihave Hwf := walHdl_wf (W := W) ioNone _ _ _ _ $$ Hwf
    wp_auto
    ihave ⟨%hl, Hrep⟩ := oracleRep_synced v o $$ Hrep
    ihave #Hrel := tRelI_synced W e.area o c d hok hl hcwf $$ [Hsl Hnm]
    · isplitl []
      · iexact Hsl
      · iexact Hnm
    iunfold tPerm at Hperm
    icases Hperm with ⟨Hpw_, Hperm⟩
    wp_apply (wp_store W e γ _ os (tSynced o) (some d) 1 hf hsm) $$ [Hh Hperm Hrep Ho Hwo]
      as ⟨Hh, Hperm, Hrep, Ho, Hwo⟩
    · iframe; iframe #
    ihave Hperm : tPerm (GF := GF) e qc $$ [Hpw_ Hperm]
    · iunfold tPerm; iframe
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    iframe #
  · obtain ⟨Herr, -⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
