/-
`member.close.wp_proof` (W4c U5): `Close` with its update committed on the tester's invariant (the WAL
state unchanged: the program's `tWalOwn` half agrees with the invariant's), then, on success,
`storeOracle` of the synced oracle (`tRelI_synced` from `Close`'s `walSyncedLb`). Lean-first (no Rocq
counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__syncLemmas
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__closeLemmas

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

theorem member.close.wp_proof
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_Close : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (W := W) (Sio := ioNone) (walRaftP (GF := GF))
        walRaftMr) :
    member.close.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc hf hok hsm hcwf
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Hpath, Hw, Hov, Hrep, Ho, Hwo, #Harea, Hwf,
    Hpw, #Hnm⟩
  wp_auto
  -- the member's handle, shared (the tester assumes nothing of I/O errors: `ioNone`); `Close` takes the
  -- whole share
  iapply fupd_wp
  imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ 0 $$ [Hwf]
    with ⟨%γs, Hws, %hγ0⟩
  · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ 0 walCov_ioNone $$ Hwf
  rcases γs with ⟨γs1, γs2, γsi⟩; dsimp only at hγ0; subst hγ0
  let γs : WalShN := ⟨γs1, γs2, 0⟩
  imodintro
  wp_apply (wp_Close W e.R e.jr (e.area) w (tWalDir e.area) (.shared γs)
      (fun d' => iprop(⌜d' = d⌝ ∗ tWalOwn γ (some d)))) $$ [Hws Hpw Hwo]
    as %err Hr
  · dsimp only
    iframe; iframe #
    iapply tInv_walAu W e γ d
    iframe; iframe #
  icases Hr with (⟨-, %d1, ⟨%hd1, Hwo⟩, #Hsl, Htok, Hp1⟩ | %Herr)
  · subst hd1
    cases err with
    | ok ie =>
      wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
    | nil =>
    wp_auto
    ihave ⟨%hl, Hrep⟩ := oracleRep_synced v o $$ Hrep
    ihave #Hrel := tRelI_synced W e.area o c d1 hok hl hcwf $$ [Hsl Hnm]
    · isplitl []
      · iexact Hsl
      · iexact Hnm
    iunfold tPerm at Hperm
    icases Hperm with ⟨Hpw_, Hperm⟩
    wp_apply (wp_store W e γ _ os (tSynced o) (some d1) 1 hf hsm) $$ [Hh Hperm Hrep Ho Hwo]
      as ⟨Hh, Hperm, Hrep, Ho, Hwo⟩
    · iframe; iframe #
    ihave Hperm : tPerm (GF := GF) e qc $$ [Hpw_ Hperm]
    · iunfold tPerm; iframe
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    iframe #
  · cases err with
    | nil => exact absurd rfl Herr.1
    | ok ie =>
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
