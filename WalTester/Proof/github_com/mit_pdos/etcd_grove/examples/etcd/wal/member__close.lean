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
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

/-- The tester's invariant is in the WAL's updates' mask. -/
theorem tN_sub_walAu : (↑tN : CoPset) ⊆ WalFs.walAuMask := by
  have h1 : (↑tN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  have h2 : (↑tN : CoPset) ## ↑osShN := ndot_ne_disjoint nroot (by decide)
  have h3 : (↑tN : CoPset) ## ↑WalFs.walN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨LawfulSet.mem_diff.2 ⟨LawfulSet.mem_diff.2
    ⟨CoPset.mem_full, fun hn => h1 p ⟨hp, hn⟩⟩, fun hn => h2 p ⟨hp, hn⟩⟩, fun hn => h3 p ⟨hp, hn⟩⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The WAL state's halves agree. -/
theorem tWalOwn_agree (γ : TGS) (od od' : Option WalDur) :
    ⊢@{IProp GF} tWalOwn γ od -∗ ghostVar γ.γw (1 : Qp).half od' -∗ ⌜od' = od⌝ := by
  unfold tWalOwn
  iintro H1 H2
  icases ghostVar_agree (GF := GF) γ.γw od (1 : Qp).half od' (1 : Qp).half $$ H1 H2 with %h
  ipureintro; exact h.symm

/-- **`Close`'s update, committed on the tester's invariant with the WAL state unchanged.** -/
theorem tInv_walAu (W : WalGS GF) (e : TEnv) (γ : TGS) (d : WalDur) :
    TInv (W := W) e γ ∗ tWalOwn γ (some d) ⊢
      AU <{ ∃∃ d' : WalDur, WalFs.walDiskAt (W := W) (tWalDir e.area) d' }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAt (W := W) (tWalDir e.area) d', COMM ⌜d' = d⌝ ∗ tWalOwn γ (some d) }> := by
  iintro ⟨#Hinv, Hwo⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  unfold WalFs.walDiskAt
  iexists d
  iframe Hwd
  isplit
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, oa, some d; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, oa, some d; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
    ipureintro; rfl

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
  imod walOpenWS_alloc (W := W) ioNone (walRaftP (GF := GF)) walRaftMr w (tWalDir e.area) ⊤ $$ [Hwf]
    with ⟨%γs, Hws⟩
  · iapply walHdl_of_wf (W := W) ioNone _ _ _ _ walCov_ioNone $$ Hwf
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
    wp_apply (wp_store W e γ _ os (tSynced o) (some d1) qc hf hsm) $$ [Hh Hperm Hrep Ho Hwo]
      as ⟨Hh, Hperm, Hrep, Ho, Hwo⟩
    · iframe; iframe #
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
