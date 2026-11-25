/-
The lemmas of `member__close.lean`'s proof (`tN_sub_walAu`, `tWalOwn_agree`, `tInv_walAu`), in a
module of their own so that `RestartAu.lean` and `SaveAu.lean` import them without the proof
(import tiers, 2026-11-18).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
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
      AU <{ ∃∃ d' : WalDur, WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d' }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d', COMM ⌜d' = d⌝ ∗ tWalOwn γ (some d) }> := by
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
  unfold WalFs.walDiskAtI
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

end proof

end etcd_wal
end EtcdGrove
end Perennial
