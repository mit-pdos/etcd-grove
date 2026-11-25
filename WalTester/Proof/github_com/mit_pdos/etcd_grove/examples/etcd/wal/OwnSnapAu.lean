/- Lean-first (no Rocq counterpart).

**`ReleaseLockTo`'s update, committed on the tester's invariant** (W4c U5, tenth session): the WAL state
`d` moves to `tReleaseD d a` (its unlock position raised to `walReleasePos`); the stored oracle `o1`
(`opOwnSnap`'s raised one) accounts for it through the member's raised candidate, at its mark.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SaveAu
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OwnSnapPure

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

/-- **`ReleaseLockTo`'s update, committed on the tester's invariant.** -/
theorem tInv_releaseAu (W : WalGS GF) (e : TEnv) (γ : TGS) (o1 : TOracle) (c1 : TCand) (d : WalDur)
    (a t : w64) (i n : Nat) (cs : ConfStateM) (hcr : o1.created = true) (hc : c1 ∈ o1.cands)
    (hok : tCandOk o1 c1 (tReleaseD d a)) (hH : d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩ true))
    (hin : i < n) :
    TInv (W := W) e γ ∗ tWalOwn γ (some d) ∗ tOrOwn γ o1 none ∗
      WalFs.walSyncedLb (W := W) (tWalDir e.area) 0 (tCandMark o1 c1) ∗
      WalFs.walNamed (W := W) (tWalDir e.area) 0 ⊢
      AU <{ ∃∃ d' : WalDur, WalFs.walDiskAtI (W := W) (tWalDir e.area) 0 d' ∗
            ⌜(∃ al, d'.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩ al)) ∧ i < n⌝ }>
          @ WalFs.walAuMask, ∅
        <{ WalFs.walDiskAtI (W := W) (tWalDir e.area) 0
            { d' with unl := max d'.unl (walReleasePos (d'.H.map WalOpG.toM) a) },
          COMM ⌜d' = d⌝ ∗ tWalOwn γ (some (tReleaseD d a)) ∗ tOrOwn γ o1 none }> := by
  iintro ⟨#Hinv, Hwo, Hoo, #Hsl, #Hnm⟩
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o2, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  ihave %hao := tOrOwn_agree (W := W) γ o1 o2 none oa $$ Hoo Ho1
  obtain ⟨h1, h2⟩ := hao
  subst h2; subst o2
  ihave %hw1 := tRelI_checkWf e.area o1 (some d) hcr $$ Hr1
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  unfold WalFs.walDiskAtI
  iexists d
  iframe Hwd
  isplitr
  · ipureintro; exact ⟨⟨true, hH⟩, hin⟩
  isplit
  · iintro ⟨Hwd, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, none, some d; iframe; iframe #
      ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hwd
    iunfold tWalOwn at Hwo
    imod ghostVar_update_halves (some (tReleaseD d a)) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, none, some (tReleaseD d a)
      unfold tReleaseD
      iframe; iframe #
      isplitr
      · ipureintro; exact hfile
      isplitl
      · iunfold tRelI
        simp only [hcr, ↓reduceIte]
        iexists tReleaseD d a, c1
        iframe #
        ipureintro; exact ⟨rfl, hc, hok, hw1⟩
      · simp only [tRelA]; iempintro
    imodintro
    unfold tWalOwn
    iframe
    ipureintro; rfl

end proof

end etcd_wal
end EtcdGrove
end Perennial
