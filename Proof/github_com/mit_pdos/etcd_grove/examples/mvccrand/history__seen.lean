/- Lean-first (no Rocq counterpart). The proof of `history.seen`: the two checks by the premises
(the snapshot's revisions extend the lower bound), then the counter's add in its invariant. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__seen
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem history.seen.wp_proof (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG)) :
    history.seen.spec (GF := GF) (hG := hG) := by
  intro h γ Hlb floor cur what hfc hc
  wp_start as ⟨Hrd, #Hlb⟩
  wp_auto
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; exact hfc
  (try wp_auto)
  wp_apply wp_snapshot h γ Hlb $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, -, #Hms, #Hst⟩
  ihave %Hmsl := ownSlice_len $$ Hms
  ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  have hlen : Hlb.length ≤ Hs.length := Hpre.1.length_le
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]
    have h1 : sint.nat s.len = (sint.Z s.len).toNat := rfl
    word
  (try wp_auto)
  iunfold histRd at Hrd
  icases Hrd with ⟨#Hh, Hown⟩
  iunfold isHistory at Hh
  icases Hh with ⟨#Hg, #Hinv⟩
  wp_if_destruct
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply_core sync.atomic.Int64.wp_Add (hAbove h) (W64 1) $$ [] [-]
      · iPkgInit
      iinv Hinv with Ha Hclose
      iunfold aboveInv at Ha
      icases Ha with ⟨%a, >Ha⟩
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑histN from Std.LawfulSet.empty_subset)
      iintro Hcl
      inext
      iexists a
      iframe
      iintro Ha
      imod Hcl with -
      imod Hclose $$ [Ha] with -
      · inext; iunfold aboveInv; iexists _; iframe
      imodintro
      (try wp_auto)
      iapply HΦ
      iunfold histRd; iunfold isHistory
      iframe #
      iframe
    · (try wp_auto)
      iapply HΦ
      iunfold histRd; iunfold isHistory
      iframe #
      iframe
  · (try wp_auto)
    iapply HΦ
    iunfold histRd; iunfold isHistory
    iframe #
    iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
