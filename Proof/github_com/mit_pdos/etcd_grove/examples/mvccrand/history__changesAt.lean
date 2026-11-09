/- Lean-first (no Rocq counterpart). The proof of `history.changesAt`: under the read lock the
revisions extend the caller's lower bound, so `r` is in range and its changes' slice is the
lower bound's. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__changesAt
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

theorem history.changesAt.wp_proof (wp_check : check.spec (GF := GF) (hG := hG)) :
    history.changesAt.spec (GF := GF) (hG := hG) := by
  intro h γ Hlb r hr0 hr
  wp_start as ⟨Hrd, #Hlb⟩
  iunfold histRd at Hrd
  icases Hrd with ⟨#Hh, Hown⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hown] as ⟨Hrl, HP⟩
  iunfold histR at HP
  icases HP with ⟨%x, Hs, Hc, Hg, Hl, #He⟩
  ihave %Hpre := mono_list_auth_lb_valid γ.l _ _ _ $$ Hl Hlb
  iunfold histElems at He
  icases He with ⟨%H2, #Hms, #Hcs, #Hst, #Hch⟩
  ihave %Hcl := ownSlice_len $$ Hcs
  ihave Hchl : (⌜x.2.2.2.1.length = x.2.2.2.2.length⌝ ∗
      [∗list] y ∈ x.2.2.2.1.zip x.2.2.2.2, y.1 ↦*□ y.2.2 : IProp GF) $$ [Hch]
  · iunfold changesP at Hch; iexact Hch
  icases Hchl with ⟨%Hcsl, #Hchs⟩
  have hlen : Hlb.length ≤ x.2.2.2.2.length := Hpre.2.length_le
  have hrl : sint.Z r < sint.Z x.2.1.len := by
    have h1 : sint.nat x.2.1.len = (sint.Z x.2.1.len).toNat := rfl
    have h2 : sint.nat r = (sint.Z r).toNat := rfl
    omega
  wp_auto
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; word
  (try wp_auto)
  obtain ⟨y, hy⟩ : ∃ y, Hlb[sint.nat r]? = some y :=
    ⟨Hlb[sint.nat r]'hr, List.getElem?_eq_getElem hr⟩
  have hyx : x.2.2.2.2[sint.nat r]? = some y := prefix_getElem? Hpre.2 hy
  have hidx : sint.nat r < x.2.2.2.1.length := by omega
  have hcs : (x.2.2.2.1.zip x.2.2.2.2)[sint.nat r]? = some (x.2.2.2.1[sint.nat r]'hidx, y) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨List.getElem?_eq_getElem hidx, hyx⟩
  ihave #Hcy := BigSepL.bigSepL_lookup hcs $$ Hchs
  have hb : 0 ≤ sint.Z r ∧ sint.Z r < sint.Z x.2.1.len := ⟨hr0, hrl⟩
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index x.2.1 (sint.Z r) x.2.2.2.1 DFrac.discard
    (x.2.2.2.1[sint.nat r]'hidx) hr0 $$ [Hcs] as -
  · iframe #; ipureintro; exact List.getElem?_eq_getElem hidx
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl Hs Hc Hg Hl] as Hown
  · inext
    iunfold histR
    iexists x
    iframe
    iunfold histElems
    iframe #
    ipureintro; exact H2
  wp_auto
  iapply HΦ
  iunfold histRd
  iframe #
  iframe
  ipureintro; rw [hy]; rfl

end proof

end mvccrand
end EtcdGrove
end Perennial
