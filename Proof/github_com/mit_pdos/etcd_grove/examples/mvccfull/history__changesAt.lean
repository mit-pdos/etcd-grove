/- Lean-first (no Rocq counterpart). The proof of `history.changesAt` (mvccrand's): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__changesAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem history.changesAt.wp_proof
    (wp_check : check.spec (GF := GF) (hG := hG)) :
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
  icases HP with ⟨%x, Hs, Hc, Hp, Hg, Hl, #He⟩
  ihave %Hpre := mono_list_auth_lb_valid γ.l _ _ _ $$ Hl Hlb
  iunfold histElems at He
  icases He with ⟨%H2, #Hms, #Hcs, #Hcps, #Hst, #Hch⟩
  ihave %Hcl := ownSlice_len $$ Hcs
  ihave Hchl : (⌜x.cs.length = x.revs.length⌝ ∗
      [∗list] y ∈ x.cs.zip x.revs, y.1 ↦*□ y.2.2 : IProp GF) $$ [Hch]
  · iunfold changesP at Hch; iexact Hch
  icases Hchl with ⟨%Hcsl, #Hchs⟩
  have hlen : Hlb.length ≤ x.revs.length := Hpre.2.length_le
  have hrl : sint.Z r < sint.Z x.changes.len := by
    have h1 : sint.nat x.changes.len = (sint.Z x.changes.len).toNat := rfl
    have h2 : sint.nat r = (sint.Z r).toNat := rfl
    omega
  wp_auto
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; word
  (try wp_auto)
  obtain ⟨y, hy⟩ : ∃ y, Hlb[sint.nat r]? = some y :=
    ⟨Hlb[sint.nat r]'hr, List.getElem?_eq_getElem hr⟩
  have hyx : x.revs[sint.nat r]? = some y := prefix_getElem? Hpre.2 hy
  have hidx : sint.nat r < x.cs.length := by omega
  have hcs : (x.cs.zip x.revs)[sint.nat r]? = some (x.cs[sint.nat r]'hidx, y) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨List.getElem?_eq_getElem hidx, hyx⟩
  ihave #Hcy := BigSepL.bigSepL_lookup hcs $$ Hchs
  have hb : 0 ≤ sint.Z r ∧ sint.Z r < sint.Z x.changes.len := ⟨hr0, hrl⟩
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index x.changes (sint.Z r) x.cs DFrac.discard
    (x.cs[sint.nat r]'hidx) hr0 $$ [Hcs] as -
  · iframe #; ipureintro; exact List.getElem?_eq_getElem hidx
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl Hs Hc Hp Hg Hl] as Hown
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

end mvccfull
end EtcdGrove
end Perennial
