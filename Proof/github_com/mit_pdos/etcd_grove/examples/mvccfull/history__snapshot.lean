/- Lean-first (no Rocq counterpart). The proof of `history.snapshot` (mvccrand's): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot

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

theorem history.snapshot.wp_proof :
    history.snapshot.spec (GF := GF) (hG := hG) := by
  intro h γ Hlb
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
  ihave #Hlb' := monoListLbOwn_get γ.l _ x.revs $$ Hl
  iunfold histElems at He
  icases He with ⟨%H2, #Hms, #Hcs, #Hcps, #Hst, #Hch⟩
  ihave %Hmlen : ⌜x.ms.length = x.revs.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  ihave %Hmsl := ownSlice_len $$ Hms
  ihave %Hmsw := ownSlice_wf $$ Hms
  wp_auto
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z x.states.len ∧
      sint.Z x.states.len ≤ sint.Z x.states.len ∧ sint.Z x.states.len ≤ sint.Z x.states.cap) = True from
    eq_true ⟨by decide, Hmsl.2, Int.le_refl _, Hmsw.2⟩, ↓reduceIte]
  wp_auto
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
  isplitr
  · ipureintro; exact ⟨Hpre.2, H2⟩
  isplitr
  · ipureintro; simp [slice.fullSlice]
  have hne : x.ms ≠ [] := by
    intro he; rw [he] at Hmlen; simp at Hmlen; omega
  iapply ownSlice_same_ptr_len' x.states _ DFrac.discard x.ms hne _ _ _ $$ Hms
  · simp [slice.fullSlice, sliceIndexRef, go.arrayIndexRef_0]
  · simp [slice.fullSlice]
  · simp [slice.fullSlice]

end proof

end mvccfull
end EtcdGrove
end Perennial
