/-
Lean-first (no Rocq counterpart).

The proof of `WatchValidator.ValidateWatch` on a watch the pure check accepts (`validateWatchL`):
`checkWatch` accepts the request (`wInPre`), the response has no error, the events pass
`validateMaybeLastEventError` and `validateBookmarks`; a watch-list (`SendInitialEvents = true`) splits
at the initial-events-end bookmark, ends there or has its initial events checked at the bookmark's
resource version and the rest checked by `validateReliable`; any other watch checks all its events by
`validateReliable`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__ValidateWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__checkWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.validateMaybeLastEventError
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__validateBookmarks
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__splitInitialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.objectRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__validateInitialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator__validateReliable

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem WatchValidator.ValidateWatch.wp_proof
    (wp_CW : WatchValidator.checkWatch.spec (GF := GF) (hG := hG))
    (wp_VMLE : validateMaybeLastEventError.spec (GF := GF) (hG := hG))
    (wp_VB : WatchValidator.validateBookmarks.spec (GF := GF) (hG := hG))
    (wp_SIE : WatchValidator.splitInitialEvents.spec (GF := GF) (hG := hG))
    (wp_ORV : objectRV.spec (GF := GF) (hG := hG))
    (wp_VIE : WatchValidator.validateInitialEvents.spec (GF := GF) (hG := hG))
    (wp_VR : WatchValidator.validateReliable.spec (GF := GF) (hG := hG)) :
    WatchValidator.ValidateWatch.spec (GF := GF) (hG := hG) := by
  intro rp R x req sl rs hpre hok
  unfold validateWatchL at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hle, hbm⟩, hrest⟩ := hok
  wp_start as ⟨#HR, #Hreq, #Hs⟩
  ihave #HR0 := HR
  iunfold replayAt at HR0
  icases HR0 with ⟨#Hd, -⟩
  ihave #Hreq0 := Hreq
  iunfold wreqRep at Hreq0
  icases Hreq0 with ⟨%p, %hreq, #Hsie⟩
  subst hreq
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"checkWatch")]
  wp_call
  (try wp_auto)
  wp_apply (wp_CW rp x _ hpre) $$ [] as %cerr %hcerr
  · iframe #
  subst hcerr
  wp_auto
  wp_apply (wp_VMLE sl rs hle) $$ [] as %e1 %he1
  · iframe #
  subst he1
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"validateBookmarks")]
  wp_call
  (try wp_auto)
  wp_apply (wp_VB rp sl rs hbm) $$ [] as %e2 %he2
  · iframe #
  subst he2
  wp_auto
  by_cases hp2 : x.SendInit' = W64 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp2)] at hrest
    have hsie : sieOfL x = some true := by simp [sieOfL, hp2]
    isimp only [hsie] at Hsie
    iunfold k8s.sendInitIs at Hsie
    ihave %hpn := typedPointsto_not_null _ _ _ $$ Hsie
    simp only [decide_eq_false hpn]
    wp_auto
    cases hsp : splitInitL rs with
    | none => rw [hsp] at hrest; cases hrest
    | some ab =>
    obtain ⟨init, rb⟩ := ab
    rw [hsp] at hrest
    rw [method_unfold (t := go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"splitInitialEvents")]
    wp_call
    (try wp_auto)
    wp_apply (wp_SIE rp sl rs init rb hsp) $$ [] as %s1 %s2 %e3 ⟨%he3, #Hs1, #Hs2⟩
    · iframe #
    subst he3
    wp_auto
    iunfold evsRO at Hs2
    icases Hs2 with ⟨%vs2, #Hs2sl, #Hvs2⟩
    ihave %Hl2 := ownSlice_len $$ Hs2sl
    ihave %Hl2' := BigSepL2.bigSepL2_length $$ Hvs2
    cases rb with
    | nil =>
      have hz : s2.len = W64 0 := by
        have : sint.nat s2.len = 0 := by rw [← Hl2.1, Hl2']; rfl
        word
      rw [hz]
      wp_auto
      iapply HΦ; ipureintro; rfl
    | cons b rest =>
    have hlen : sint.nat s2.len = rest.length + 1 := by
      have := Hl2.1; rw [Hl2'] at this; simp only [List.length_cons] at this; omega
    have hnz : s2.len ≠ W64 0 := by intro h; rw [h] at hlen; rw [show sint.nat (W64 0) = 0 from rfl] at hlen; omega
    simp only [decide_eq_false hnz]
    wp_auto
    have hlt : 0 < vs2.length := by rw [Hl2']; exact Nat.zero_lt_succ _
    obtain ⟨v0, hv0⟩ : ∃ v, vs2[0]? = some v := ⟨vs2[0], List.getElem?_eq_getElem hlt⟩
    ihave #Hv0 := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      hv0 (show (b :: rest)[0]? = some b from rfl) $$ Hvs2
    iunfold evRep at Hv0
    icases Hv0 with ⟨%hty0, #Ho0⟩
    icases ownSlice_elem_acc (0 : Int) v0 s2 DFrac.discard vs2 (Int.le_refl 0) hv0 $$ Hs2sl with ⟨#Hp0, -⟩
    iStructNamedSuffix Hp0 "_e"
    have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s2.len := ⟨by decide, by word⟩
    simp only [hb0]
    rw [show sint.Z (W64 0) = (0 : Int) from rfl]
    wp_auto
    simp only at hrest
    cases hb : objRVL b.o with
    | none => rw [hb] at hrest; simp at hrest
    | some brv =>
    rw [hb] at hrest
    simp only [Bool.and_eq_true] at hrest
    obtain ⟨hinit, hrel⟩ := hrest
    obtain ⟨o, ho, hbrv⟩ : ∃ o, b.o = .obj o ∧ o.ResourceVersion' = brv := by
      revert hb; cases b.o <;> simp [objRVL]
    isimp only [ho] at Ho0
    iunfold evObjRep at Ho0
    wp_apply (wp_ORV v0.Object' o) $$ []
    · iframe #
    rw [hbrv]
    rw [method_unfold (t := go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"validateInitialEvents")]
    wp_call
    (try wp_auto)
    wp_apply (wp_VIE rp R x _ s1 init brv hinit) $$ [] as %e4 %he4
    · iframe #
    subst he4
    wp_auto
    ihave #Hs2' : evsRO (GF := GF) s2 (b :: rest) $$ []
    · iunfold evsRO
      iexists vs2
      iframe Hs2sl Hvs2
    rw [method_unfold (t := go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"validateReliable")]
    wp_call
    (try wp_auto)
    wp_apply (wp_VR rp R x _ s2 (b :: rest) hrel) $$ [] as %e5 %he5
    · iframe #
    subst he5
    wp_auto
    iapply HΦ; ipureintro; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp2)] at hrest
    by_cases hp1 : x.SendInit' = W64 1
    · have hsie : sieOfL x = some false := by simp [sieOfL, hp1]
      isimp only [hsie] at Hsie
      iunfold k8s.sendInitIs at Hsie
      ihave %hpn := typedPointsto_not_null _ _ _ $$ Hsie
      simp only [decide_eq_false hpn]
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"validateReliable")]
      wp_call
      (try wp_auto)
      wp_apply (wp_VR rp R x _ sl rs hrest) $$ [] as %e5 %he5
      · iframe #
      subst he5
      wp_auto
      iapply HΦ; ipureintro; rfl
    · have hsie : sieOfL x = none := by
        unfold sieOfL
        split <;> (try split) <;> first | rfl | (exfalso; apply hp2; assumption)
      isimp only [hsie] at Hsie
      iunfold k8s.sendInitIs at Hsie
      icases Hsie with %hpn
      subst hpn
      simp only [_root_.decide_true]
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator.ty) (m := go!"validateReliable")]
      wp_call
      (try wp_auto)
      wp_apply (wp_VR rp R x _ sl rs hrest) $$ [] as %e5 %he5
      · iframe #
      subst he5
      wp_auto
      iapply HΦ; ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
