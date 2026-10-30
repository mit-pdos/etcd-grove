module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Read
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
public import Spec.sort.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.Read.wp_proof (hIs : Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (hIds : Page.FreelistPageIds.spec (GF := GF) (hG := hG))
    (hSort : sort.Sort.spec (GF := GF) (hG := hG)) :
    shared.Read.spec (GF := GF) (hG := hG) := by
  intro I s σ p pv dq c xs dq2 hInit Hnn Hfl Hov Hnd Hxs Hlen Hemp
  wp_start as ⟨#Hhdl, Hsh, Hown, Hp, Hcc, Hsl⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases ownSharedW_wfw _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
  wp_auto
  wp_apply (hIs p pv dq) $$ [Hp] as Hp
  · iexact Hp
  rw [decide_eq_true Hfl]
  try wp_auto
  wp_apply (hIds p pv dq c Hnn Hfl Hov) $$ [Hp Hcc] as ⟨Hp, Hcc⟩
  · iframe
  try wp_auto
  iunfold fpIdsSlice at Hsl
  ihave %Hxl := ownSlice_len _ _ _ $$ Hsl
  by_cases Hz : fpCount pv c = W64 0
  · simp only [Hz, ite_true] at Hxl ⊢
    try isimp only [Hz, ite_true] at Hsl
    have Hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hxl.1]; rfl)
    subst Hx0
    rw [decide_eq_true (show (slice.nil : GoSlice).len = W64 0 from rfl)]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl0, Hslc⟩
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    unfold ownSharedW ownSharedC
    icases Hsh with ⟨%sv, %c', Hsh, %Hok⟩
    iNamed Hsh
    try wp_auto
    rw [Hiface]
    unfold FLImpl.iface
    try wp_auto
    ihave Hsh : ownSharedW s I.iface σ $$ [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
    · unfold ownSharedW ownSharedC
      iexists sv, c'
      iframe
      ipureintro; exact ⟨Hiface, Hok⟩
    have Hwf' : ({ σ with free := [] } : FLState).WFw :=
      Hwf.with_free (by simp [PgidsIncr]) (by simp) (by simpa using Hlen)
    wp_bind (App (Val #(methods I.ity go!"Init" I.iv)) _)
    iapply (hInit s σ _ [] Hwf' (Or.inr (Hemp.resolve_left (by simp)))) $$ [Hsh Hown Hsl0 Hslc]
    · iframe
      isplitl []
      · iexact Hpkg
      iexact Hhdl
    inext
    iintro ⟨Hsh, Hown⟩
    try wp_auto
    iapply HΦ
    rw [show fpIdsSlice p pv c = slice.nil by simp [fpIdsSlice, Hz]]
    iframe
    isplitr
    · ipureintro; exact ⟨by simp [PgidsIncr], List.Perm.refl _⟩
    iunfold ownSharedW, ownSharedC at Hsh
    iExactEq Hsh; rfl
  · simp only [Hz, ite_false] at Hxl ⊢
    try isimp only [Hz, ite_false] at Hsl
    rw [decide_eq_false (fun h => h)]
    try wp_auto
    wp_apply (wp_slice_make2 (V := w64) (fpCount pv c)) as %cp ⟨Hcp, Hcpc⟩
    · ipureintro
      unfold fpCount
      by_cases h : fpOverflow pv
      · rw [if_pos h]; exact Hov h
      · rw [if_neg h]; word
    try wp_auto
    wp_apply (wp_slice_copy cp _ _ xs dq2) $$ [Hcp Hsl] as %nc ⟨_, Hcp, Hsl⟩
    · iframe
    have hxl : xs.length = sint.nat (fpCount pv c) := Hxl.1
    rw [show xs.take (List.replicate (sint.nat (fpCount pv c)) (zero_val w64)).length ++
        (List.replicate (sint.nat (fpCount pv c)) (zero_val w64)).drop xs.length = xs by
      rw [List.length_replicate, ← hxl, List.take_length, List.drop_replicate, Nat.sub_self,
        List.replicate_zero, List.append_nil]]
    try wp_auto
    wp_apply (hSort _ cp xs (Or.inl rfl)) $$ [Hcp] as %ys ⟨%Hys, Hcp⟩
    · iexact Hcp
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    unfold ownSharedW ownSharedC
    icases Hsh with ⟨%sv, %c', Hsh, %Hok⟩
    iNamed Hsh
    try wp_auto
    rw [Hiface]
    unfold FLImpl.iface
    try wp_auto
    ihave Hsh : ownSharedW s I.iface σ $$ [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
    · unfold ownSharedW ownSharedC
      iexists sv, c'
      iframe
      ipureintro; exact ⟨Hiface, Hok⟩
    have Hinc : PgidsIncr ys := pgidsIncr_of_sorted_nodup Hys.1 (Hys.2.nodup_iff.2 Hnd)
    have Hwf' : ({ σ with free := ys } : FLState).WFw :=
      Hwf.with_free Hinc (fun x hx => Hxs x (Hys.2.mem_iff.1 hx))
        (by rw [Hys.2.length_eq]; exact Hlen)
    have Hyne : ys ≠ [] := by
      intro h; subst h
      have h0 : xs.length = 0 := by have := Hys.2.length_eq; simpa using this.symm
      apply Hz; rw [h0] at hxl; word
    wp_bind (App (Val #(methods I.ity go!"Init" I.iv)) _)
    iapply (hInit s σ _ ys Hwf' (Or.inl Hyne)) $$ [Hsh Hown Hcp Hcpc]
    · iframe
      isplitl []
      · iexact Hpkg
      iexact Hhdl
    inext
    iintro ⟨Hsh, Hown⟩
    try wp_auto
    iapply HΦ
    rw [show fpIdsSlice p pv c =
      slice.mk (p +ₗ (16 + 8 * uint.Z (fpIdx pv))) (fpCount pv c) (fpCount pv c) by
        unfold fpIdsSlice; rw [if_neg Hz]]
    iframe
    isplitr
    · ipureintro; exact ⟨Hinc, Hys.2⟩
    iunfold ownSharedW, ownSharedC at Hsh
    iExactEq Hsh; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
