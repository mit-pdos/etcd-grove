/-
The proof of `Spec/go_etcd_io/bbolt/DB__validMetaOverPages.lean` (W6; the fork's 2c660ee): the meta
of page `i` read in place (`pageInBuffer`, `Page.Meta`), validated, its freelist page's and root
page's headers read in place; every `false` exit refutes one conjunct of `metaOverPages`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__validMetaOverPages
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.common.Meta__RootBucket
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section views
variable [GooseExts]

/-- A page's header is the decoding of the first 16 bytes from its offset. -/
theorem pageHdr_view (B : List w8) (f : Nat) :
    pageHdr (bytesAt B (4096 * f) 4096) = (decode ((B.drop (f * 4096)).take 16) : Page) := by
  unfold pageHdr bytesAt
  rw [Nat.mul_comm 4096 f, List.drop_zero, List.take_take, Nat.min_eq_left (by decide)]

/-- A page's meta is the decoding of 64 bytes 16 past its offset. -/
theorem metaOf_view (B : List w8) (i : Nat) :
    metaOf (bytesAt B (4096 * i) 4096) = (decode ((B.drop (i * 4096 + 16)).take 64) : Meta) := by
  unfold metaOf bytesAt
  rw [List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by decide),
    Nat.mul_comm 4096 i]
  first | rfl | (congr 3; omega) | simp [Nat.add_comm]

end views

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
/-- The meta's root-bucket header, read at any fraction. -/
theorem meta_root_view (mp : Loc) (mv : Meta) (dq : DFrac) :
    (mp ↦{dq} mv : IProp GF) ⊢ (structFieldRef Meta go!"root" mp) ↦{dq} mv.root' := by
  iintro Hmv
  iStructNamed Hmv
  iexact root

theorem DB.validMetaOverPages.wp_proof
    (hPIB : DB.pageInBuffer.spec_own (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG))
    (hFreelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (hRootBucket : internal.common.Meta.RootBucket.spec (GF := GF) (hG := hG))
    (hRootPage : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hIsFl : internal.common.Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hIsLeaf : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hIsBranch : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG)) :
    DB.validMetaOverPages.spec (GF := GF) (hG := hG) := by
  intro db sl B dqp i hi hBl
  wp_start as ⟨#Hpkg, Hps, #Hsl⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hlen : sint.Z sl.len = (B.length : Int) := by have := Hsll.1; have := Hsll.2; word
  wp_auto
  wp_if_destruct
  · -- `i` past the buffer's pages
    try wp_auto
    iapply HΦ
    iframe Hps
    ipureintro
    intro _ h
    have h1 := h.1
    word
  have hiB : i < B.length / 4096 := by word
  have hB0 : B ≠ [] := by intro h; rw [h] at hiB; simp at hiB
  ihave %Hp := ownSlice_ptr_pos _ _ _ hB0 $$ Hsl
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hp $$ Hsl
    with ⟨#Hbs, -⟩
  rw [flatMap_encode_w8]
  icases persistent_entails_left (internal.common.bytesPointsto_in_bounds _ _ _ hB0) $$ Hbs
    with ⟨-, %Hib⟩
  -- the meta of page `i`
  wp_apply hPIB db sl (W64 (i : Int)) dqp (by word) (by word) Hp $$ [Hps] as Hps
  · iframe Hps; iframe #
  have hi64 : (W64 (i : Int)).toNat = i := by word
  rw [hi64]
  wp_apply hMeta (sl.ptr +ₗ ((i * 4096 : Nat) : Int)) (by simp [Loc.add]; omega)
    (by simp [Loc.add]; omega)
  try wp_auto
  have e16 : sl.ptr +ₗ ((i * 4096 : Nat) : Int) +ₗ 16 = sl.ptr +ₗ ((i * 4096 + 16 : Nat) : Int) := by
    simp [Loc.add]; omega
  rw [e16]
  icases bytesPointsto_view_read (V := Meta) sl.ptr DFrac.discard B (i * 4096 + 16) _ rfl
    (by omega) Hp $$ Hbs with ⟨#HM, -⟩
  rw [← metaOf_view B i]
  generalize hmv : metaOf (bytesAt B (4096 * i) 4096) = mv
  wp_apply hValidate _ _ _ (by simp [Loc.add]; omega) $$ [HM] as %e1 ⟨-, %He1⟩
  · iexact HM
  cases e1 with
  | ok ei =>
    -- not valid
    wp_auto
    iapply HΦ
    iframe Hps
    ipureintro
    intro _ h
    have h2 := h.2.1
    rw [hmv] at h2
    exact nomatch He1.2 h2
  | nil =>
  have hval : metaValid mv := He1.1 rfl
  wp_auto
  wp_apply hFreelist _ _ _ $$ [HM] as -
  · iexact HM
  try wp_auto
  -- the freelist page, if named
  wp_if_destruct
  · -- a freelist page named
    have hfl : metaFlpg mv = some mv.freelist'.toNat := by
      unfold metaFlpg pgidNoFreelist; rw [if_neg]; word
    wp_if_destruct
    · -- past the buffer
      try wp_auto
      iapply HΦ
      iframe Hps
      ipureintro
      intro _ h
      have h3 := (h.2.2.1 _ (by rw [hmv]; exact hfl)).1
      word
    have hfB : mv.freelist'.toNat < B.length / 4096 := by word
    wp_apply hPIB db sl mv.freelist' dqp (by word) (by word) Hp $$ [Hps] as Hps
    · iframe Hps; iframe #
    icases bytesPointsto_view_read (V := Page) sl.ptr DFrac.discard B (mv.freelist'.toNat * 4096) _
      rfl (by omega) Hp $$ Hbs with ⟨#HP, -⟩
    rw [← pageHdr_view B mv.freelist'.toNat]
    generalize hpv : pageHdr (bytesAt B (4096 * mv.freelist'.toNat) 4096) = pv
    wp_auto
    wp_apply hIsFl _ _ _ $$ [HP] as -
    · iexact HP
    by_cases hflag : pv.flags' = W16 16
    · simp only [hflag, decide_true]
      wp_auto
      wp_apply hId _ _ _ $$ [HP] as -
      · iexact HP
      wp_auto
      wp_if_destruct
      · -- another page's id
        try wp_auto
        iapply HΦ
        iframe Hps
        ipureintro
        intro _ h
        have h3 := (h.2.2.1 _ (by rw [hmv]; exact hfl)).2.2
        unfold pageId at h3
        rw [hpv] at h3
        apply Hif
        word
      · try wp_auto
        done
    · simp only [hflag, decide_false]
      wp_auto
      iapply HΦ
      iframe Hps
      ipureintro
      intro _ h
      have h3 := (h.2.2.1 _ (by rw [hmv]; exact hfl)).2.1
      unfold pageFlags freelistPageFlag at h3
      rw [hpv] at h3
      apply hflag
      word
  · done

end proof

end bbolt
end EtcdGrove
end Perennial
