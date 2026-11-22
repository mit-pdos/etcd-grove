-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/CloneLeaf.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The leaf helpers of `raftpb/noax.go`'s clones (`cloneUint64`, `cloneBool`, `cloneBytes`,
`cloneUint64s`, `cloneUnknown`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`, "Stage 3a"). Shared by the proofs of `CloneEntry`, `CloneConfState` and
`CloneSnapshot`; outside the spec/proof discipline (unexported helpers of the package).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.CloneEntry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## Cells -/

theorem optCell_null {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (o : Option V) :
    optCell (GF := GF) p o ⊢ ⌜p = null ↔ o = none⌝ := by
  cases o with
  | none => simp only [optCell]; iintro %H; ipureintro; simp [H]
  | some v =>
    simp only [optCell]
    iintro #H
    ihave %Hn := typedPointsto_not_null $$ H
    ipureintro; simp [Hn]

theorem nx_cellRO_optCell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    cellRO (GF := GF) p v ⊢ ∃ o : Option V, optCell p o ∗ ⌜v = o.getD (zero_val V)⌝ := by
  iunfold cellRO
  iintro (%H | #H)
  · obtain ⟨rfl, rfl⟩ := H
    iexists none
    simp only [optCell]
    ipureintro; simp
  · iexists some v
    simp only [optCell]
    iframe H
    ipureintro; rfl

theorem nx_optCell_cellRO {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (o : Option V) :
    optCell (GF := GF) p o ⊢ cellRO p (o.getD (zero_val V)) := by
  iunfold cellRO
  cases o with
  | none => simp only [optCell]; iintro %H; ileft; ipureintro; exact ⟨H, rfl⟩
  | some v => simp only [optCell, Option.getD_some]; iintro #H; iright; iexact H

/-- `cloneUint64(p)`: a fresh frozen cell holding what `p`'s holds, `nil` for `nil`. -/
theorem wp_cloneUint64 (p : Loc) (o : Option w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ optCell p o }}
      (App (Val #(functions raftpb.cloneUint64 [])) (Val #p))
    {{ (p' : Loc), RET #p'; optCell p' o }} := by
  wp_start as #Hc
  cases o with
  | none =>
    simp only [optCell]
    icases Hc with %Hp
    subst Hp
    wp_auto
    iapply HΦ
    ipureintro; trivial
  | some v =>
    simp only [optCell]
    ihave %Hn := typedPointsto_not_null $$ Hc
    iapply wp_fupd
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hn
    ipersist «$r0»
    imodintro
    iapply HΦ
    iexact «$r0»

/-- `cloneBool(p)`: as `cloneUint64`. -/
theorem wp_cloneBool (p : Loc) (o : Option Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ optCell p o }}
      (App (Val #(functions raftpb.cloneBool [])) (Val #p))
    {{ (p' : Loc), RET #p'; optCell p' o }} := by
  wp_start as #Hc
  cases o with
  | none =>
    simp only [optCell]
    icases Hc with %Hp
    subst Hp
    wp_auto
    iapply HΦ
    ipureintro; trivial
  | some v =>
    simp only [optCell]
    ihave %Hn := typedPointsto_not_null $$ Hc
    iapply wp_fupd
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hn
    ipersist «$r0»
    imodintro
    iapply HΦ
    iexact «$r0»

/-! ## Slices -/

/-- `cloneUint64s(s)` (`append([]uint64(nil), s...)`): a fresh slice holding `s`'s elements. -/
theorem wp_cloneUint64s (s : GoSlice) (dq : DFrac) (vs : List w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ s ↦*{dq} vs }}
      (App (Val #(functions raftpb.cloneUint64s [])) (Val #s))
    {{ (s' : GoSlice), RET #s'; s ↦*{dq} vs ∗ s' ↦* vs }} := by
  wp_start as Hs
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap (GF := GF) w64 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  wp_apply wp_slice_append (V := w64) slice.nil [] s vs dq $$ [Hnil Hcap Hs] as %s' ⟨Hs', -, Hs⟩
  · iframe Hnil Hcap Hs
  iapply HΦ
  iframe Hs
  simp only [List.nil_append]
  iexact Hs'

/-- `cloneUnknown(u)` (`append([]byte(nil), u...)`): a fresh slice holding the read-only bytes. -/
theorem wp_cloneUnknown (u : GoSlice) (uf : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ u ↦*□ uf }}
      (App (Val #(functions raftpb.cloneUnknown [])) (Val #u))
    {{ (u' : GoSlice), RET #u'; u' ↦* uf }} := by
  wp_start as #Hu
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap (GF := GF) w8 slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  wp_apply wp_slice_append (V := w8) slice.nil [] u uf DFrac.discard $$ [Hnil Hcap] as %u' ⟨Hu', -, -⟩
  · iframe Hnil Hcap Hu
  iapply HΦ
  simp only [List.nil_append]
  iexact Hu'

/-- `append` onto an empty non-`nil` slice (a `[]byte{}` literal's): a non-`nil` slice. -/
theorem wp_append_nonnil (p : Loc) (hp : p ≠ null) (sl2 : GoSlice) (vs : List w8) (dq : DFrac) :
    {{ (sl2 ↦*{dq} vs : IProp GF) }}
      (App (App (Val #(functions go.append [go.GoType.SliceType go.byte]))
        (Val #(slice.mk p (W64 0) (W64 0)))) (Val #sl2))
    {{ (s' : GoSlice), RET #s'; s' ↦* vs ∗ sl2 ↦*{dq} vs ∗ ⌜s' ≠ slice.nil⌝ }} := by
  iintro %Φ Hs2 HΦ
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  ihave He : (slice.mk p (W64 0) (W64 0) ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_empty _ _ (by rfl) (by simp)
    iapply array_empty _ _ hp
  by_cases hvs : vs = []
  · subst hvs
    have hl : sint.Z sl2.len = 0 := by
      obtain ⟨h1, h2⟩ := Hlen2
      simp only [List.length_nil] at h1
      word
    iapply wp_slice_append_fits (V := w8) (slice.mk p (W64 0) (W64 0)) sl2 _ ⟨by simp, by omega⟩
      (by simp; omega)
    have h0 : sl2.len = W64 0 := by word
    have hs : slice.slice (slice.mk p (W64 0) (W64 0)) w8 (slice.mk p (W64 0) (W64 0)).len
        ((slice.mk p (W64 0) (W64 0)).len + sl2.len) = slice.mk p (W64 0) (W64 0) := by
      simp only [slice.slice, sliceIndexRef, h0]
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
      congr 1
    rw [hs]
    wp_apply wp_slice_copy (V := w8) _ ([] : List w8) sl2 [] dq $$ [He Hs2] as %n ⟨-, He, Hs2⟩
    · iframe He Hs2
    isplitr
    · ipureintro; exact isPanic_intoVal _
    imodintro
    iapply HΦ
    iframe Hs2
    simp only [List.take_nil, List.drop_nil, List.append_nil]
    iframe He
    ipureintro
    intro h
    exact hp (congrArg GoSlice.ptr h)
  · ihave Hcap : ownSliceCap (GF := GF) w8 (slice.mk p (W64 0) (W64 0)) (DFrac.own 1) $$ []
    · iapply ownSliceCap_empty _ rfl (by simp)
    iapply wp_slice_append (V := w8) _ [] sl2 vs dq $$ [He Hcap Hs2]
    · iframe He Hcap Hs2
    iintro %s'
    inext
    iintro ⟨Hs', -, Hs2⟩
    simp only [List.nil_append]
    ihave %Hl' := ownSlice_len _ _ _ $$ Hs'
    iapply HΦ
    iframe Hs' Hs2
    ipureintro
    intro h
    subst h
    apply hvs
    apply List.eq_nil_of_length_eq_zero
    have : sint.nat (slice.nil : GoSlice).len = 0 := rfl
    omega

/-- `cloneBytes(b)`: `nil` for `nil`, else a fresh non-`nil` slice holding `b`'s bytes. -/
theorem wp_cloneBytes (b : GoSlice) (dq : DFrac) (vs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ b ↦*{dq} vs }}
      (App (Val #(functions raftpb.cloneBytes [])) (Val #b))
    {{ (b' : GoSlice), RET #b'; b ↦*{dq} vs ∗ b' ↦* vs ∗ ⌜b = slice.nil ↔ b' = slice.nil⌝ }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · have hvs : vs = [] := by
      apply List.eq_nil_of_length_eq_zero
      have : sint.nat (slice.nil : GoSlice).len = 0 := rfl
      omega
    subst hvs
    iapply HΦ
    iframe Hb
    isplitl
    · iapply ownSlice_nil
    · ipureintro; simp
  · wp_apply wp_slice_literal_nonnull (l := ([] : List w8))
    isplitr
    · ipureintro; rfl
    iintro %lp %Hlp ⟨-, -⟩
    simp only [show go.arrayLiteralSize ([] : List keyed_element) = 0 from rfl]
    wp_auto
    wp_apply wp_append_nonnil lp Hlp b vs dq $$ [Hb] as %b' ⟨Hb', Hb, %Hb'n⟩
    · iexact Hb
    iapply HΦ
    iframe Hb Hb'
    ipureintro
    exact ⟨fun h => absurd h Hif, fun h => absurd h Hb'n⟩

/-- `cloneBytes` of a frozen `bytes` field: a frozen copy. -/
theorem wp_cloneBytes_C (b : GoSlice) (o : Option (List w8)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ bytesC b o }}
      (App (Val #(functions raftpb.cloneBytes [])) (Val #b))
    {{ (b' : GoSlice), RET #b'; bytesC b' o }} := by
  iintro %Φ ⟨#Hi, #Hb⟩ HΦ
  iapply wp_fupd
  cases o with
  | none =>
    simp only [bytesC]
    icases Hb with %Hb
    subst Hb
    ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    iapply wp_cloneBytes slice.nil (DFrac.own 1) [] $$ [Hnil]
    · iframe Hi Hnil
    iintro %b'
    inext
    iintro ⟨-, -, %Hb'⟩
    imodintro
    iapply HΦ
    try simp only [bytesC]
    ipureintro; exact Hb'.1 rfl
  | some bs =>
    simp only [bytesC]
    icases Hb with ⟨%Hn, #Hb⟩
    iapply wp_cloneBytes b DFrac.discard bs $$ [Hb]
    · iframe Hi Hb
    iintro %b'
    inext
    iintro ⟨-, Hb', %Hb'⟩
    ipersist Hb'
    imodintro
    iapply HΦ
    try simp only [bytesC]
    iframe Hb'
    ipureintro; exact fun h => Hn (Hb'.2 h)

end lemmas

end EtcdGrove
end Perennial
