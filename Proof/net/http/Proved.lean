/-
**The HTTP boundary's statements proved over net/http's translated code** (prove-http,
2026-11-20): what `Proof/net/http/Axioms.lean` assumed until then and the translation now has a
body for (`Code/net/http.toml`); (stdlib2, 2026-11-21) `bytes.NewBuffer` over Perennial's. `Axioms.lean` imports this file, so the boundary's importers see
the same names.
-/
module

public import Proof.net.http.Boundary
public import Perennial.Proof.bytes.Link
public import Proof.net.textproto.Header

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.http.Assumptions]

/-- `http.StatusText(code)` (`status.go:81`, go1.27.3): a `switch` on the code whose every case
returns a string literal, `""` by default. -/
theorem StatusText_ok : StatusText_spec (GF := GF) := by
  intro code
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals (iapply HΦ; itrivial)

/-! ### `Header.Set` and `Get` (prove-http3, 2026-11-21; until then the axioms `HeaderSet_ok`,
`HeaderSetPtr_ok`, `HeaderGetPtr_ok` and `HeaderGetOwnPtr_ok`), over net/textproto's code -/

theorem hdrVals_hdrSet (hs : List (GoString × GoString)) (k v k' : GoString) :
    hdrVals (hdrSet hs k v) k' = if k' = canonKey k then [v] else hdrVals hs k' := by
  unfold hdrVals hdrSet
  rw [List.filter_append, List.map_append]
  by_cases h : k' = canonKey k
  · subst h
    rw [ite_eq_left rfl]
    have : (hs.filter (fun kv => decide (kv.1 ≠ canonKey k))).filter
        (fun kv => decide (kv.1 = canonKey k)) = [] := by
      rw [List.filter_filter, List.filter_eq_nil_iff]; intro x _; simp
    rw [this]; simp
  · rw [ite_eq_right h]
    have : (hs.filter (fun kv => decide (kv.1 ≠ canonKey k))).filter
        (fun kv => decide (kv.1 = k')) = hs.filter (fun kv => decide (kv.1 = k')) := by
      rw [List.filter_filter]; congr 1; funext kv
      by_cases hk : kv.1 = k'
      · subst hk; simp [h]
      · simp [hk]
    rw [this]; simp [Ne.symm h]

/-- The empty string literal is the empty list of bytes. -/
theorem emptyStr_eq : ([] : List GoString).head?.getD (stringToGoString "") = [] := by
  first
  | simp [stringToGoString]
  | (simp only [List.head?_nil, Option.getD_none, stringToGoString]; rfl)
  | (show stringToGoString "" = []; unfold stringToGoString; simp [String.toUTF8])

theorem hdrGet_eq (hs : List (GoString × GoString)) (k : GoString) :
    hdrGet hs k = ((hdrVals hs (canonKey k)).head?).getD "" := by
  unfold hdrGet hdrVals
  rw [List.head?_map, List.head?_filter]

/-- `textproto.MIMEHeader(hm).Get(k)` of a header map at any fraction. -/
theorem wp_MIMEHeaderGet (hm : Loc) (dq : DFrac) (hs : List (GoString × GoString)) (k : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.textproto ∗ hdrMap hm dq hs }}
      (App (Val (hm @!! _root_.Perennial.net.textproto.MIMEHeader.ty @!! go!"Get")) (Val #k))
    {{ RET #(hdrGet hs k); hdrMap hm dq hs }} := by
  wp_start as Hh
  unfold hdrMap
  icases Hh with ⟨%M, Hm, #Hv, %Hn⟩
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  try wp_auto
  rw [decide_eq_false Hnn]
  try wp_auto
  wp_apply EtcdGrove.textproto.wp_CanonicalMIMEHeaderKey
  wp_apply (wp_map_lookup1 go.string (go.GoType.SliceType go.string) hm M (canonKey k) dq) $$ Hm as Hm
  try wp_auto
  rw [hdrGet_eq]
  cases hM : M !! canonKey k with
  | none =>
    rw [Hn _ hM, emptyStr_eq]
    simp only [Option.getD_none]
    rw [decide_eq_true (show (zero_val GoSlice).len = W64 0 from rfl)]
    try wp_auto
    iapply HΦ
    iexists M; iframe Hm Hv; ipureintro; exact Hn
  | some sl =>
    simp only [Option.getD_some]
    ihave Hsl := Hv $$ %(canonKey k) %sl %hM
    ihave %Hl := ownSlice_len _ _ _ $$ Hsl
    wp_if_destruct
    · have h0 : hdrVals hs (canonKey k) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [Hl.1, Hif]; rfl)
      rw [h0, emptyStr_eq]
      try wp_auto
      iapply HΦ
      iexists M; iframe Hm Hv; ipureintro; exact Hn
    · cases hv : hdrVals hs (canonKey k) with
      | nil => exfalso; apply Hif; rw [hv] at Hl; simp at Hl; word
      | cons x xs =>
        try rw [hv] at Hl
        try wp_auto
        rw [ite_eq_left (by simp only [List.length_cons] at Hl; word)]
        wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (x :: xs) DFrac.discard x (by decide) $$ [Hsl]
          as -
        · iframe Hsl; ipureintro; rfl
        try wp_auto
        simp only [List.head?_cons, Option.getD_some]
        iapply HΦ
        iexists M; iframe Hm Hv; ipureintro; exact Hn

/-- `textproto.MIMEHeader(hm).Set(k, v)` of a header map being built. -/
theorem wp_MIMEHeaderSet (hm : Loc) (hs : List (GoString × GoString)) (k v : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.textproto ∗ hdrOwn hm hs }}
      (App (App (Val (hm @!! _root_.Perennial.net.textproto.MIMEHeader.ty @!! go!"Set")) (Val #k))
        (Val #v))
    {{ RET #(); hdrOwn hm (hdrSet hs k v) }} := by
  wp_start as Hh
  unfold hdrOwn hdrMap
  icases Hh with ⟨%M, Hm, #Hv, %Hn⟩
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  try wp_auto
  wp_apply EtcdGrove.textproto.wp_CanonicalMIMEHeaderKey
  wp_apply (wp_mapInsert go.string hm M (canonKey k) _) $$ Hm as Hm
  try wp_auto
  iapply HΦ
  iexists _; iframe Hm
  isplitr
  · iintro !> %k' %sl' %hk'
    rcases (GMap.lookup_insert_Some _ _ _ _ _).1 hk' with ⟨rfl, rfl⟩ | ⟨hne, hk'⟩
    · rw [hdrVals_hdrSet, ite_eq_left rfl]
      iexact Hsl
    · rw [hdrVals_hdrSet, ite_eq_right (Ne.symm hne)]
      iapply Hv; ipureintro; exact hk'
  · ipureintro
    intro k' hk'
    rcases (GMap.lookup_insert_None _ _ _ _).1 hk' with ⟨hk', hne⟩
    rw [hdrVals_hdrSet, ite_eq_right (Ne.symm hne)]
    exact Hn _ hk'

/-- (Until 2026-11-21 an axiom.) -/
theorem HeaderSet_ok : HeaderSet_spec (GF := GF) := by
  intro hm hs k v
  wp_start as Hh
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.net.textproto $$ []
  · iPkgInit
  try wp_auto
  try rw [method_unfold (t := _root_.Perennial.net.http.Header.ty) (m := go!"Set")]
  try wp_auto
  wp_apply wp_MIMEHeaderSet hm hs k v $$ [$Hh] as Hh
  try wp_auto
  iapply HΦ $$ Hh

/-- (Until 2026-11-21 an axiom.) -/
theorem HeaderSetPtr_ok : HeaderSetPtr_spec (GF := GF) := by
  intro p hm hs k v
  wp_start as ⟨#Hp, Hh⟩
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.net.textproto $$ []
  · iPkgInit
  try wp_auto
  try rw [method_unfold (t := _root_.Perennial.net.http.Header.ty) (m := go!"Set")]
  try wp_auto
  wp_apply wp_MIMEHeaderSet hm hs k v $$ [$Hh] as Hh
  try wp_auto
  iapply HΦ $$ Hh

/-- (Statement, used by no proof: proved with the others, 2026-11-21.) -/
theorem HeaderGet_ok : HeaderGet_spec (GF := GF) := by
  intro hm hs k
  wp_start as #Hh
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.net.textproto $$ []
  · iPkgInit
  unfold hdrAt hdrAtRaw
  try wp_auto
  try rw [method_unfold (t := _root_.Perennial.net.http.Header.ty) (m := go!"Get")]
  try wp_auto
  wp_apply wp_MIMEHeaderGet hm DFrac.discard hs k $$ [] as -
  · iexact Hh
  try wp_auto
  iapply HΦ; itrivial

/-- (Until 2026-11-21 an axiom.) -/
theorem HeaderGetPtr_ok : HeaderGetPtr_spec (GF := GF) := by
  intro p hm hs k
  wp_start as ⟨#Hp, #Hh⟩
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.net.textproto $$ []
  · iPkgInit
  unfold hdrAt hdrAtRaw
  try wp_auto
  try rw [method_unfold (t := _root_.Perennial.net.http.Header.ty) (m := go!"Get")]
  try wp_auto
  wp_apply wp_MIMEHeaderGet hm DFrac.discard hs k $$ [] as -
  · iexact Hh
  try wp_auto
  iapply HΦ; itrivial

/-- (Until 2026-11-21 an axiom.) -/
theorem HeaderGetOwnPtr_ok : HeaderGetOwnPtr_spec (GF := GF) := by
  intro p hm hs k
  wp_start as ⟨#Hp, Hh⟩
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.net.textproto $$ []
  · iPkgInit
  unfold hdrOwn
  try wp_auto
  try rw [method_unfold (t := _root_.Perennial.net.http.Header.ty) (m := go!"Get")]
  try wp_auto
  wp_apply wp_MIMEHeaderGet hm (DFrac.own 1) hs k $$ [$Hh] as Hh
  try wp_auto
  iapply HΦ $$ Hh

end proof

section buffer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bytes.Assumptions]

/-- `bytes.NewBuffer(b)` (`NewBuffer_spec`), over its code: `&Buffer{buf: b}`. (stdlib2,
2026-11-21, until then an axiom; Perennial's `bytes.NewBuffer.spec` also takes `b`'s spare
capacity since mit-pdos/perennial#670, which `bufferHas` does not hold.) -/
theorem NewBuffer_ok : NewBuffer_spec (GF := GF) := by
  intro b bs
  iintro %Φ !> Hb HΦ
  wp_func_call
  wp_auto
  iapply HΦ
  unfold readerHas bufferHas
  iright
  iexists _
  isplitr
  · ipureintro; rfl
  iexists _, bs
  iframe
  ipureintro
  refine ⟨by word, by word, ?_⟩
  rw [show sint.nat (0 : w64) = 0 from rfl, List.drop_zero]

/-- `nil` is a reader of no bytes, an empty request body (`readerHas`'s first case; `NewRequest`'s
`nil` body). (stdlib2, 2026-11-21; until then an axiom.) -/
theorem readerHas_nil : ⊢ readerHas (GF := GF) GoInterface.nil [] := by
  unfold readerHas
  ileft
  ipureintro
  exact ⟨rfl, rfl⟩

end buffer

end http
end EtcdGrove
end Perennial
