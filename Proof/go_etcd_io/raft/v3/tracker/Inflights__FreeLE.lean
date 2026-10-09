/- Port of election_proof/proof_Inflights__FreeLE.v. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.Inflights__FreeLE

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- The tail after the loop, shared by its two exits (`break` and `i = count`):
`count -= i; bytes -= bytes; start = idx; if count == 0 { start = 0 }`, then
re-establish `InflightsOk` from the loop invariant `Hidx` and the ring invariant
`Hring`. -/
local macro "freele_finish" : tactic => `(tactic| (
  try wp_auto
  -- the new `count` as an integer, once, so that the pure goals below are `omega`'s
  have Hc' : sint.Z (iv.count' - iw) = sint.Z iv.count' - sint.Z iw := by word
  have H0 : sint.Z (W64 0) = 0 := rfl
  wp_if_destruct <;>
  · iapply HΦ
    isplitl [Hiv Hbuf Hbuf_cap]
    · iapply ownInflightsRaw_intro $$ Hiv Hbuf Hbuf_cap
      ipureintro
      unfold InflightsOk
      word
    · ipureintro
      unfold InflightsFreed
      word))

set_option hygiene false in
/-- An exit that leaves the window as it was. -/
local macro "freele_unchanged" : tactic => `(tactic| (
  iapply HΦ
  isplitl [Hiv Hbuf Hbuf_cap]
  · iapply ownInflightsRaw_intro $$ Hiv Hbuf Hbuf_cap
    ipureintro; exact Hok
  · ipureintro; exact ⟨rfl, rfl, Int.le_refl _⟩))

/-- The loop invariant: `0 ≤ i ≤ count` and `idx = (start + i) mod size`, written as its
two cases so that `word`/`omega` can use it. An occupied slot `idx` (i.e. `i < count`)
is inside the buffer by `InflightsOk`'s last conjunct: either the occupied range does
not wrap and ends inside the buffer, or the buffer is the whole ring. -/
private theorem wp_Inflights_FreeLE_internal (l : Loc) (r : InflightsRing) (to : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
        "Hin" ∷ ownInflightsRaw l r }}
      (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"FreeLE")) (Val #to))
    {{ (r' : InflightsRing), RET #();
        ownInflightsRaw l r' ∗ ⌜InflightsFreed r.win r'.win⌝ }} := by
  wp_start as H
  iNamed H
  iunfold ownInflightsRaw at Hin
  iNamed Hin
  subst Hring
  ihave %Hblen := ownSlice_len $$ Hbuf
  have Hok := Hinfl_ok
  simp only [InflightsOk, word_unfold] at Hinfl_ok
  obtain ⟨Hs0, Hc, Hbl, Hsz, Hstart, Hring⟩ := Hinfl_ok
  have Hlenz : (buf.length : Int) = sint.Z iv.buffer'.len := by rw [Hblen.1]; word
  wp_auto
  by_cases Hc0 : iv.count' = W64 0
  · -- exit 1, empty window
    rw [decide_eq_true Hc0]
    wp_auto
    freele_unchanged
  rw [decide_eq_false Hc0]
  -- a non-empty window: `0 < count ≤ size`, so `start < size`, and the occupied slot
  -- `start` is inside the buffer
  have Hcpos : 0 < sint.Z iv.count' := by
    have : sint.Z iv.count' ≠ 0 := fun Hz => Hc0 (by word)
    omega
  have Hslt : sint.Z iv.start' < sint.Z iv.size' := by omega
  have Hsbuf : sint.Z iv.start' < (buf.length : Int) := by omega
  obtain ⟨e0, He0⟩ : ∃ e0, buf[(sint.Z iv.start').toNat]? = some e0 :=
    List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩ |> fun h => ⟨_, h⟩
  wp_auto
  have Hb1 : sint.Z iv.start' < sint.Z iv.buffer'.len := by omega
  simp only [Hs0, Hb1, and_self, ↓reduceIte]
  icases ownSlice_elem_acc (sint.Z iv.start') e0 _ _ _ Hs0 He0 $$ Hbuf with ⟨He, Hback⟩
  wp_auto
  ihave Hbuf := Hback $$ He
  rw [list_insert_id He0]
  wp_if_destruct
  · -- exit 1, `to` is left of the window
    freele_unchanged
  -- the loop: `i` counts freed slots, `idx` is `start + i` mod `size`
  ihave IH : iprop(∃ (idxv iw bv : w64),
      "idx" ∷ idx_ptr ↦ idxv ∗ "i" ∷ i_ptr ↦ iw ∗ "bytes" ∷ bytes_ptr ↦ bv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iw ∧ sint.Z iw ≤ sint.Z iv.count'⌝ ∗
      "%Hidx" ∷ ⌜(sint.Z iv.start' + sint.Z iw < sint.Z iv.size' ∧
                   sint.Z idxv = sint.Z iv.start' + sint.Z iw) ∨
                  (sint.Z iv.size' ≤ sint.Z iv.start' + sint.Z iw ∧
                   sint.Z idxv = sint.Z iv.start' + sint.Z iw - sint.Z iv.size')⌝) $$ [idx i bytes]
  · iexists iv.start', W64 0, W64 0
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, .inl ⟨by word, by word⟩⟩
  irename «in» => Hin_ptr
  wp_for IH
  wp_if_destruct
  · -- `i < count`: slot `idx` is occupied, hence inside the buffer
    have Hidxb : 0 ≤ sint.Z idxv ∧ sint.Z idxv < (buf.length : Int) := by omega
    obtain ⟨e, He⟩ : ∃ e, buf[(sint.Z idxv).toNat]? = some e :=
      ⟨_, List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩⟩
    have Hb2 : sint.Z idxv < sint.Z iv.buffer'.len := by omega
    simp only [Hidxb.1, Hb2, and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z idxv) e _ _ _ Hidxb.1 He $$ Hbuf with ⟨He', Hback⟩
    wp_auto
    ihave Hbuf := Hback $$ He'
    rw [list_insert_id He]
    wp_if_destruct
    · -- `break`: the first inflight past `to`
      wp_for_post
      freele_finish
    · try wp_auto
      simp only [Hidxb.1, Hb2, and_self, ↓reduceIte]
      icases ownSlice_elem_acc (sint.Z idxv) e _ _ _ Hidxb.1 He $$ Hbuf with ⟨He', Hback⟩
      wp_auto
      ihave Hbuf := Hback $$ He'
      rw [list_insert_id He]
      try wp_auto
      wp_if_destruct
      · -- `idx` wraps
        wp_for_post
        iframe
        simp only [named]
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, .inr ⟨by word, by word⟩⟩
      · wp_for_post
        iframe
        simp only [named]
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, ?_⟩
        rcases Hidx with ⟨H1, H2⟩ | ⟨H1, H2⟩
        · exact .inl ⟨by word, by word⟩
        · exact .inr ⟨by word, by word⟩
  · -- `i = count`: every inflight is freed
    freele_finish

/-- The public triple: open `ownInflights`, run the ring-buffer proof above on the
internal `ownInflightsRaw`, close it. `InflightsFreed` is what the internal
postcondition says about the record. -/
theorem tracker.Inflights.FreeLE.wp_proof :
    tracker.Inflights.FreeLE.spec (GF := GF) (hG := hG) := by
  intro l i to
  iintro %Φ ⟨#Hinit, Hin⟩ HΦ
  ihave Hin : iprop(∃ r, ownInflightsRaw l r ∗ ⌜r.win = i⌝) $$ [Hin]
  · unfold ownInflights; simp only [named]; iexact Hin
  icases Hin with ⟨%r, Hin, %Hiabs⟩
  iapply wp_Inflights_FreeLE_internal $$ [$Hinit $Hin]
  inext
  iintro %r' ⟨Hin, %Hfreed⟩
  iapply HΦ
  isplitl
  · iapply ownInflights_intro $$ Hin
  ipureintro
  subst Hiabs
  exact Hfreed

end proof

end EtcdGrove
end Perennial
