/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/entriesOf.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entryOf
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]


variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem entriesOf.wp_proof (wp_entryOf : entryOf.spec (GF := GF) (hG := hG)) :
    entriesOf.spec (GF := GF) (hG := hG) := by
  intro sl dq els es nn hnorm
  wp_start as ⟨Hsl, #Hents⟩
  ihave %Hl := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hents
  wp_auto
  wp_apply wp_slice_make3 (V := AntCheck.G.Entry) (W64 0) sl.len ⟨by decide, Hl.2⟩
    as %o0 ⟨Ho, Hcap, -⟩
  try wp_auto
  imod (receipt_zero (GF := GF)) with Hr0
  ihave IH : iprop(∃ (k : w64) (o : GoSlice) (gs : List AntCheck.G.Entry) (pe : Loc),
      "i" ∷ i_ptr ↦ k ∗ "out" ∷ out_ptr ↦ o ∗ "e" ∷ e_ptr ↦ pe ∗ "Ho" ∷ o ↦* gs ∗
      "Hcap" ∷ ownSliceCap AntCheck.G.Entry o (DFrac.own 1) ∗
      "Hg" ∷ ([∗list] g;x ∈ gs;(es.take (sint.nat k)).map entOfE, AntCheck.entryRO g x) ∗
      "Hr" ∷ ⧗ (sint.nat k) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len⌝) $$ [i out e Ho Hcap Hr0]
  · iexists W64 0, o0, [], _
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
    isplitr
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
    ipureintro; exact ⟨by decide, Hl.2⟩
  iapply wp_fupd
  wp_for IH
  wp_if_destruct
  · ihave %Hl := ownSlice_len $$ Hsl
    ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hents
    obtain ⟨l, Hlk⟩ : ∃ l, els[sint.nat k]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hl.1]; word)⟩
    obtain ⟨x, Hxk⟩ : ∃ x, es[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hl2, Hl.1]; word)⟩
    ihave #Hx := BigSepL2.bigSepL2_lookup Hlk Hxk $$ Hents
    rw [if_pos ⟨Hk.1, Hif⟩]
    wp_bind (App (Val (GoInstruction (GoLoad _))) (Val _))
    iapply (wp_load_slice_index sl (sint.Z k) els dq l Hk.1) $$ [Hsl]
    · iframe Hsl; ipureintro; exact Hlk
    inext
    iintro Hsl
    wp_take_receipt as Hr1
    wp_apply wp_entryOf l DFrac.discard x nn (hnorm x (List.mem_of_getElem? Hxk)) $$ [$Hpkg $Hx]
      as %g ⟨-, Hg1⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append o gs _ [g] (DFrac.own 1) $$ [$Ho $Hcap $Hsl1] as %o' ⟨Ho, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    iexists (k + W64 1), o', gs ++ [g], l
    rw [hk1]
    iframe
    isplitl [Hg Hg1]
    · rw [List.take_add_one, Hxk, Option.toList_some, List.map_append, List.map_singleton]
      iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
      iframe
    isplitl [Hr Hr1]
    · iapply (receipt_add _ _).2
      iframe
    ipureintro; exact ⟨by word, by word⟩
  · have hk : sint.nat k = es.length := by rw [← Hl2, Hl.1]; word
    rw [hk, List.take_length]
    imod ownSlice_persist $$ Ho with #Ho
    try wp_auto
    imodintro
    iapply HΦ
    iframe Hsl Hr
    iunfold AntCheck.logRO
    iexists gs
    iframe Ho Hg

end proof

end AntHarness
end EtcdGrove
end Perennial
