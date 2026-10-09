/-
Proof of `Spec/Op__applyOpts.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__applyOpts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Op.applyOpts.wp_proof : Op.applyOpts.spec (GF := GF) (hG := hG) := by
  intro opp op o sl gs
  wp_start as ⟨Hop, #Hat, #Hopts⟩
  unfold optsAt
  icases Hopts with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  wp_auto
  ihave IH : iprop(∃ (n : w64) (op' : go_etcd_io.etcd.client.v3.Op) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ opp ↦ op' ∗ "opt" ∷ opt_ptr ↦ f0 ∗
      "#Hat" ∷ opFullAt op' (opFold (gs.take (sint.nat n)) o) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hop opt]
  · iexists W64 0, op, _
    simp only [named]
    iframe
    isplitl []
    · simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, opFold, List.foldl_nil]
      iexact Hat
    ipureintro; constructor <;> word
  iclear Hat
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, gs[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold optSpec
    wp_apply Hg $$ [$Hop $Hat] as %op'' ⟨Hop, #Hat'⟩
    wp_for_post
    iframe
    iexists n + W64 1, op'', f
    simp only [named]
    iframe
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, opFold_take_succ gs o _ g Hgi]
      iexact Hat'
    ipureintro; constructor <;> word
  · have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
    iapply HΦ
    iframe
    rw [show opFold gs o = opFold (gs.take (sint.nat n)) o by rw [Hge, List.take_length]]
    iexact Hat

end proof

end EtcdGrove
end Perennial
