/-
`(*clientv3.LeaseOp).applyOpts(opts)` (`client/v3/op.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.LeaseOp__applyOpts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem LeaseOp.applyOpts.wp_proof :
    LeaseOp.applyOpts.spec (GF := GF) (hG := hG) := by
  intro p op sl gs
  wp_start as ⟨Hop, #Hopts⟩
  unfold leaseOptsAt
  icases Hopts with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  wp_auto
  ihave IH : iprop(∃ (n : w64) (op' : go_etcd_io.etcd.client.v3.LeaseOp) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ p ↦ op' ∗ "opt" ∷ opt_ptr ↦ f0 ∗
      "%Hop'" ∷ ⌜op' =
        { op with attachedKeys' := (leaseKeysFold (gs.take (sint.nat n)) op.attachedKeys') }⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hop opt]
  · iexists W64 0, op, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨?_, by word, by word⟩
    rw [show sint.nat (W64 0) = 0 by rfl]
    simp [leaseKeysFold]
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
    unfold leaseOptSpec
    wp_apply Hg $$ [$Hop] as Hop
    wp_for_post
    iframe
    iexists n + W64 1, _, f
    simp only [named]
    iframe
    ipureintro
    refine ⟨?_, by word, by word⟩
    subst Hop'
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    unfold leaseKeysFold
    rw [foldl_apply_take_succ gs op.attachedKeys' _ g Hgi]
  · have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
    iapply HΦ
    subst Hop'
    rw [Hge, List.take_length]
    iframe

end proof

end EtcdGrove
end Perennial
