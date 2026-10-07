/-
Port of `election_proof/proof_entsSize.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.entsSize
import EtcdGrove.Raft.ElectionProof.Spec.Entry__Size

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `for range` accumulating `Entry.Size()` into `size`. Since the spec says nothing
about the value, the loop invariant carries no arithmetic at all -- only the three
mutable locations and the index bound that the `IndexRef` needs. `ent` is allocated
*outside* the loop and written on every iteration, so it is existentially quantified
inside the invariant (the `cur` lesson from `raft.campaign`'s proof).

`Entry.Size` has a pointer receiver and the range variable `ent` is that pointer, so
`raftpb.Entry.Size.spec` applies to `ent_ptr` directly. -/
theorem entsSize.wp_proof
    (wp_Entry_Size : raftpb.Entry.Size.spec (GF := GF) (hG := hG)) :
    entsSize.spec (GF := GF) (hG := hG) := by
  intro s es dq
  wp_start as Hs
  iNamed Hs
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave IH : iprop(∃ (n sz : w64) (ev : raftpb.Entry),
      "i" ∷ i_ptr ↦ n ∗ "size" ∷ size_ptr ↦ sz ∗ "ent" ∷ ent_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (es.length : Int)⌝) $$ [i size ent]
  · iexists W64 0, zero_val w64, zero_val raftpb.Entry
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · list_elem es (sint.nat n) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index s (sint.Z n) es dq e Hn.1 $$ [Hs] with Hs
    · iframe
      ipureintro
      exact He_lookup
    wp_apply wp_Entry_Size $$ [$ent] as %sz2 ent
    wp_for_post
    iframe
    iexists n + W64 1, sz + sz2, e
    iframe
    ipureintro
    word
  · iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
