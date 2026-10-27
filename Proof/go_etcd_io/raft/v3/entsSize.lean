/-
Port of `election_proof/proof_entsSize.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.entsSize
public import Spec.google_golang_org.protobuf.proto.SizeEntry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `for range` accumulating `proto.Size(ent)` into `size`. Since the spec says nothing
about the value, the loop invariant carries no arithmetic at all -- only the mutable locations
and the index bound. raft v3.7: the range variable `ent` is a `*pb.Entry` (allocated outside
the loop, so in the invariant), a log entry by the slice's `entRO`s, weighed by
`proto.SizeEntry.spec` at `□`. -/
theorem entsSize.wp_proof
    (wp_proto_SizeEntry : proto.SizeEntry.spec (GF := GF) (hG := hG)) :
    entsSize.spec (GF := GF) (hG := hG) := by
  intro s es dq
  wp_start as H
  iNamed H
  iunfold entsPts at Hs
  icases Hs with ⟨%ls, Hs, #Hb⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  ihave IH : iprop(∃ (n sz : w64) (ev : Loc),
      "i" ∷ i_ptr ↦ n ∗ "size" ∷ size_ptr ↦ sz ∗ "ent" ∷ ent_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (es.length : Int)⌝) $$ [i size ent]
  · iexists _, _, _
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < es.length := by word
    obtain ⟨e, He⟩ : ∃ e, es[(sint.Z n).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases entsBig_lookup ls es _ e He $$ Hb with ⟨%l, %Hl, #Hl⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index s (sint.Z n) ls dq l Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    wp_apply wp_proto_SizeEntry l DFrac.discard e $$ [$Hl] as %sz2 ⟨-, -⟩
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    word
  · iapply HΦ
    iunfold entsPts
    iexists ls
    iframe Hs Hb

end proof

end EtcdGrove
end Perennial
