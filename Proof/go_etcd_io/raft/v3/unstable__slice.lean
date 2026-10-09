/- Port of election_proof/proof_unstable__slice.v. -/
module

public import Spec.go_etcd_io.raft.v3.unstable__slice
public import Spec.go_etcd_io.raft.v3.unstable__mustCheckOutOfBounds

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

/-- After the bounds check the whole body is one three-index slice expression. Goose
renders `u.entries[a:b:b]` as `slice.fullSlice entries V a b b`, whose `cap` is
`b - a` -- equal to its `len`, which is the `cap = len` the postcondition promises and
which `raftLog.slice` needs so that `extend` reallocates. The ownership lemmas
(`ownSlice_slice`) only speak about `slice.slice entries V a b`, whose `cap` is
`entries.cap - a`; the two agree on pointer and length, so `ownSlice_same_ptr_len`
(`InvRaftlog.lean`) carries the points-to across. That lemma needs a non-empty list,
which is why the spec demands `lo < hi`. The entries are read-only (`ownUnstable`), so
the sub-slice's points-to is split off a persistent one and nothing has to be given
back. -/
theorem unstable.slice.wp_proof
    (wp_unstable_mustCheckOutOfBounds :
      unstable.mustCheckOutOfBounds.spec (GF := GF) (hG := hG)) :
    unstable.slice.spec (GF := GF) (hG := hG) := by
  intro u uv uents lo hi Hrange Hnw
  obtain ⟨Hr1, Hr2, Hr3⟩ := Hrange
  have Hrange' : uint.Z uv.offset' ≤ uint.Z lo ∧ uint.Z lo ≤ uint.Z hi ∧
      uint.Z hi ≤ uint.Z uv.offset' + (uents.length : Int) := ⟨Hr1, by omega, Hr3⟩
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_unstable_mustCheckOutOfBounds _ _ _ _ _ Hrange' Hnw $$ [$Hun] as Hun
  unfold ownUnstable
  iNamed Hun
  ihave #Hents := Hents
  ihave %Hlen := ownSlice_len $$ Hents
  ihave %Hwf := ownSlice_wf $$ Hents
  wp_auto
  obtain ⟨Hlen1, Hlen2⟩ := Hlen
  obtain ⟨-, Hwf⟩ := Hwf
  have Hlenz : (uents.length : Int) = sint.Z uv.entries'.len := by
    rw [Hlen1]; word
  have Hlo' : sint.Z (lo - uv.offset') = uint.Z lo - uint.Z uv.offset' := by word
  have Hhi' : sint.Z (hi - uv.offset') = uint.Z hi - uint.Z uv.offset' := by word
  simp only [show (0 ≤ sint.Z (lo - uv.offset') ∧
      sint.Z (lo - uv.offset') ≤ sint.Z (hi - uv.offset') ∧
      sint.Z (hi - uv.offset') ≤ sint.Z (hi - uv.offset') ∧
      sint.Z (hi - uv.offset') ≤ sint.Z uv.entries'.cap) = True from eq_true (by omega),
    ↓reduceIte]
  wp_auto
  have Hsublen : (subslice (sint.nat (lo - uv.offset')) (sint.nat (hi - uv.offset')) uents).length
      = sint.nat (hi - uv.offset') - sint.nat (lo - uv.offset') :=
    subslice_length _ _ _ (by word)
  have Hne : subslice (sint.nat (lo - uv.offset')) (sint.nat (hi - uv.offset')) uents ≠ [] := by
    intro Hc; rw [Hc] at Hsublen; simp only [List.length_nil] at Hsublen; word
  have Hcap : sint.Z (slice.fullSlice uv.entries' raftpb.Entry (lo - uv.offset') (hi - uv.offset')
      (hi - uv.offset')).len ≤ sint.Z (slice.fullSlice uv.entries' raftpb.Entry (lo - uv.offset')
      (hi - uv.offset') (hi - uv.offset')).cap := by
    simp only [slice.fullSlice]; omega
  ihave ⟨-, #H2, -⟩ := (ownSlice_slice (lo - uv.offset') (hi - uv.offset') _ _ _
    ⟨by omega, by omega, by omega⟩).1 $$ Hents
  ihave Hs := ownSlice_same_ptr_len
    (slice.slice uv.entries' raftpb.Entry (lo - uv.offset') (hi - uv.offset'))
    (slice.fullSlice uv.entries' raftpb.Entry (lo - uv.offset') (hi - uv.offset') (hi - uv.offset'))
    _ _ Hne rfl rfl Hcap $$ H2
  iapply HΦ
  iframe
  isplitr
  · iexact Hents
  isplitr
  · iexact Hs
  ipureintro
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [Hsublen]; word
  · intro e He
    exact List.mem_of_mem_take (List.mem_of_mem_drop He)
  · rw [← Hlo', ← Hhi']

end proof

end EtcdGrove
end Perennial
