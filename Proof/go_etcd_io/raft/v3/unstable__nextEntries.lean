/-
Port of `election_proof/proof_unstable__nextEntries.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__nextEntries

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

theorem unstable.nextEntries.wp_proof : unstable.nextEntries.spec (GF := GF) (hG := hG) := by
  intro u us Hip
  wp_start as H
  iNamed H
  open_unstable
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  ihave %Hwf := ownSlice_wf $$ Hents
  wp_auto
  have Hk : sint.Z (us.inprogress - us.offset) =
      uint.Z us.inprogress - uint.Z us.offset := by word
  wp_if_destruct
  · -- everything is in progress: `nil`
    iapply HΦ
    isplitl
    · close_unstable
    rw [List.drop_eq_nil_of_le (by word)]
    iapply ownSlice_nil
  · rw [ite_eq_left ⟨by word, by word, by word⟩]
    wp_auto
    icases (ownSlice_slice (us.inprogress - us.offset) uv.entries'.len uv.entries'
      DFrac.discard us.ents ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #H2, -⟩
    iapply HΦ
    isplitl [Hu Hents_cap]
    · close_unstable
    have Hsub : subslice (sint.nat (us.inprogress - us.offset)) (sint.nat uv.entries'.len)
        us.ents = us.ents.drop (uint.Z us.inprogress - uint.Z us.offset).toNat := by
      rw [subslice_def, List.take_of_length_le (by word)]
      congr 1
      word
    rw [← Hsub]
    iframe # ∗

end proof

end EtcdGrove
end Perennial
