/-
Port of `election_proof/proof_unstable__nextEntries.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.Spec.unstable__nextEntries

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

theorem unstable.nextEntries.wp_proof : unstable.nextEntries.spec (GF := GF) (hG := hG) := by
  intro u uv uents Hip
  wp_start as H
  iNamed H
  iunfold ownUnstable at Hun
  iNamed Hun
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  ihave %Hwf := ownSlice_wf $$ Hents
  wp_auto
  have Hk : sint.Z (uv.offsetInProgress' - uv.offset') =
      uint.Z uv.offsetInProgress' - uint.Z uv.offset' := by word
  wp_if_destruct
  · -- everything is in progress: `nil`
    iapply HΦ
    unfold ownUnstable
    iframe # ∗
    rw [List.drop_eq_nil_of_le (by word)]
    iapply ownSlice_nil
  · rw [ite_eq_left ⟨by word, by word, by word⟩]
    wp_auto
    icases (ownSlice_slice (uv.offsetInProgress' - uv.offset') uv.entries'.len uv.entries'
      DFrac.discard uents ⟨by word, by word, by word⟩).1 $$ Hents with ⟨-, #H2, -⟩
    iapply HΦ
    unfold ownUnstable
    iframe # ∗
    have Hsub : subslice (sint.nat (uv.offsetInProgress' - uv.offset')) (sint.nat uv.entries'.len)
        uents = uents.drop (uint.Z uv.offsetInProgress' - uint.Z uv.offset').toNat := by
      rw [subslice_def, List.take_of_length_le (by word)]
      congr 1
      word
    rw [← Hsub]
    iframe # ∗

end proof

end EtcdGrove
end Perennial
