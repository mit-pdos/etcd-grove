/-
Port of `election_proof/proof_unstable__shrinkEntriesArray.v` (857d09190).
-/
import EtcdGrove.Raft.Spec.unstable__shrinkEntriesArray

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

theorem unstable.shrinkEntriesArray.wp_proof :
    unstable.shrinkEntriesArray.spec (GF := GF) (hG := hG) := by
  intro u uv uents
  wp_start as H
  iNamed H
  iunfold ownUnstable at Hun
  iNamed Hun
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  wp_alloc u_ptr as u; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  by_cases He : uents = []
  · -- empty: `nil`
    subst He
    wp_if_destruct
    · wp_load; wp_pures; wp_store; wp_pures; iclear u
      iapply HΦ
      unfold ownUnstable
      simp only [named]
      iframe Hu
      isplitl
      · iapply ownSliceCap_nil
      · iapply ownSlice_nil
    · wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
      exfalso; simp at Hlen; word
  · wp_if_destruct
    · exfalso; apply He; apply List.eq_nil_of_length_eq_zero; word
    wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
    wp_if_destruct
    · wp_load; wp_pures; wp_load; wp_pures
      -- copy into an array of exactly the right size
      wp_apply wp_slice_make2 (V := raftpb.Entry) as %sl ⟨Hsl, Hsl_cap⟩
      · ipureintro; word
      wp_pures; wp_alloc newEntries_ptr as newEntries; wp_pures; wp_store; wp_pures; wp_load
      wp_pures; wp_load; wp_pures; wp_load; wp_pures
      wp_apply +noauto wp_slice_copy $$ [$Hsl $Hents] as %n ⟨%Hn, Hsl, -⟩
      have Hcp : (uents.take (List.replicate (sint.nat uv.entries'.len)
            (zero_val raftpb.Entry)).length ++
          (List.replicate (sint.nat uv.entries'.len) (zero_val raftpb.Entry)).drop uents.length) =
          uents := by
        rw [List.length_replicate, List.take_of_length_le (by rw [Hlen.1]; exact Nat.le_refl _),
          List.drop_of_length_le (by rw [List.length_replicate, Hlen.1]; exact Nat.le_refl _), List.append_nil]
      rw [Hcp]
      ipersist Hsl
      wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures; iclear u newEntries
      iapply HΦ
      unfold ownUnstable
      iframe Hu
      iframe # ∗
    · ispecialize HΦ $$ %uv.entries'
      iapply HΦ
      unfold ownUnstable
      iframe # ∗

end proof

end EtcdGrove
end Perennial
