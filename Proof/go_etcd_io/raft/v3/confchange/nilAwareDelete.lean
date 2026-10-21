/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/nilAwareDelete.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.nilAwareDelete

@[expose] public section

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

theorem confchange.nilAwareDelete.wp_proof :
    confchange.nilAwareDelete.spec (GF := GF) (hG := hG) := by
  intro mp m id s
  wp_start as ⟨Hmp, Hm⟩
  wp_auto
  unfold ownIdsetQ
  icases Hm with (⟨%Hnil, %Hs⟩ | Hm)
  · subst Hnil Hs
    wp_auto
    iapply HΦ
    iframe
    unfold ownIdsetC
    ileft; ipureintro; exact ⟨rfl, GMap.delete_empty _⟩
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_mapDelete $$ Hm as Hm
    wp_apply wp_map_len_lt $$ Hm as ⟨Hm, %Hlt⟩
    wp_if_destruct
    · iapply HΦ
      iframe
      unfold ownIdsetC
      ileft; ipureintro
      refine ⟨rfl, GMap.map_size_empty_inv _ ?_⟩
      have := congrArg sint.Z Hif
      word
    · iapply HΦ
      iframe
      unfold ownIdsetC
      iright; iframe
      ipureintro
      intro he
      rw [he, GMap.map_size_empty] at Hif
      exact Hif rfl

end proof

end EtcdGrove
end Perennial
