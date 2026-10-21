/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/nilAwareAdd.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.nilAwareAdd

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

theorem confchange.nilAwareAdd.wp_proof :
    confchange.nilAwareAdd.spec (GF := GF) (hG := hG) := by
  intro mp m id s
  wp_start as ⟨Hmp, Hm⟩
  wp_auto
  unfold ownIdsetQ
  icases Hm with (⟨%Hnil, %Hs⟩ | Hm)
  · subst Hnil Hs
    wp_auto
    wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
    wp_apply wp_mapInsert $$ Hmref as Hmref
    iapply HΦ
    iframe
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_mapInsert $$ Hm as Hm
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
