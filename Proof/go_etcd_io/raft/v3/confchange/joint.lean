/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/joint.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.joint
public import Spec.go_etcd_io.raft.v3.confchange.outgoing

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

theorem confchange.joint.wp_proof
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG)) :
    confchange.joint.spec (GF := GF) (hG := hG) := by
  intro cfg vin vout s dq Harr
  wp_start as Hs
  wp_auto
  wp_apply wp_confchange_outgoing _ vin vout Harr
  unfold ownIdsetQ
  icases Hs with (⟨%Hnil, %Hs⟩ | Hm)
  · subst Hnil Hs
    wp_auto
    rw [show decide (0 < GMap.size (∅ : GMap w64 Unit)) = false by
      simp [GMap.map_size_empty]]
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · wp_apply wp_map_len_lt $$ Hm as ⟨Hm, %Hlt⟩
    have e : decide (sint.Z (W64 0) < sint.Z (W64 (GMap.size s : Int))) =
        decide (0 < GMap.size s) := by
      apply decide_eq_decide.2
      have : sint.Z (W64 (GMap.size s : Int)) = GMap.size s := by word
      rw [this]; simp
    rw [e]
    iapply HΦ
    iright; iexact Hm

end proof

end EtcdGrove
end Perennial
