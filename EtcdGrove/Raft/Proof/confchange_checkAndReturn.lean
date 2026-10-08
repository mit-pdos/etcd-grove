/-
Proof of `Spec/confchange_checkAndReturn.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.confchange_checkAndReturn
import EtcdGrove.Raft.Spec.confchange_checkInvariants

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

theorem confchange.checkAndReturn.wp_proof
    (wp_confchange_checkInvariants : confchange.checkInvariants.spec (GF := GF) (hG := hG)) :
    confchange.checkAndReturn.spec (GF := GF) (hG := hG) := by
  intro cfg trk v vm prs dqv dqp Hcfg Hdom
  wp_start as ⟨Hv, Htrk⟩
  wp_alloc trk_ptr as trk; wp_pures; wp_alloc cfg_ptr as cfg; wp_pures; wp_load; wp_pures; wp_load
  wp_pures
  wp_apply wp_confchange_checkInvariants _ _ v vm prs _ _ Hcfg Hdom $$ [$Hv $Htrk]
    as ⟨Hv, Htrk⟩
  wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_load; wp_pures; iclear trk cfg err
  wp_end

end proof

end EtcdGrove
end Perennial
