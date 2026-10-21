/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__err.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__err

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

theorem confchange.Changer.err.wp_proof :
    confchange.Changer.err.spec (GF := GF) (hG := hG) := by
  intro p chg err dq
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
