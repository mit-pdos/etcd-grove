/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__ReqTimeout.lean`. Lean-first (no Rocq
counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem config.ServerConfig.ReqTimeout.wp_proof :
    config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG) := by
  intro c et tm
  wp_start as ⟨#Het, #Htm⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
