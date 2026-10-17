/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/AutoPeriodic__Stop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.AutoPeriodic__Stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.AutoPeriodic.Stop.wp_proof :
    v3compactor.AutoPeriodic.Stop.spec (GF := GF) (hG := hG) := by
  intro ac P
  wp_start as #Hac
  iunfold isAutoPeriodic at Hac
  icases Hac with ⟨-, -, -, -, -, -, -, ⟨%ctx, %γ, %cancel, #Hctx, #Hcancel, -, #Hcs⟩, -⟩
  wp_auto
  wp_bind (App (Val #cancel) (Val #()))
  iunfold context.cancelSpec at Hcs
  iapply Hcs
  · itrivial
  inext
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
