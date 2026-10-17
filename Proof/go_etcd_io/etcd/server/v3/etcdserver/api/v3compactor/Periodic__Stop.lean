/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__Stop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Stop

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

theorem v3compactor.Periodic.Stop.wp_proof :
    v3compactor.Periodic.Stop.spec (GF := GF) (hG := hG) := by
  intro rc P
  wp_start as #Hrc
  iunfold isPeriodic at Hrc
  icases Hrc with ⟨-, -, -, -, -, -, #Hctx, -⟩
  iunfold cancellableCtxAt at Hctx
  icases Hctx with ⟨%ctx, %γ, %cancel, #Fctx, #Fcancel, -, #Hcs⟩
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
