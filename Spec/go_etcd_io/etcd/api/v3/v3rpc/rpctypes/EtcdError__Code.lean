/-
`rpctypes.EtcdError.Code()` (`api/v3rpc/rpctypes/error.go`, a value receiver): its code (unit P3a:
the client's `isSafeRetryImmutableRPC` reads it). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `e.Code()` of an `EtcdError` value `e` returns its code. -/
abbrev rpctypes.EtcdError.Code.spec : Prop :=
  ∀ (e : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError),
  {{ (True : IProp GF) }}
    (App (Val #(methods go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty go!"Code" #e))
      (Val #()))
  {{ RET #e.code'; True }}

end spec

end EtcdGrove
end Perennial
