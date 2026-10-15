/-
`rpctypes.EtcdError.Error()` (`api/v3rpc/rpctypes/error.go`, a value receiver): its description.
What makes the `EtcdError` `rpctypes.Error` returns an error whose `Error()` returns (unit P3a,
2026-10-14). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- `e.Error()` of an `EtcdError` value `e` returns its description. -/
abbrev rpctypes.EtcdError.Error.spec : Prop :=
  ∀ (e : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError),
  {{ (True : IProp GF) }}
    (App (Val #(methods go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty go!"Error" #e))
      (Val #()))
  {{ RET #e.desc'; True }}

end spec

end EtcdGrove
end Perennial
