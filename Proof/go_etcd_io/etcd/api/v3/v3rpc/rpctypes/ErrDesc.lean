/-
**An `EtcdError`'s description** (D29, 2026-10-21): the trust boundary. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.cache.v3

section axioms
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- **An `EtcdError`'s description is its `desc`** (an axiom; D29): `errDesc` is what
`rpctypes.ErrorDesc` returns; an `EtcdError` has no `GRPCStatus` method
(`RpctypesEtcdErrorMethods.noGRPCStatus`), so `status.FromError` says it is not a status error and
`ErrorDesc` returns its `Error()`, which is `e.desc` (`EtcdError.Error`, `error.go`). A fact of the
description's definition, which `errDesc`, opaque, cannot state by itself. -/
axiom rpctypes.errDesc_etcdError (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
  errDesc (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) = x.desc'

end axioms

end EtcdGrove
end Perennial
