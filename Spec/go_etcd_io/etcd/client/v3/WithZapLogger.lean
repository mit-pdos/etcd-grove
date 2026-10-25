/-
`WithZapLogger(lg)` (`client/v3/client.go`; PR etcd#22658): a `NewCtxClient` option that stores `lg`
into `c.lg`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithZapLogger(lg)` returns an `Option` closure satisfying `ctxClientOptOk`. -/
abbrev WithZapLogger.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithZapLogger)) (Val #lg))
  {{ (opt : GoFunc), RET #opt; ctxClientOptOk opt }}

end spec

end EtcdGrove
end Perennial
