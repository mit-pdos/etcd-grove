/-
`ready.Reset()`. Lean-first (no Rocq counterpart); see `InvReady.lean`.
-/
import EtcdGrove.Cache.InvReady

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `r.Reset()`: afterwards the `ready` was not ready in some epoch at least `e0`. -/
abbrev ready.Reset.spec : Prop :=
  ∀ (r : Loc) (γ : ReadyNames) (e0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isReady r γ ∗ readyEpochLb γ e0 }}
    (App (Val (r @!! go.GoType.PointerType ready.ty @!! go!"Reset")) (Val #()))
  {{ RET #(); readySeen γ e0 false }}

end spec

end EtcdGrove
end Perennial
