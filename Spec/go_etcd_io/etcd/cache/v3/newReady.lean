/-
`newReady()`. Lean-first (no Rocq counterpart); see `InvReady.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvReady

@[expose] public section

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

/-- `newReady()`: a `ready` in epoch `0` (not ready). -/
abbrev newReady.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (@! newReady)) (Val #()))
  {{ (r : Loc) (γ : ReadyNames), RET #r; isReady r γ ∗ readyEpochLb γ 0 }}

end spec

end EtcdGrove
end Perennial
