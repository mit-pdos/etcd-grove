/-
`realTimer.Chan()` (`cache/clock.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

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

/-- `r.Chan()`: the timer's channel `C`, on which a receive yields some time (`isChanBag`). -/
abbrev realTimer.Chan.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isRealTimer r }}
    (App (Val (r @!! go.GoType.PointerType realTimer.ty @!! go!"Chan")) (Val #()))
  {{ (ch : Loc) (γ : ChanNames), RET #ch; isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
