/-
`clientv3.isUnavailableErr` (`client/v3/client.go`).

Users: the watcher (1b).

Proof sketch: `ctx.Err()` (W0's `Err.spec`), `status.FromError`, `status.Code`, `errors.Is`, the
error's `Error()` (2a's specs over `callErr`).

Changes: from `specs-ref`.

Margin: the result is not described (its callers only branch on it).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `isUnavailableErr(...)`: no panic. -/
def isUnavailableErr.spec : Prop :=
  ∀ (ctx err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ (⌜ctx = GoInterface.nil⌝ ∨ Context.ctxOk ctx) ∗ (⌜err = GoInterface.nil⌝ ∨ ∃ k, callErr err k) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.isUnavailableErr)) (Val #ctx)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
