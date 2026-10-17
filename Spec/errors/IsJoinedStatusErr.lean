/-
`errors.Is(err, target)` for `err` a tree of `status` errors and joins (`joinedStatusErrOk`,
`Proof/errors/JoinedStatusErr.lean`) and a pointer-error target (etcd#19935's `watcher.Close`
asks `errors.Is(err, context.Canceled)` of the join of its streams' errors): the trust boundary,
as `Spec/errors/IsStatusErr.lean` is for a single `status` error. Perennial's `errors.wp_Is`
proves it but for its premise `TreeTyped S target` (the errors of the tree of the target's type
hold pointers), which is Go's typing, not derivable in the model; it holds of a `*joinError` (a
pointer) and is assumed of a `status` error, as `errors.IsStatusErr` assumes it.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.errors.JoinedStatusErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` with `err` a tree of `status` errors and joins and `target` a
pointer error returns a boolean: `false` if `err` is `nil` and `true` if `err` is `target` (Go's
`Is` first checks `err == nil || target == nil`, then `err == target`; Perennial's `errors.Is`
spec). -/
abbrev errors.IsJoinedStatusErr.spec : Prop :=
  ∀ (err target : GoInterface),
  (∃ tii, target = GoInterface.ok tii ∧ _root_.Perennial.errors.IsPointerError tii) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ joinedStatusErrOk (GF := GF) err }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; ⌜err = GoInterface.nil → b = false⌝ ∗ ⌜err = target → b = true⌝ }}

end spec

end EtcdGrove
end Perennial
