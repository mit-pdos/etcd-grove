/-
`errors.Is`, stated as (a weakening of the postcondition of) Perennial's `errors.wp_Is`, which
proves it: for a `nil` or pointer `target`, and an `err` in an error tree (`errors.errorIsTree`)
whose errors of `target`'s type hold pointers (`errors.TreeTyped`). Lean-first (no Rocq
counterpart).

It was an axiom for any `err` and `target`, which is false: Go's `Is` calls `err`'s `Is` and
`Unwrap` methods (which may panic), and `err == target` panics for a `target` of a comparable
type that holds a non-comparable value (`errors.Is(E{[]int{}}, E{[]int{}})` for
`type E struct{ x any }`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `errors.Is(err, target)`, for a `nil` or pointer `target` and an `err` of an error tree
`S` (with the `Is` methods' meaning `M`), returns some boolean. -/
abbrev errors.Is.spec : Prop :=
  ∀ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop) (err target : GoInterface),
  (∀ tii, target = GoInterface.ok tii → _root_.Perennial.errors.IsPointerError tii) →
  _root_.Perennial.errors.TreeTyped S target →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗ ⌜S err⌝ }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
