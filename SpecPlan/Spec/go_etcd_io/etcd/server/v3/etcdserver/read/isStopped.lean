/-
## `read.isStopped(err)` (internal helper)

Users: `LinearizableReadLoop` (`read.go:118`). Mirrors the code: `errors.Is` against raft's and the
server's `ErrStopped` (Perennial's `errors.Is` over the error's exact method relations: a read path
error's dynamic type is one of the standard error types, so neither call panics).
Changes: unchanged in content. Margin: the result is not specified (both outcomes are safe for the
loop: return, or close the round with the error).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- Whether `err` is a stop error (unspecified). -/
def isStopped.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      (⌜err = GoInterface.nil⌝ ∨ readErr err) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.isStopped)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec
end Read
end EtcdGrove
end Perennial
