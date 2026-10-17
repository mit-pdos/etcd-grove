/-
`errors.Is(err, target)` for any error `err` and a pointer-error target (`client/v3/concurrency`'s
`Mutex.Lock` and `Election.Campaign` test `errors.Is(err, errWaitKeyDeleted)` of whatever
`waitDeletes` returned: a context's error, the client's `Get` or watch error, or the package's own
`errLostWatcher`/`errWaitKeyDeleted`; etcd#22387): the trust boundary. Lean-first (no Rocq
counterpart). Perennial's `errors.wp_Is` needs the error tree of `err` with its `Is`/`Unwrap`
methods' specs, which the client's contract does not give (its errors are any errors).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)`, for a pointer-error `target` (`errors.New`'s) and any `err`, returns
some boolean. Nothing is said of which: the callers' specs do not depend on it. -/
abbrev errors.IsAnyErr.spec : Prop :=
  ∀ (err : GoInterface) (tii : GoInterfaceOk),
  _root_.Perennial.errors.IsPointerError tii →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok tii)))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
