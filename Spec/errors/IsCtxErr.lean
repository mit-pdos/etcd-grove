/-
`errors.Is(err, target)` for a context error target (`context.Canceled`, `context.DeadlineExceeded`):
the trust boundary. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.context
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

/-- `errors.Is(err, target)` with `target` the value of `context.Canceled` or
`context.DeadlineExceeded` and `err` a context's error (`context.isTypedErr`; the server's
`parseProposeCtxErr` takes `cctx.Err()`): returns some boolean, `true` if `err` is the target
itself (Go's `Is` first compares `err == target`, the target's type being comparable; 2026-10-12,
the request path's unit 3a). Perennial's `errors.wp_Is` needs
the error tree of `err` (a context's `Err` is only known to be a typed error) and a pointer target
(`DeadlineExceeded` is a `deadlineExceededError{}` struct, comparable, so Go's `Is` does not
panic comparing it). -/
abbrev errors.IsCtxErr.spec : Prop :=
  ∀ (err target : GoInterface),
  context.isTypedErr err →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      (globalAddr context.Canceled ↦□ target ∨ globalAddr context.DeadlineExceeded ↦□ target) }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; ⌜err = target → b = true⌝ }}

end spec

end EtcdGrove
end Perennial
