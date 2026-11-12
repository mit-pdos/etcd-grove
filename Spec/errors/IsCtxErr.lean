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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` with `target` the value of `context.Canceled` or
`context.DeadlineExceeded` and `err` a context's error (`context.isCtxErr`: `Canceled`'s
`*errors.errorString` or `DeadlineExceeded`'s `deadlineExceededError{}`, the errors a done
context's `Err` returns; the server's `parseProposeCtxErr` and `LeaseRenew` take `cctx.Err()`):
returns some boolean, `true` if `err` is the target itself (Go's `Is` first compares
`err == target`, the target's type being comparable; 2026-10-12, the request path's unit 3a).
Neither error type has an `Is` or `Unwrap` method, and both are comparable, so Go's `Is` cannot
panic. Perennial's `errors.wp_Is` needs the error tree of `err` and a pointer target
(`DeadlineExceeded` is a `deadlineExceededError{}` struct, not a pointer). Until premise-fixes-6
(2026-11-11) the premise was `context.isTypedErr err`, which admits an error type whose `Is` or
`Unwrap` panics (`notes/axiom-review/isctxerr.md`; `examples/premisefix/isctxerr`). -/
abbrev errors.IsCtxErr.spec : Prop :=
  ∀ (err target : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ context.isCtxErr err ∗
      (globalAddr context.Canceled ↦□ target ∨ globalAddr context.DeadlineExceeded ↦□ target) }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; ⌜err = target → b = true⌝ }}

end spec

end EtcdGrove
end Perennial
