/-
`ctx.Err()`'s error, as `fmt` formats it: the trust boundary (Perennial's `context.isContext`
says nothing of the `Error()` method of the error `Err()` returns). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.fmt.Errorf
public import Perennial.Proof.context

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
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- A non-nil `err`'s `Error()` returns some string (`fmt.stringMethodSpec`): what `fmt.argsOk`
asks of an error argument. -/
def context.errStringOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ → fmt.stringMethodSpec e go!"Error")

instance context.errStringOk_persistent (err : GoInterface) :
    Persistent (context.errStringOk (GF := GF) err) := by
  unfold context.errStringOk; infer_instance

/-- **`ctx.Err()`, with its error's `Error()`**: for a context `c` (`isContext c s`), the triple
of `Err()` in `isContext` (`"#HErr"`, for any `cl`), whose postcondition also gives
`context.errStringOk` of the error returned.

Not the same assumption as `context.ErrDone` (`Spec/context/ErrDone.lean`, the request path's),
and neither follows from the other (2026-10-13, the merge of `origin/lean`): this one is for any
context, done or not, and of the error says only that its `Error()` returns; `ErrDone` is for a
done context only, and says which error it is (the value of `context.Canceled` or of
`context.DeadlineExceeded`), not what its `Error()` does (nothing in Perennial's `context` gives
`DeadlineExceeded`'s `Error()`). The cache's `watchEvents` uses this one; the server's
`processInternalRaftRequestOnce` uses `ErrDone`. -/
abbrev context.Err.spec : Prop :=
  ∀ (c : GoInterfaceOk) (s : _root_.Perennial.context.ContextDesc (IProp GF)) (cl : Broadcast),
  _root_.Perennial.context.isContext c s ⊢ □ ∀ Φ : val → IProp GF,
    (match cl with
     | .Done => _root_.Perennial.context.ContextClosed s.Done_gn
     | _ => iprop(True)) -∗
    ▷ (∀ err : GoInterface,
        (match cl with
         | .Done => iprop(⌜err ≠ interface.nil⌝)
         | _ => if err = interface.nil then iprop(True)
                else iprop(□ s.PDone ∗ _root_.Perennial.context.ContextClosed s.Done_gn)) -∗
        context.errStringOk err -∗ Φ #err) -∗
    WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}

end spec

end EtcdGrove
end Perennial
