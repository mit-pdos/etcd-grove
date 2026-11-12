/-
Lean-first (no Rocq counterpart).

# A context that is never done (stage 7e-2, blocker B2 of `notes/k8s-7e-2-draft.md`)

`ctxNeverDone ctx` (persistent): `ctx`'s `Done()` is the `nil` channel, so a `select` on it with a
`default` runs the default (`processListItem`'s timeout check). True of `context.Background()` (an
`emptyCtx`: Perennial's `wp_background_Done`) and of value contexts over it; `tracing.Start` keeps it
(its trusted spec; `examples/k8s7e2attack`'s `TestTracingStartDoneNil*`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def ctxNeverDone (ctx : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜ctx = GoInterface.ok ci⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #(chan.nil : GoChan) -∗
      WP (App (Val #(methods ci.ty go!"Done" ci.v)) (Val #())) {{ Φ }})

instance ctxNeverDone_persistent (ctx : GoInterface) : Persistent (ctxNeverDone (GF := GF) ctx) := by
  unfold ctxNeverDone; infer_instance

end defs

end EtcdGrove
end Perennial
