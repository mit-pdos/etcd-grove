/-
The `wait.Wait` contract (`pkg/v3/wait`, names-only), shared by the server's apply thread
(`InvApplier.lean`) and the apply package (`apply.Apply`: `IsRegistered`). Lean-first
(no Rocq counterpart). In the apply package's directory, light (it imports only `Base`): the
server's `InvApplier.lean` imports it (2026-10-12: moved here from there, with `IsRegistered`
added).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `w` is a `wait.Wait` whose `IsRegistered` returns whether a request waits on the id
(`apply.Apply` applies a request without side effects only then), with the reader's resource
`RD` (2026-10-12, the request path's unit 2: `pkg/wait`'s `IsRegistered` read-locks a shard's
`RWMutex`, which needs a reader slot, `wait.New`'s `RD`; `Trigger`, which the apply package does
not call, went: the server's apply thread triggers through `pkg/wait`'s contract, `isWait`).
What the caller knows of the id's registration, `K ot id`, and what `false` then tells it,
`G ot id`, are the wait's (`pkg/v3/wait`: `waitRegdOpt`/`waitGoneOpt`, `ot = some t` for a
caller that knows the id was registered with the consumer token `t`, `none` for one that knows
nothing; the request path's unit 4d, 2026-10-13). -/
def waitOk (w : GoInterface) (RD : IProp GF) (K G : Option GName → w64 → IProp GF) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜w = GoInterface.ok wi⌝ ∗
    □ (∀ (id : w64) (ot : Option GName),
      {{ RD ∗ K ot id }} (App (Val #(methods wi.ty go!"IsRegistered" wi.v)) (Val #id))
      {{ (b : Bool), RET #b; RD ∗ (⌜b = true⌝ ∨ G ot id) }}))

instance waitOk_persistent (w : GoInterface) (RD : IProp GF) (K G : Option GName → w64 → IProp GF) :
    Persistent (waitOk (GF := GF) w RD K G) := by
  unfold waitOk; infer_instance

end defs

end EtcdGrove
end Perennial
