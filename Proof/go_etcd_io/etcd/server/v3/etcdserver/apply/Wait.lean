/-
The `wait.Wait` contract (`pkg/v3/wait`, names-only), shared by the server's apply thread
(`InvApplier.lean`: `Trigger`) and the apply package (`apply.Apply`: `IsRegistered`). Lean-first
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

/-- `w` is a `wait.Wait` whose `Trigger` returns (it hands the result to a waiting request;
nothing of the protocol) and whose `IsRegistered` returns some boolean (whether a request
waits on the id: `apply.Apply` applies a request without side effects only then). -/
def waitOk (w : GoInterface) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜w = GoInterface.ok wi⌝ ∗
    □ (∀ (id : w64) (x : GoInterface),
      {{ True }} (App (App (Val #(methods wi.ty go!"Trigger" wi.v)) (Val #id)) (Val #x))
      {{ RET #(); True }}) ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods wi.ty go!"IsRegistered" wi.v)) (Val #id))
      {{ (b : Bool), RET #b; True }}))

instance waitOk_persistent (w : GoInterface) : Persistent (waitOk (GF := GF) w) := by
  unfold waitOk; infer_instance

end defs

end EtcdGrove
end Perennial
