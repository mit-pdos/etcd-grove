/-
`call.done()` (`client.go`): a non-blocking send of `call` on its `Done` channel (`select` with a
`default`). With the call's promise (`callDone`: `Fulfill` of the future idiom on that channel)
and its outcome (`Error` and `callPost`), it fulfils the promise when the channel has room; when
it has none, Go drops the reply (the `default` case, which logs only under `debugLog`, `false`),
and so does the spec: the promise is lost, and its receiver waits for good. Proved in
`Net/Proof/net/rpc/Call__done.lean`.
-/
module

public import Net.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Call.done.spec : Prop :=
  ∀ (pc : Loc) (sm : GoString) (args reply : GoInterface) (ch : Loc) (γ : RpcConnNames)
    (γt : GName) (γf : FutureNames) (K : Loc → IProp GF) (Φ : List w8 → GoString → IProp GF)
    (Θ : List w8 → Bool → IProp GF) (D : IProp GF) (o : Option Nat) (err : GoInterface),
  {{ globalAddr net.rpc.debugLog ↦□ false ∗ callFields pc sm args reply ch ∗ ticket γt o ∗
      callDone γ γt sm args reply ch γf K Φ Θ D ∗
      structFieldRef net.rpc.Call go!"Error" pc ↦ err ∗ callPost γ o Φ Θ D err }}
    (App (Val (pc @!! go.GoType.PointerType net.rpc.Call.ty @!! go!"done")) (Val #()))
  {{ RET #(); True }}

end spec

end net.rpc
end Perennial
