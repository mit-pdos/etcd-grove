/-
`c.Go(sm, args, reply, done)` (`client.go`) with a buffered `done` channel (`done == nil`, for which
`Go` makes one, is not specified here): a new `*Call` `pc` holding the arguments and `done`,
sent (`Client.send.spec`): its outcome goes to `done` (`callDone`: the caller's promise on it, and
how the outcome fulfils it), `send`'s result comes back (`sendRes`, on the call's ticket `γt`).
An unbuffered channel makes Go's `Go` panic (`log.Panic`), so the capacity is a premise. Proved in
`Net/Proof/net/rpc/Client__Go.lean`.
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
abbrev Client.Go.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames) (sm svc M : GoString)
    (S : MethodSpec GF) (args reply : GoInterface) (done : Loc) (γt : GName) (γf : FutureNames)
    (K : Loc → IProp GF) (Φ : List w8 → GoString → IProp GF) (Rargs D : IProp GF)
    (Θ : List w8 → Bool → IProp GF) (C : CodecSpec GF),
  {{ isClientN c W a γ ∗
      ⌜splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧ reply ≠ interface.nil⌝ ∗
      ⌜done ≠ null ∧ 0 < sint.Z γf.chanName.chanCap⌝ ∗
      codecSet C ∗ C.enc args (fun bs => iprop(S M bs Φ ∗ Rargs)) ∗ D ∗
      □ (D -∗ ∀ rep, Φ rep [] -∗ C.dec rep reply (Θ rep)) ∗
      ghostMapAuth γt 1 (∅ : GMap Unit (Option Nat)) ∗
      callDone γ.conn γt sm args reply done γf K Φ Θ D }}
    (App (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Go"))
      (Val #sm)) (Val #args)) (Val #reply)) (Val #done))
  {{ (pc : Loc), RET #pc; callFields pc sm args reply done ∗ ∃ o, ticket γt o ∗
      sendRes γ.conn o Rargs (C.enc args (fun bs => iprop(S M bs Φ ∗ Rargs))) }}

end spec

end net.rpc
end Perennial
