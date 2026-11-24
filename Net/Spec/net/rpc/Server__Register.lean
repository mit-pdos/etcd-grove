/-
`s.Register(rcvr)` (`server.go`): `register(rcvr, "", false)`, the service named after the
receiver's type (`nm`, which must start with an upper-case ASCII letter; `rcvr` not a nil pointer).
Proved in `Net/Proof/net/rpc/Server__Register.lean`.
-/
module

public import Net.Spec.net.rpc.Server__register

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.Register.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF)
    (nm : GoString) (c : w8) (rest : GoString),
  nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
  {{ isServer s γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm false) }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"Register")) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg γ C nm S) ∨ ⌜err ≠ interface.nil⌝ }}

end sec

end net.rpc
end Perennial
