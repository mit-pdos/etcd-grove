/-
`RegisterName(name, rcvr)` (`server.go`): `DefaultServer.RegisterName(name, rcvr)`, so
`Server.RegisterName`'s spec with the package's `DefaultServer` (`defaultServer γ`) for the server.
Proved in `Net/Proof/net/rpc/RegisterName.lean`.
-/
module

public import Net.Spec.net.rpc.Server__RegisterName

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
abbrev RegisterName.spec : Prop :=
  ∀ (γ : GName) (C : CodecSpec GF) (name : GoString) (rcvr : GoInterface)
    (S : MethodSpec GF) (nm : GoString) (np : Bool),
  name ≠ [] →
  {{ defaultServer γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm np) }}
    (App (App (Val (@! net.rpc.RegisterName)) (Val #name)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg γ C name S) ∨ ⌜err ≠ interface.nil⌝ }}

end sec

end net.rpc
end Perennial
