/-
`s.RegisterName(name, rcvr)` (`server.go`): `register(rcvr, name, true)`, the service named
`name` (not empty). Proved in `Net/Proof/net/rpc/Server__RegisterName.lean`.
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
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.RegisterName.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (C : CodecSpec GF) (name : GoString) (rcvr : GoInterface)
    (S : MethodSpec GF) (nm : GoString) (np : Bool),
  name ≠ [] →
  {{ isServer s γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm np) }}
    (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"RegisterName"))
      (Val #name)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg γ C name S) ∨ ⌜err ≠ interface.nil⌝ }}

/-- `s.RegisterName(name, rcvr)` by the owner of `s`'s registry (`Server.register.spec_fresh`),
`name` free: registered. Proved in `Net/Proof/net/rpc/Server__RegisterNameFresh.lean`. -/
abbrev Server.RegisterName.spec_fresh : Prop :=
  ∀ (s : Loc) (γ γf : GName) (R : GMap GoString Unit) (C : CodecSpec GF) (name : GoString)
    (rcvr : GoInterface) (S : MethodSpec GF) (nm : GoString) (np : Bool),
  name ≠ [] →
  {{ isServerO s γ (some γf) ∗ svcOwn γf R ∗ ⌜name ∉ R⌝ ∗ codecSet C ∗
      C.rcv rcvr (rcvrIs C rcvr S nm np) }}
    (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"RegisterName"))
      (Val #name)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∗ svcReg γ C name S ∗ svcOwn γf (R.insert name ()) }}

end sec

end net.rpc
end Perennial
