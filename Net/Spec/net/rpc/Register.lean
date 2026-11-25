/-
`Register(rcvr)` (`server.go`): `DefaultServer.Register(rcvr)`, so `Server.Register`'s spec with
the package's `DefaultServer` (`defaultServer γ`) for the server. Proved in
`Net/Proof/net/rpc/Register.lean`.
-/
module

public import Net.Spec.net.rpc.Server__Register

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
abbrev Register.spec : Prop :=
  ∀ (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF)
    (nm : GoString) (c : w8) (rest : GoString),
  nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
  {{ defaultServer γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm false) }}
    (App (Val (@! net.rpc.Register)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg γ C nm S) ∨ ⌜err ≠ interface.nil⌝ }}

/-- `Register(rcvr)` by the owner of `DefaultServer`'s registry (`defaultServerO γ γf`,
`svcOwn γf R`), its type's name `nm` free: registered (`Server.Register.spec_fresh`). Proved in
`Net/Proof/net/rpc/RegisterFresh.lean`. -/
abbrev Register.spec_fresh : Prop :=
  ∀ (γ γf : GName) (R : GMap GoString Unit) (C : CodecSpec GF) (rcvr : GoInterface)
    (S : MethodSpec GF) (nm : GoString) (c : w8) (rest : GoString),
  nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
  {{ defaultServerO γ γf ∗ svcOwn γf R ∗ ⌜nm ∉ R⌝ ∗ codecSet C ∗
      C.rcv rcvr (rcvrIs C rcvr S nm false) }}
    (App (Val (@! net.rpc.Register)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∗ svcReg γ C nm S ∗ svcOwn γf (R.insert nm ()) }}

variable [log.Assumptions]

/-- `Register(rcvr)` of a receiver with no method net/rpc can serve (`rcvrNone nm`), its type's name
`nm` exported, on `DefaultServer` in any registry mode (`defaultServerAny γ`): an error
(`Server.Register.spec_none`). Proved in `Net/Proof/net/rpc/RegisterNone.lean`. -/
abbrev Register.spec_none : Prop :=
  ∀ (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (nm : GoString) (c : w8) (rest : GoString),
  nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
  {{ defaultServerAny γ ∗ codecSet C ∗ C.rcv rcvr (rcvrNone nm) ∗
      isPkgInit (PROP := IProp GF) pkg_id.log }}
    (App (Val (@! net.rpc.Register)) (Val #rcvr))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ }}

end sec

end net.rpc
end Perennial
