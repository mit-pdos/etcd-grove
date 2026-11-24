/-
`s.register(rcvr, name, useName)` (`server.go`) on a server `s` (`isServer`), the codec registered
(`codecSet C`) and the receiver one whose `Receiver` the codec describes as `rcvrIs C rcvr S nm np`
(`C.rcv`, `ServerDefs.lean`: its type's name `nm`, nil pointer or not `np`, methods meeting `S`, at
least one): it registers the service under `name` (`useName`) or `nm` (`svcReg`), or returns an
error when the name is taken. The premises exclude the other errors, which log (`log.Print`, which
Perennial does not model: `notes/perennial-changes.md`): `name` not empty (with `useName`), or `nm`
starting with an upper-case ASCII letter and `rcvr` not a nil pointer (without, where Go panics on a
nil pointer); the methods are not empty (`rcvrIs`). Proved in
`Net/Proof/net/rpc/Server__register.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

/-- `register`'s premise on the name it registers (see the file header). -/
def regNameOk (nm : GoString) (np : Bool) (name : GoString) (useName : Bool) : Prop :=
  if useName then name ≠ [] else
    np = false ∧ ∃ c rest, nm = c :: rest ∧ uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.register.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (S : MethodSpec GF)
    (nm : GoString) (np : Bool) (name : GoString) (useName : Bool),
  regNameOk nm np name useName →
  {{ isServer s γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm np) }}
    (App (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"register"))
      (Val #rcvr)) (Val #name)) (Val #useName))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg γ C (if useName then name else nm) S) ∨
        ⌜err ≠ interface.nil⌝ }}

/-- `register` on a server whose registry has an owner (`isServerO s γ (some γf)`), by the owner
(`svcOwn γf R`), of a name free in `R`: it succeeds, the name registered (`svcReg`) and added to
`R`. The name is not taken: every name taken has its owner's element (`svcOwnIn`), so it is in `R`.
The premises are `Server.register.spec`'s. Proved in `Net/Proof/net/rpc/Server__registerFresh.lean`. -/
abbrev Server.register.spec_fresh : Prop :=
  ∀ (s : Loc) (γ γf : GName) (R : GMap GoString Unit) (C : CodecSpec GF) (rcvr : GoInterface)
    (S : MethodSpec GF) (nm : GoString) (np : Bool) (name : GoString) (useName : Bool),
  regNameOk nm np name useName →
  {{ isServerO s γ (some γf) ∗ svcOwn γf R ∗ ⌜(if useName then name else nm) ∉ R⌝ ∗ codecSet C ∗
      C.rcv rcvr (rcvrIs C rcvr S nm np) }}
    (App (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"register"))
      (Val #rcvr)) (Val #name)) (Val #useName))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗
      svcReg γ C (if useName then name else nm) S ∗
      svcOwn γf (R.insert (if useName then name else nm) ()) }}

/-- `register` of a receiver with no method net/rpc can serve (`rcvrNone nm`: name `nm`, not a nil
pointer, no methods), under `register`'s premises on the name (`regNameOk`): it logs ("has no
exported methods of suitable type", `log.Println`) and returns an error, whatever the server's
registry mode (`isServerAny`; the server is not touched). Proved in
`Net/Proof/net/rpc/Server__registerNone.lean`. -/
abbrev Server.register.spec_none : Prop :=
  ∀ (s : Loc) (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface) (nm : GoString)
    (name : GoString) (useName : Bool),
  regNameOk nm false name useName →
  {{ isServerAny s γ ∗ codecSet C ∗ C.rcv rcvr (rcvrNone nm) ∗ isPkgInit (PROP := IProp GF) pkg_id.log }}
    (App (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"register"))
      (Val #rcvr)) (Val #name)) (Val #useName))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ }}

end spec

end net.rpc
end Perennial
