/-
The specs of the model pieces the craq port needs that are not proved yet (notes/dsv-craq.md,
"Hypotheses"): each is a `Prop` named after the lab's spec, taken as a premise by the theorems
that use it, never an axiom. Here only lemmas: H4 (rpc over HTTP) is `HttpRpc.lean`'s `RpcHttpAddr`, `RpcHttpDial`. H1 (net/rpc's and net/http's package
initialization) is the instance variables of the packages' `Base.lean`; H5 (the generated codec)
is `Codec.lean`'s `CodecLaws`; H2, H3 (the servers) and H6 (`log`) are stated where they are used.

Also the local fact `errMsg_errAny` (the lab's `net.rpc.errMsg_errAny`, which `Net/` does not
have): an error with a known message is an error with some message.
-/
module

public import Net.Proof.net.rpc.Base
public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.net.rpc.ClientGhost
public import Net.Proof.net.rpc.ClientRead
public import Net.Proof.net.rpc.Codec
public import Net.Proof.net.rpc.Errs
public import Net.Proof.net.rpc.Proto
public import Net.Proof.net.rpc.ProtoGhost
public import Net.Proof.net.rpc.ServerDefs
public import Net.Proof.net.rpc.ServerGhost
public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Close
public import Net.Proof.models_lab.Errors
public import Dsverify.Proof.net.rpc.Init

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

/-- Net's net/rpc client specs the kit's rpc clients call (`Client.Call`, `Client.Close`), proved
in `Net/Proof/net/rpc/Results.lean`: an instance argument of the proofs that call them, which see
their callees through specs only (CLAUDE.md, "Import tiers"); `examples/craqnet/Link.lean` makes
the instance from Net's proofs (not a hypothesis). -/
class RpcClientSpecs [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.rpc.Assumptions]
    [net.FieldAssumptions] [NetProtoGS] : Prop where
  call : net.rpc.Client.Call.spec (GF := GF) (hG := hG)
  close : net.rpc.Client.Close.spec (GF := GF) (hG := hG)

section hyps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]


attribute [local instance] GooseGlobalGS.gooseInvGS

end hyps

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem errMsg_errAny (err : GoInterface) (msg : GoString) :
    net.rpc.errMsg (hG := hG) err msg ⊢ models_lab.errAny err := by
  unfold net.rpc.errMsg models_lab.errAny
  iintro ⟨%e, %h, %hts, #Hw⟩
  iexists e
  isplitr
  · ipureintro; exact h
  isplitr
  · ipureintro; exact hts
  imodintro
  iintro %Φ HΦ
  iapply Hw
  inext
  iapply HΦ

theorem errorString_isError [errors.Assumptions] :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

/-- An `errors.New` variable's value has its message and is not a `ServerError` (the lab's
`net.rpc.newVar_errMsg'`). -/
theorem newVar_errMsg' [errors.Assumptions] (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ e : GoInterface, globalAddr X ↦□ e ∗ net.rpc.errMsg e msg ∗ ⌜net.rpc.notServerErr e⌝ := by
  unfold errors.newVar
  iintro ⟨%x, #Hx, -, #H⟩
  iexists _
  iframe Hx
  isplitl
  · unfold net.rpc.errMsg
    iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact errorString_isError
    iexact H
  · ipureintro
    intro e he
    cases he
    simp [net.rpc.ServerError.ty]

end lemmas

end github_com.despreston.go_craq

end Perennial
