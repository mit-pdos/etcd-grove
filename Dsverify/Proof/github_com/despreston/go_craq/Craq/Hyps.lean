/-
The specs of the model pieces the craq port needs that are not proved yet (notes/dsv-craq.md,
"Hypotheses"): each is a `Prop` named after the lab's spec, taken as a premise by the theorems
that use it, never an axiom. Here: H4 (`rpc.DialHTTP`). H1 (net/rpc's and net/http's package
initialization) is the instance variables of the packages' `Base.lean`; H5 (the generated codec)
is `Codec.lean`'s `CodecLaws`; H2, H3 (the servers) and H6 (`log`) are stated where they are used.

Also the local fact `errMsg_errAny` (the lab's `net.rpc.errMsg_errAny`, which `Net/` does not
have): an error with a known message is an error with some message.
-/
module

public import Net.Proof.net.rpc.ClientDefs
public import Net.Proof.models_lab.Errors
public import Dsverify.Proof.net.rpc.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

section hyps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]


attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **H4.** `rpc.DialHTTP("tcp", a)` to an rpc address `a` of world `W`: a client of `a`, or the
dial's error (the lab's `net.rpc.DialHTTP.wp`; Net's `Dial.spec` with the HTTP `CONNECT`
handshake first: plan 5.2, item 6). Note: `rpcAddr W a`'s protocols are net/rpc's frames from the
connection's first byte; over HTTP the handshake's bytes come first, so the shared piece will
need a protocol with the handshake (notes/dsv-craq.md). -/
abbrev DialHTTP.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ net.rpc.rpcAddr (Gg := hG.goose_globalGS) W a }}
    (App (App (Val (@! net.rpc.DialHTTP)) (Val #go!"tcp")) (Val #a))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ net.rpc.isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}

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

end lemmas

end github_com.despreston.go_craq

end Perennial
