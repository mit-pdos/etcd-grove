/-
The kit's generated codec, **server side** (H5, the bindings): what the net/rpc server's
`Method`s need of `rpcDecode` (the request arguments, decoded into the fresh value `NewArg()`
allocates) and of `rpcEncode` (the replies, encoded from the value `Call` filled in).

Decoding: Net's `methodOk` (`argDec`, `Net/Proof/net/rpc/ServerDefs.lean`) owes decoding only of
argument bytes some client deposited for the method, and the method specs (`nodeSpec`,
`coordSpec`, `Methods.lean`) say those bytes are an encoding of a value of the argument type
(`⌜args = enc…⌝`): so each lemma here assumes that, and on success gives back exactly the encoded
value. Its failure branch (never taken, but `dec`'s shape asks for it) gives some field values.

Encoding: the reply types' `enc_*`, in the shape of `Codec.lean`'s argument encoders.

Proved in `CodecSrvProof.lean` (`craqSrvCodecLaws`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]
variable [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [examples.craqnet.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Decoding the arguments -/

abbrev decA_EmptyArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (Ψ : Bool → IProp GF),
    ⌜args = encEmptyArgs⌝ ∗ p ↦ transport.netrpc.EmptyArgs.mk ∗
      (∀ ok, p ↦ transport.netrpc.EmptyArgs.mk -∗ Ψ ok) ⊢
    craqCodec.dec args (ptrIface transport.netrpc.EmptyArgs.ty p) Ψ

abbrev decA_string.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (s : GoString) (Ψ : Bool → IProp GF),
    ⌜args = encString s⌝ ∗ p ↦ (go!"" : GoString) ∗
      (∀ ok, (if ok then p ↦ s else ∃ s' : GoString, p ↦ s') -∗ Ψ ok) ⊢
    craqCodec.dec args (ptrIface go.string p) Ψ

abbrev decA_NodeMeta.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (m : MetaV) (Ψ : Bool → IProp GF),
    ⌜args = encMeta m⌝ ∗ metaPtr p (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩ ∗
      (∀ ok, (if ok then metaPtr p (DFrac.own 1) m else ∃ m' : MetaV, metaPtr p (DFrac.own 1) m') -∗
        Ψ ok) ⊢
    craqCodec.dec args (ptrIface transport.NodeMeta.ty p) Ψ

abbrev decA_CommitArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (k : GoString) (v : w64) (Ψ : Bool → IProp GF),
    ⌜args = encCommitArgs k v⌝ ∗ p ↦ transport.netrpc.CommitArgs.mk go!"" (W64 0) ∗
      (∀ ok, (if ok then p ↦ transport.netrpc.CommitArgs.mk k v
        else ∃ (k' : GoString) (v' : w64), p ↦ transport.netrpc.CommitArgs.mk k' v') -∗ Ψ ok) ⊢
    craqCodec.dec args (ptrIface transport.netrpc.CommitArgs.ty p) Ψ

abbrev decA_WriteArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (k x : GoString) (v : w64) (Ψ : Bool → IProp GF),
    ⌜args = encWriteArgs k x v⌝ ∗ p ↦ transport.netrpc.WriteArgs.mk go!"" slice.nil (W64 0) ∗
      (∀ ok, (if ok then ∃ sl : GoSlice, p ↦ transport.netrpc.WriteArgs.mk k sl v ∗ sl ↦* x
        else ∃ (k' : GoString) (sl : GoSlice) (v' : w64),
          p ↦ transport.netrpc.WriteArgs.mk k' sl v') -∗ Ψ ok) ⊢
    craqCodec.dec args (ptrIface transport.netrpc.WriteArgs.ty p) Ψ

abbrev decA_ClientWriteArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (k x : GoString) (Ψ : Bool → IProp GF),
    ⌜args = encClientWriteArgs k x⌝ ∗ p ↦ transport.netrpc.ClientWriteArgs.mk go!"" slice.nil ∗
      (∀ ok, (if ok then ∃ sl : GoSlice, p ↦ transport.netrpc.ClientWriteArgs.mk k sl ∗ sl ↦* x
        else ∃ (k' : GoString) (sl : GoSlice),
          p ↦ transport.netrpc.ClientWriteArgs.mk k' sl) -∗ Ψ ok) ⊢
    craqCodec.dec args (ptrIface transport.netrpc.ClientWriteArgs.ty p) Ψ

/-- `NewArg()`'s `new(transport.PropagateRequest)` holds the nil map. -/
abbrev decA_PropagateRequest.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (req : GMap GoString w64) (Ψ : Bool → IProp GF),
    ⌜encPropReq req args⌝ ∗ p ↦ (null : Loc) ∗
      (∀ ok, (if ok then reqPtr p (DFrac.own 1) req else ∃ mp : Loc, p ↦ mp) -∗ Ψ ok) ⊢
    craqCodec.dec args (ptrIface transport.PropagateRequest.ty p) Ψ

/-! ## Encoding the replies -/

abbrev enc_EmptyReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.EmptyReply.mk ∗
      (p ↦{dq} transport.netrpc.EmptyReply.mk -∗ Ψ encEmptyReply) ⊢
    craqCodec.enc (ptrIface transport.netrpc.EmptyReply.ty p) Ψ

abbrev enc_VersionResponse.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (v : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.VersionResponse.mk k v ∗
      (p ↦{dq} transport.netrpc.VersionResponse.mk k v -∗ Ψ (encVersionResp k v)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.VersionResponse.ty p) Ψ

abbrev enc_Item.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (sl : GoSlice) (dqs : DFrac) (x : GoString)
    (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.Item.mk k sl ∗ sl ↦*{dqs} x ∗
      (p ↦{dq} transport.Item.mk k sl -∗ sl ↦*{dqs} x -∗ Ψ (encItem k x)) ⊢
    craqCodec.enc (ptrIface transport.Item.ty p) Ψ

abbrev enc_PropagateResponse.spec : Prop :=
  ∀ (p : Loc) (resp : GMap GoString (List (GoString × w64))) (Ψ : List w8 → IProp GF),
    respPtr p resp ∗ (respPtr p resp -∗ ∀ bs, ⌜encPropResp resp bs⌝ -∗ Ψ bs) ⊢
    craqCodec.enc (ptrIface transport.PropagateResponse.ty p) Ψ

/-- The server side's codec lemmas (H5, the bindings). -/
structure SrvCodecLaws : Prop where
  decA_EmptyArgs : decA_EmptyArgs.spec (GF := GF)
  decA_string : decA_string.spec (GF := GF)
  decA_NodeMeta : decA_NodeMeta.spec (GF := GF)
  decA_CommitArgs : decA_CommitArgs.spec (GF := GF)
  decA_WriteArgs : decA_WriteArgs.spec (GF := GF)
  decA_ClientWriteArgs : decA_ClientWriteArgs.spec (GF := GF)
  decA_PropagateRequest : decA_PropagateRequest.spec (GF := GF)
  enc_EmptyReply : enc_EmptyReply.spec (GF := GF)
  enc_VersionResponse : enc_VersionResponse.spec (GF := GF)
  enc_Item : enc_Item.spec (GF := GF)
  enc_NodeMeta : enc_NodeMeta.spec (GF := GF)
  enc_PropagateResponse : enc_PropagateResponse.spec (GF := GF)

end codec

end github_com.despreston.go_craq

end Perennial
