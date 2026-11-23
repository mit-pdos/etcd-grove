/-
The kit's generated codec (`examples/craqnet/rpc_gen.go`, by `models/net/rpc/rpcgen.py`) as the
specs see it.

**The `CodecSpec`** (`craqCodec`): each predicate transformer is the weakest precondition of the
generated function it describes (`rpcEncode`, `rpcDecode`, `rpcReceiver`), so the codec meets it by definition
(`craqCodec_encOk`, `craqCodec_decOk`, `craqCodec_rcvOk`), and `rpcReady` (net/rpc initialized, the codec registered)
is what the clients need. The facts a proof needs are the codec lemmas below (the lab's): per wire
type, what encoding a Go value gives (`Wire.lean`'s, rpcgen's bytes), and that decoding a reply
into a fresh zero value is safe and, on success, gives back the value of an encoding.

**Hypothesis H5** (notes/dsv-craq.md): the codec lemmas `enc_*`, `dec_*` are stated here and not
proved (proofs of rpcgen output exist for no kit yet); they are premises of what uses them
(`CodecLaws`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Iface
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Base
public import Net.Proof.net.rpc.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

/-- A pointer to a struct as an interface value. -/
abbrev ptrIface [GooseExts] [GoGlobalContext] (t : go.GoType) (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #p

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]
variable [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [examples.craqnet.Assumptions]


attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def craqCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions examples.craqnet.rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions examples.craqnet.rpcDecode [])) (Val #data)) (Val #ptr)) {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions examples.craqnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }})

theorem craqCodec_encOk : ⊢ net.rpc.encOk (hG := hG) craqCodec (functions examples.craqnet.rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold craqCodec
  iapply Henc
  iexact HΦ

theorem craqCodec_rcvOk : ⊢ net.rpc.rcvOk (hG := hG) craqCodec (functions examples.craqnet.rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold craqCodec
  iapply Hr
  iexact HΦ

theorem craqCodec_decOk : ⊢ net.rpc.decOk (hG := hG) craqCodec (functions examples.craqnet.rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold craqCodec
  iapply Hdec $$ Hd
  iexact HΦ

/-- net/rpc is initialized and the kit's codec registered (persistent). -/
def rpcReady : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ net.rpc.codecSet craqCodec)

instance rpcReady_persistent : Persistent (rpcReady (hG := hG)) := by
  unfold rpcReady; infer_instance

/-! ## Encoding the arguments -/

abbrev enc_string.spec : Prop :=
  ∀ (s : GoString) (Ψ : List w8 → IProp GF),
    Ψ (encString s) ⊢ craqCodec.enc (interface.mkOk go.string #s) Ψ

abbrev enc_EmptyArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.EmptyArgs.mk ∗
      (p ↦{dq} transport.netrpc.EmptyArgs.mk -∗ Ψ encEmptyArgs) ⊢
    craqCodec.enc (ptrIface transport.netrpc.EmptyArgs.ty p) Ψ

abbrev enc_NodeMeta.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : MetaV) (Ψ : List w8 → IProp GF),
    metaPtr p dq m ∗ (metaPtr p dq m -∗ Ψ (encMeta m)) ⊢
    craqCodec.enc (ptrIface transport.NodeMeta.ty p) Ψ

abbrev enc_CommitArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (v : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.CommitArgs.mk k v ∗
      (p ↦{dq} transport.netrpc.CommitArgs.mk k v -∗ Ψ (encCommitArgs k v)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.CommitArgs.ty p) Ψ

abbrev enc_WriteArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (sl : GoSlice) (dqs : DFrac)
    (x : GoString) (v : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.WriteArgs.mk k sl v ∗ sl ↦*{dqs} x ∗
      (p ↦{dq} transport.netrpc.WriteArgs.mk k sl v -∗ sl ↦*{dqs} x -∗
        Ψ (encWriteArgs k x v)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.WriteArgs.ty p) Ψ

abbrev enc_ClientWriteArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (sl : GoSlice) (dqs : DFrac)
    (x : GoString) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.ClientWriteArgs.mk k sl ∗ sl ↦*{dqs} x ∗
      (p ↦{dq} transport.netrpc.ClientWriteArgs.mk k sl -∗ sl ↦*{dqs} x -∗
        Ψ (encClientWriteArgs k x)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.ClientWriteArgs.ty p) Ψ

abbrev enc_PropagateRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (req : GMap GoString w64)
    (Ψ : List w8 → IProp GF),
    reqPtr p dq req ∗ (reqPtr p dq req -∗ ∀ bs, ⌜encPropReq req bs⌝ -∗ Ψ bs) ⊢
    craqCodec.enc (ptrIface transport.PropagateRequest.ty p) Ψ

/-! ## Decoding the replies -/

abbrev dec_EmptyReply.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    p ↦ transport.netrpc.EmptyReply.mk ∗ (∀ ok, p ↦ transport.netrpc.EmptyReply.mk -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.netrpc.EmptyReply.ty p) Ψ

abbrev dec_VersionResponse.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    p ↦ transport.netrpc.VersionResponse.mk go!"" (W64 0) ∗
      (∀ ok, (if ok then ∃ (k : GoString) (v : w64), p ↦ transport.netrpc.VersionResponse.mk k v ∗
          ⌜∀ k' v', rep = encVersionResp k' v' → k = k' ∧ v = v'⌝
        else p ↦ transport.netrpc.VersionResponse.mk go!"" (W64 0)) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.netrpc.VersionResponse.ty p) Ψ

abbrev dec_Item.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    p ↦ transport.Item.mk go!"" slice.nil ∗
      (∀ ok, (if ok then ∃ (k : GoString) (sl : GoSlice) (x : GoString),
          p ↦ transport.Item.mk k sl ∗ sl ↦* x ∗ ⌜∀ k' x', rep = encItem k' x' → k = k' ∧ x = x'⌝
        else p ↦ transport.Item.mk go!"" slice.nil) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.Item.ty p) Ψ

abbrev dec_NodeMeta.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    metaPtr p (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩ ∗
      (∀ ok, (∃ m : MetaV, metaPtr p (DFrac.own 1) m) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.NodeMeta.ty p) Ψ

abbrev dec_PropagateResponse.spec : Prop :=
  ∀ (p mp : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    p ↦ mp ∗ ownMap mp (DFrac.own 1) (∅ : GMap GoString GoSlice) ∗
      (∀ ok, (if ok then ∃ resp, respPtr p resp ∗ ⌜∀ r, encPropResp r rep → resp = r⌝
        else p ↦ mp ∗ ownMap mp (DFrac.own 1) (∅ : GMap GoString GoSlice)) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.PropagateResponse.ty p) Ψ

/-- The codec lemmas (hypothesis H5). -/
structure CodecLaws : Prop where
  enc_string : enc_string.spec (GF := GF)
  enc_EmptyArgs : enc_EmptyArgs.spec (GF := GF)
  enc_NodeMeta : enc_NodeMeta.spec (GF := GF)
  enc_CommitArgs : enc_CommitArgs.spec (GF := GF)
  enc_WriteArgs : enc_WriteArgs.spec (GF := GF)
  enc_ClientWriteArgs : enc_ClientWriteArgs.spec (GF := GF)
  enc_PropagateRequest : enc_PropagateRequest.spec (GF := GF)
  dec_EmptyReply : dec_EmptyReply.spec (GF := GF)
  dec_VersionResponse : dec_VersionResponse.spec (GF := GF)
  dec_Item : dec_Item.spec (GF := GF)
  dec_NodeMeta : dec_NodeMeta.spec (GF := GF)
  dec_PropagateResponse : dec_PropagateResponse.spec (GF := GF)

end codec

end github_com.despreston.go_craq

end Perennial
