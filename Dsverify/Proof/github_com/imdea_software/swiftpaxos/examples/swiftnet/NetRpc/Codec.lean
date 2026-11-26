/-
The kit's net/rpc codec as Net's `CodecSpec` (`Net/Proof/net/rpc/Codec.lean`): the generated
functions' (`examples/swiftnet/rpc_gen.go`, `rpc_model_gen.go`) weakest preconditions, and the
codec lemmas the clients need (encoding the arguments, decoding the replies), stated here and
proved in `NetRpc/CodecProof.lean`. As dsv-craq's `Craq/Codec.lean`; the lab's kitgen codec
(`Interface/Rpc.lean`'s `wp_rpcEncode_*`/`wp_rpcDecode_*`, `Proof/codec/*`) is replaced, not
ported.

`rpcDecode(data, ptr)` reads `data`'s type tag and **panics** (`rpcNotModelled`) when the tag
parses but names another type than `ptr`'s: so each decoding lemma assumes `tagOk t rep` (the
tag, if it parses, is the target's). Net's `Client.Call.spec` asks for decoding only of the
method's answers (`Φ rep []` in hand), from which the clients derive `tagOk`. A struct field
the bytes do not send keeps its value (`decMerge`); a failed decoding leaves some value.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.RpcWire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Net.Proof.net.rpc.Codec
public import Net.Proof.net.rpc.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos

/-- A pointer to a struct as an interface value. -/
abbrev ptrIface [GooseExts] [GoGlobalContext] (t : go.GoType) (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #p

/-- A decoded `int32` field: the bytes' value if sent (non-zero), else the old one. -/
def mergeI32 (old new : w32) : w32 := if new = W32 0 then old else new

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def swiftCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions examples.swiftnet.rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions examples.swiftnet.rpcDecode [])) (Val #data)) (Val #ptr)) {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions examples.swiftnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }})

theorem swiftCodec_encOk :
    ⊢ net.rpc.encOk (hG := hG) swiftCodec (functions examples.swiftnet.rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold swiftCodec
  iapply Henc
  iexact HΦ

theorem swiftCodec_rcvOk :
    ⊢ net.rpc.rcvOk (hG := hG) swiftCodec (functions examples.swiftnet.rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold swiftCodec
  iapply Hr
  iexact HΦ

theorem swiftCodec_decOk :
    ⊢ net.rpc.decOk (hG := hG) swiftCodec (functions examples.swiftnet.rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold swiftCodec
  iapply Hdec $$ Hd
  iexact HΦ


/-! ## Encoding the arguments (the clients: the kit's `register`, the master's `run`) -/

abbrev enc_RegisterArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (addr : GoString) (port : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.RegisterArgs.mk addr port ∗
      (p ↦{dq} replica.defs.RegisterArgs.mk addr port -∗ Ψ (encRegisterArgs addr port)) ⊢
    swiftCodec.enc (ptrIface replica.defs.RegisterArgs.ty p) Ψ

abbrev enc_BtlArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.BeTheLeaderArgs.mk ∗
      (p ↦{dq} replica.defs.BeTheLeaderArgs.mk -∗ Ψ encBtlArgs) ⊢
    swiftCodec.enc (ptrIface replica.defs.BeTheLeaderArgs.ty p) Ψ

abbrev enc_PingArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (a : w8) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.PingArgs.mk a ∗
      (p ↦{dq} replica.defs.PingArgs.mk a -∗ Ψ (encPingArgs a)) ⊢
    swiftCodec.enc (ptrIface replica.defs.PingArgs.ty p) Ψ

/-! ## Decoding the replies -/

/-- The pure `rpcGetU64`. -/
def getU64 (bs : List w8) : Option (w64 × List w8) :=
  if 8 ≤ bs.length then some (leToU64 (bs.take 8), bs.drop 8) else none

/-- The pure `rpcGetTag`: a length, then that many bytes. -/
def getTag (bs : List w8) : Option (GoString × List w8) :=
  match getU64 bs with
  | some (n, r) =>
    if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n)) else none
  | none => none

/-- `rep`'s type tag, if it parses, is `t`. -/
def tagOk (t : GoString) (rep : List w8) : Prop :=
  ∀ t' rest, getTag rep = some (t', rest) → t' = t

/-- `Register`'s reply decoded into the zero `RegisterReply` (the kit's `var reply`). -/
abbrev dec_RegisterReply.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk tRegisterReply rep⌝ ∗
    p ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false ∗
      (∀ ok, (if ok then ∃ (id : w64) (sl : GoSlice) (nl : List GoString) (r il : Bool),
          p ↦ replica.defs.RegisterReply.mk id sl r il ∗ sl ↦* nl ∗
          ⌜∀ id' nl' r' il', rep = encRegisterReply id' nl' r' il' →
            id = id' ∧ nl = nl' ∧ r = r' ∧ il = il'⌝
        else ∃ v : replica.defs.RegisterReply, p ↦ v) -∗ Ψ ok) ⊢
    swiftCodec.dec rep (ptrIface replica.defs.RegisterReply.ty p) Ψ

/-- `BeTheLeader`'s reply decoded into any `BeTheLeaderReply` (the master's
`NewBeTheLeaderReply()`): a field the bytes do not send keeps its value. -/
abbrev dec_BtlReply.spec : Prop :=
  ∀ (p : Loc) (l0 nl0 : w32) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk tBeTheLeaderReply rep⌝ ∗
    p ↦ replica.defs.BeTheLeaderReply.mk l0 nl0 ∗
      (∀ ok, (if ok then ∃ (l nl : w32), p ↦ replica.defs.BeTheLeaderReply.mk l nl ∗
          ⌜∀ l' nl', rep = encBtlReply l' nl' → l = mergeI32 l0 l' ∧ nl = mergeI32 nl0 nl'⌝
        else ∃ v : replica.defs.BeTheLeaderReply, p ↦ v ∗ ⌜∀ l' nl', rep ≠ encBtlReply l' nl'⌝) -∗
        Ψ ok) ⊢
    swiftCodec.dec rep (ptrIface replica.defs.BeTheLeaderReply.ty p) Ψ

abbrev dec_PingReply.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk tPingReply rep⌝ ∗
    p ↦ replica.defs.PingReply.mk ∗ (∀ ok, p ↦ replica.defs.PingReply.mk -∗ Ψ ok) ⊢
    swiftCodec.dec rep (ptrIface replica.defs.PingReply.ty p) Ψ

/-- The clients' codec lemmas (proved in `NetRpc/CodecProof.lean`: `swiftCodecLaws`). -/
structure CodecLaws : Prop where
  enc_RegisterArgs : enc_RegisterArgs.spec (GF := GF)
  enc_BtlArgs : enc_BtlArgs.spec (GF := GF)
  enc_PingArgs : enc_PingArgs.spec (GF := GF)
  dec_RegisterReply : dec_RegisterReply.spec (GF := GF)
  dec_BtlReply : dec_BtlReply.spec (GF := GF)
  dec_PingReply : dec_PingReply.spec (GF := GF)

end codec

end github_com.imdea_software.swiftpaxos

end Perennial
