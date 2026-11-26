/-
The server side's codec lemmas (the bindings: `rpc_model_gen.go`'s `NewArg`s decode a deposit's
argument bytes, `Call`'s reply is encoded by `rpcEncode`), stated here and proved in
`NetRpc/CodecSrvProof.lean` (`swiftSrvCodecLaws`, `swiftArgFacts`, `swiftDecLen`). As dsv-craq's
`Craq/CodecSrv.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Decoding the arguments (into `NewArg()`'s fresh zero value) -/

abbrev decA_RegisterArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (addr : GoString) (port : w64) (Ψ : Bool → IProp GF),
    ⌜args = encRegisterArgs addr port⌝ ∗ p ↦ replica.defs.RegisterArgs.mk go!"" (W64 0) ∗
      (∀ ok, (if ok then p ↦ replica.defs.RegisterArgs.mk addr port
        else ∃ v : replica.defs.RegisterArgs, p ↦ v) -∗ Ψ ok) ⊢
    swiftCodec.dec args (ptrIface replica.defs.RegisterArgs.ty p) Ψ

abbrev decA_GetLeaderArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (Ψ : Bool → IProp GF),
    ⌜args = encGetLeaderArgs⌝ ∗ p ↦ replica.defs.GetLeaderArgs.mk ∗
      (∀ ok, p ↦ replica.defs.GetLeaderArgs.mk -∗ Ψ ok) ⊢
    swiftCodec.dec args (ptrIface replica.defs.GetLeaderArgs.ty p) Ψ

abbrev decA_GetReplicaListArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (Ψ : Bool → IProp GF),
    ⌜args = encGetReplicaListArgs⌝ ∗ p ↦ replica.defs.GetReplicaListArgs.mk ∗
      (∀ ok, p ↦ replica.defs.GetReplicaListArgs.mk -∗ Ψ ok) ⊢
    swiftCodec.dec args (ptrIface replica.defs.GetReplicaListArgs.ty p) Ψ

abbrev decA_BtlArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (Ψ : Bool → IProp GF),
    ⌜args = encBtlArgs⌝ ∗ p ↦ replica.defs.BeTheLeaderArgs.mk ∗
      (∀ ok, p ↦ replica.defs.BeTheLeaderArgs.mk -∗ Ψ ok) ⊢
    swiftCodec.dec args (ptrIface replica.defs.BeTheLeaderArgs.ty p) Ψ

abbrev decA_PingArgs.spec : Prop :=
  ∀ (p : Loc) (args : List w8) (a : w8) (Ψ : Bool → IProp GF),
    ⌜args = encPingArgs a⌝ ∗ p ↦ replica.defs.PingArgs.mk (W8 0) ∗
      (∀ ok, (if ok then p ↦ replica.defs.PingArgs.mk a
        else ∃ v : replica.defs.PingArgs, p ↦ v) -∗ Ψ ok) ⊢
    swiftCodec.dec args (ptrIface replica.defs.PingArgs.ty p) Ψ

/-! ## Encoding the replies -/

abbrev enc_RegisterReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (id : w64) (sl : GoSlice) (dqs : DFrac) (nl : List GoString)
    (r il : Bool) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.RegisterReply.mk id sl r il ∗ sl ↦*{dqs} nl ∗
      (p ↦{dq} replica.defs.RegisterReply.mk id sl r il -∗ sl ↦*{dqs} nl -∗
        Ψ (encRegisterReply id nl r il)) ⊢
    swiftCodec.enc (ptrIface replica.defs.RegisterReply.ty p) Ψ

abbrev enc_GetLeaderReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (id : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.GetLeaderReply.mk id ∗
      (p ↦{dq} replica.defs.GetLeaderReply.mk id -∗ Ψ (encGetLeaderReply id)) ⊢
    swiftCodec.enc (ptrIface replica.defs.GetLeaderReply.ty p) Ψ

abbrev enc_GetReplicaListReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (sr sa : GoSlice) (dqr dqa : DFrac) (rl : List GoString)
    (al : List Bool) (r : Bool) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.GetReplicaListReply.mk sr sa r ∗ sr ↦*{dqr} rl ∗ sa ↦*{dqa} al ∗
      (p ↦{dq} replica.defs.GetReplicaListReply.mk sr sa r -∗ sr ↦*{dqr} rl -∗ sa ↦*{dqa} al -∗
        Ψ (encGetReplicaListReply rl al r)) ⊢
    swiftCodec.enc (ptrIface replica.defs.GetReplicaListReply.ty p) Ψ

abbrev enc_BtlReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (l nl : w32) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.BeTheLeaderReply.mk l nl ∗
      (p ↦{dq} replica.defs.BeTheLeaderReply.mk l nl -∗ Ψ (encBtlReply l nl)) ⊢
    swiftCodec.enc (ptrIface replica.defs.BeTheLeaderReply.ty p) Ψ

abbrev enc_PingReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} replica.defs.PingReply.mk ∗
      (p ↦{dq} replica.defs.PingReply.mk -∗ Ψ encPingReply) ⊢
    swiftCodec.enc (ptrIface replica.defs.PingReply.ty p) Ψ

/-- The server side's codec lemmas (the bindings). -/
structure SrvCodecLaws : Prop where
  decA_RegisterArgs : decA_RegisterArgs.spec (GF := GF)
  decA_GetLeaderArgs : decA_GetLeaderArgs.spec (GF := GF)
  decA_GetReplicaListArgs : decA_GetReplicaListArgs.spec (GF := GF)
  decA_BtlArgs : decA_BtlArgs.spec (GF := GF)
  decA_PingArgs : decA_PingArgs.spec (GF := GF)
  enc_RegisterReply : enc_RegisterReply.spec (GF := GF)
  enc_GetLeaderReply : enc_GetLeaderReply.spec (GF := GF)
  enc_GetReplicaListReply : enc_GetReplicaListReply.spec (GF := GF)
  enc_BtlReply : enc_BtlReply.spec (GF := GF)
  enc_PingReply : enc_PingReply.spec (GF := GF)

/-- A decoding gives the bytes' bound (`rpcDecode` reads a slice: its length is below `2^63`). -/
abbrev decLen.spec : Prop :=
  ∀ (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF),
    (⌜bs.length < 2 ^ 63⌝ -∗ swiftCodec.dec bs ptr Ψ) ⊢
      swiftCodec.dec bs ptr (fun ok => iprop(⌜bs.length < 2 ^ 63⌝ ∗ Ψ ok))

end codec

/-- The argument encodings are injective (under the bound a decoding gives). -/
structure ArgFacts : Prop where
  encRegisterArgs_inj : ∀ (a a' : GoString) (p p' : w64),
    (encRegisterArgs a p).length < 2 ^ 63 →
    encRegisterArgs a p = encRegisterArgs a' p' → a = a' ∧ p = p'
  encPingArgs_inj : ∀ (x x' : w8), encPingArgs x = encPingArgs x' → x = x'

end github_com.imdea_software.swiftpaxos

end Perennial
