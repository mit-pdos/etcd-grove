/-
The kit's generated codec (`examples/gryffnet/rpc_gen.go`, `rpc_model_gen.go`, by
`models/net/rpc/rpcgen.py`) as `Net/`'s net/rpc specs see it (dsv-craq's pattern,
`Craq/Codec.lean`, `Craq/CodecSrv.lean`). Supersedes the lab's `Rpc/Codec{Low,Encode,Decode,Proof}.lean`
(the lab's kitgen codec and its `RpcCodec`, which `Net/`'s `CodecSpec` replaces).

**The `CodecSpec`** (`gryffCodec`): each predicate transformer is the weakest precondition of the
generated function it describes (`rpcEncode`, `rpcDecode`, `rpcReceiver`), so the codec meets it
by definition (`gryffCodec_encOk`, `gryffCodec_decOk`, `gryffCodec_rcvOk`). The facts a proof
needs are the codec lemmas below, proved in `CodecProof.lean` (`gryffCodecLaws`):
* the client side (the replicas' `Master.Register`, the master's `Replica.Ping` and
  `Replica.BeTheLeader`): `enc_*` of the argument pointers, `dec_*` of the reply pointers, for the
  bytes the method specs allow (`Rpc/Defs.lean`'s `encRegReply` ...; Net's `Client.Call.spec` asks
  for decoding only of the method's answers, `Φ rep []` in hand). A replica decodes into its
  `reply` variable, which keeps the zero value until a `Ready` answer (a `RegisterReply` that is
  not ready is `encRegReply 0 [] false`, all of whose fields are unsent);
* the server side (Net's `methodOk`: `argDec` of a deposit's argument bytes, `callRet`'s
  encoding of the reply): `decA_*` of the arguments into the fresh value `NewArg()` allocates, and
  `enc_*` of the replies `Call` filled in;
* the receivers (`rcv_Master`, `rcv_Replica`): `rpcReceiver` of a `*masterlib.Master` or a
  `*gryff.Replica` builds the `Receiver` whose methods meet a method spec `S`, given each method's
  `NewArg` obligation (`newArgOk`, dsv-craq's `Netrpc/Bindings.lean`), which the servers' proofs
  give (`Server/*`, `B/*`); `newArg_unused` gives it for a method no deposit names
  (`GetLeader`, `GetReplicaList`).
-/
module

public import Dsverify.Proof.gryff.Rpc.Defs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-- A pointer to a struct as an interface value. -/
abbrev ptrIface [GooseExts] [GoGlobalContext] (t : go.GoType) (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #p

/-- The generated `Method` of the functions named `na`, `nr`, `cl`. -/
abbrev mOf [GooseExts] [GoSemanticsFunctions] [GoGlobalContext] (na nr cl : GoString) :
    net.rpc.Method :=
  net.rpc.Method.mk (functions na []) (functions nr []) (functions cl [])

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def gryffCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions examples.gryffnet.rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions examples.gryffnet.rpcDecode [])) (Val #data)) (Val #ptr))
      {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions examples.gryffnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }})

theorem gryffCodec_encOk :
    ⊢ net.rpc.encOk (hG := hG) gryffCodec (functions examples.gryffnet.rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold gryffCodec
  iapply Henc
  iexact HΦ

theorem gryffCodec_rcvOk :
    ⊢ net.rpc.rcvOk (hG := hG) gryffCodec (functions examples.gryffnet.rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold gryffCodec
  iapply Hr
  iexact HΦ

theorem gryffCodec_decOk :
    ⊢ net.rpc.decOk (hG := hG) gryffCodec (functions examples.gryffnet.rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold gryffCodec
  iapply Hdec $$ Hd
  iexact HΦ

/-! ## The client side: encoding the arguments -/

abbrev enc_RegisterArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (addr : GoString) (port : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} src.masterproto.RegisterArgs.mk addr port ∗
      (p ↦{dq} src.masterproto.RegisterArgs.mk addr port -∗ Ψ (encRegArgs addr port)) ⊢
    gryffCodec.enc (ptrIface src.masterproto.RegisterArgs.ty p) Ψ

abbrev enc_PingArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (a : w8) (Ψ : List w8 → IProp GF),
    p ↦{dq} src.genericsmrproto.PingArgs.mk a ∗
      (p ↦{dq} src.genericsmrproto.PingArgs.mk a -∗ Ψ (encPingArgs a)) ⊢
    gryffCodec.enc (ptrIface src.genericsmrproto.PingArgs.ty p) Ψ

abbrev enc_BTLArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} src.genericsmrproto.BeTheLeaderArgs.mk ∗
      (p ↦{dq} src.genericsmrproto.BeTheLeaderArgs.mk -∗ Ψ encBTLArgs) ⊢
    gryffCodec.enc (ptrIface src.genericsmrproto.BeTheLeaderArgs.ty p) Ψ

/-! ## The client side: decoding the replies -/

/-- A `RegisterReply` answer into the zero `RegisterReply`: its fields (a `NodeList` not sent
stays `nil`). -/
abbrev dec_RegisterReply.spec : Prop :=
  ∀ (p : Loc) (id : w64) (nodes : List GoString) (ready : Bool) (Ψ : Bool → IProp GF),
    p ↦ src.masterproto.RegisterReply.mk (W64 0) slice.nil false ∗
      (∀ nl : GoSlice, p ↦ src.masterproto.RegisterReply.mk id nl ready -∗
        (if nodes = [] then iprop(⌜nl = slice.nil⌝) else iprop(nl ↦* nodes)) -∗ Ψ true) ⊢
    gryffCodec.dec (encRegReply id nodes ready)
      (ptrIface src.masterproto.RegisterReply.ty p) Ψ

abbrev dec_PingReply.spec : Prop :=
  ∀ (p : Loc) (Ψ : Bool → IProp GF),
    p ↦ src.genericsmrproto.PingReply.mk ∗ (p ↦ src.genericsmrproto.PingReply.mk -∗ Ψ true) ⊢
    gryffCodec.dec encPingReply (ptrIface src.genericsmrproto.PingReply.ty p) Ψ

abbrev dec_BTLReply.spec : Prop :=
  ∀ (p : Loc) (Ψ : Bool → IProp GF),
    p ↦ src.genericsmrproto.BeTheLeaderReply.mk ∗
      (p ↦ src.genericsmrproto.BeTheLeaderReply.mk -∗ Ψ true) ⊢
    gryffCodec.dec encBTLReply (ptrIface src.genericsmrproto.BeTheLeaderReply.ty p) Ψ

/-! ## The server side: decoding the arguments into `NewArg()`'s fresh value -/

abbrev decA_RegisterArgs.spec : Prop :=
  ∀ (p : Loc) (addr : GoString) (port : w64) (Ψ : Bool → IProp GF),
    p ↦ src.masterproto.RegisterArgs.mk go!"" (W64 0) ∗
      (p ↦ src.masterproto.RegisterArgs.mk addr port -∗ Ψ true) ⊢
    gryffCodec.dec (encRegArgs addr port) (ptrIface src.masterproto.RegisterArgs.ty p) Ψ

abbrev decA_PingArgs.spec : Prop :=
  ∀ (p : Loc) (a : w8) (Ψ : Bool → IProp GF),
    p ↦ src.genericsmrproto.PingArgs.mk (W8 0) ∗
      (p ↦ src.genericsmrproto.PingArgs.mk a -∗ Ψ true) ⊢
    gryffCodec.dec (encPingArgs a) (ptrIface src.genericsmrproto.PingArgs.ty p) Ψ

abbrev decA_BTLArgs.spec : Prop :=
  ∀ (p : Loc) (Ψ : Bool → IProp GF),
    p ↦ src.genericsmrproto.BeTheLeaderArgs.mk ∗
      (p ↦ src.genericsmrproto.BeTheLeaderArgs.mk -∗ Ψ true) ⊢
    gryffCodec.dec encBTLArgs (ptrIface src.genericsmrproto.BeTheLeaderArgs.ty p) Ψ

/-! ## The server side: encoding the replies -/

abbrev enc_RegisterReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (id : w64) (nl : GoSlice) (dqs : DFrac) (nodes : List GoString)
    (ready : Bool) (Ψ : List w8 → IProp GF),
    p ↦{dq} src.masterproto.RegisterReply.mk id nl ready ∗ nl ↦*{dqs} nodes ∗
      (p ↦{dq} src.masterproto.RegisterReply.mk id nl ready -∗ nl ↦*{dqs} nodes -∗
        Ψ (encRegReply id nodes ready)) ⊢
    gryffCodec.enc (ptrIface src.masterproto.RegisterReply.ty p) Ψ

abbrev enc_PingReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} src.genericsmrproto.PingReply.mk ∗
      (p ↦{dq} src.genericsmrproto.PingReply.mk -∗ Ψ encPingReply) ⊢
    gryffCodec.enc (ptrIface src.genericsmrproto.PingReply.ty p) Ψ

abbrev enc_BTLReply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} src.genericsmrproto.BeTheLeaderReply.mk ∗
      (p ↦{dq} src.genericsmrproto.BeTheLeaderReply.mk -∗ Ψ encBTLReply) ⊢
    gryffCodec.enc (ptrIface src.genericsmrproto.BeTheLeaderReply.ty p) Ψ

/-- The codec lemmas. -/
structure CodecLaws : Prop where
  enc_RegisterArgs : enc_RegisterArgs.spec (GF := GF)
  enc_PingArgs : enc_PingArgs.spec (GF := GF)
  enc_BTLArgs : enc_BTLArgs.spec (GF := GF)
  dec_RegisterReply : dec_RegisterReply.spec (GF := GF)
  dec_PingReply : dec_PingReply.spec (GF := GF)
  dec_BTLReply : dec_BTLReply.spec (GF := GF)
  decA_RegisterArgs : decA_RegisterArgs.spec (GF := GF)
  decA_PingArgs : decA_PingArgs.spec (GF := GF)
  decA_BTLArgs : decA_BTLArgs.spec (GF := GF)
  enc_RegisterReply : enc_RegisterReply.spec (GF := GF)
  enc_PingReply : enc_PingReply.spec (GF := GF)
  enc_BTLReply : enc_BTLReply.spec (GF := GF)

end codec

/-! ## The receivers -/

section methods
variable [GooseExts] [GoSemanticsFunctions] [GoGlobalContext]

/-- The master's methods' generated `Method`s. -/
abbrev mGetLeader : net.rpc.Method := mOf examples.gryffnet.rpcNewArg_r0_GetLeader
  examples.gryffnet.rpcNewReply_r0_GetLeader examples.gryffnet.rpcCall_r0_GetLeader
abbrev mGetReplicaList : net.rpc.Method := mOf examples.gryffnet.rpcNewArg_r0_GetReplicaList
  examples.gryffnet.rpcNewReply_r0_GetReplicaList examples.gryffnet.rpcCall_r0_GetReplicaList
abbrev mRegister : net.rpc.Method := mOf examples.gryffnet.rpcNewArg_r0_Register
  examples.gryffnet.rpcNewReply_r0_Register examples.gryffnet.rpcCall_r0_Register
/-- The replicas' methods' generated `Method`s. -/
abbrev mBeTheLeader : net.rpc.Method := mOf examples.gryffnet.rpcNewArg_r1_BeTheLeader
  examples.gryffnet.rpcNewReply_r1_BeTheLeader examples.gryffnet.rpcCall_r1_BeTheLeader
abbrev mPing : net.rpc.Method := mOf examples.gryffnet.rpcNewArg_r1_Ping
  examples.gryffnet.rpcNewReply_r1_Ping examples.gryffnet.rpcCall_r1_Ping

end methods


section rcv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [net.rpc.Assumptions] [π : NetProtoGS]

/-- What a method's `NewArg` must meet (`methodOk`'s body; dsv-craq's `newArgOk`). -/
def newArgOk (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (v : net.rpc.Method) : IProp GF :=
  iprop(□ ∀ Ψ : val → IProp GF,
      ▷ (∀ (argv : GoInterface) (D : IProp GF) (Θ : List w8 → Bool → IProp GF),
          ⌜argv ≠ interface.nil⌝ -∗ net.rpc.argDec C argv D Sm Θ -∗ D -∗
          (∀ (args : List w8) (Φ : List w8 → GoString → IProp GF), Sm args Φ -∗ Θ args true -∗
            net.rpc.callObl C rcvr v argv Φ) -∗ Ψ #argv) -∗
      WP (App (Val #v.NewArg') (Val #())) {{ Ψ }})

instance newArgOk_persistent (C : net.rpc.CodecSpec GF) (rcvr : GoInterface)
    (Sm : net.rpc.MSpec GF) (v : net.rpc.Method) : Persistent (newArgOk (hG := hG) C rcvr Sm v) := by
  unfold newArgOk; infer_instance

theorem methodOk_of (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (mm : Loc) (v : net.rpc.Method) :
    mm ↦□ v ∗ newArgOk C rcvr Sm v ⊢ net.rpc.methodOk C rcvr Sm mm := by
  unfold net.rpc.methodOk newArgOk
  iintro ⟨#Hm, #Hn⟩
  iexists v
  iframe Hm
  iexact Hn

/-- `rpcReceiver` of a non-nil `*masterlib.Master`: its `Receiver`, named `"Master"`, whose
methods meet `S`, given their `NewArg` obligations. -/
abbrev rcv_Master.spec : Prop :=
  ∀ (mp : Loc) (S : net.rpc.MethodSpec GF), mp ≠ null →
    newArgOk gryffCodec (ptrIface src.masterlib.Master.ty mp) (S go!"GetLeader") mGetLeader ∗
    newArgOk gryffCodec (ptrIface src.masterlib.Master.ty mp) (S go!"GetReplicaList")
      mGetReplicaList ∗
    newArgOk gryffCodec (ptrIface src.masterlib.Master.ty mp) (S go!"Register") mRegister ⊢
    gryffCodec.rcv (ptrIface src.masterlib.Master.ty mp)
      (net.rpc.rcvrIs gryffCodec (ptrIface src.masterlib.Master.ty mp) S go!"Master" false)

/-- `rpcReceiver` of a non-nil `*gryff.Replica`: its `Receiver`, named `"Replica"`. -/
abbrev rcv_Replica.spec : Prop :=
  ∀ (rp : Loc) (S : net.rpc.MethodSpec GF), rp ≠ null →
    newArgOk gryffCodec (ptrIface src.gryff.Replica.ty rp) (S go!"BeTheLeader") mBeTheLeader ∗
    newArgOk gryffCodec (ptrIface src.gryff.Replica.ty rp) (S go!"Ping") mPing ⊢
    gryffCodec.rcv (ptrIface src.gryff.Replica.ty rp)
      (net.rpc.rcvrIs gryffCodec (ptrIface src.gryff.Replica.ty rp) S go!"Replica" false)

/-- The `NewArg` obligation of a method no deposit names (`GetLeader`, `GetReplicaList`). -/
abbrev newArg_GetLeader.spec : Prop :=
  ∀ (rcvr : GoInterface) (Sm : net.rpc.MSpec GF),
    (∀ args Φ, Sm args Φ ⊢ False) →
    net.rpc.codecSet gryffCodec ⊢ newArgOk gryffCodec rcvr Sm mGetLeader

abbrev newArg_GetReplicaList.spec : Prop :=
  ∀ (rcvr : GoInterface) (Sm : net.rpc.MSpec GF),
    (∀ args Φ, Sm args Φ ⊢ False) →
    net.rpc.codecSet gryffCodec ⊢ newArgOk gryffCodec rcvr Sm mGetReplicaList

/-- The receivers' lemmas. -/
structure RcvLaws : Prop where
  rcv_Master : rcv_Master.spec (GF := GF)
  rcv_Replica : rcv_Replica.spec (GF := GF)
  newArg_GetLeader : newArg_GetLeader.spec (GF := GF)
  newArg_GetReplicaList : newArg_GetReplicaList.spec (GF := GF)

end rcv

end Perennial.gryff
