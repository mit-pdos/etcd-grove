/-
transport/netrpc, the server side: the rpc bindings `*NodeBinding`, `*CoordinatorBinding` as
net/rpc receivers of the kit's generated codec (`rpc_model_gen.go`'s `rpcReceiver`): each meets
`rcvrIs craqCodec` for its address's method spec (`nodeSpec`, `coordSpec`), which
`Server.RegisterName` asks for. Per method (`methodOk`): `NewArg()` allocates the argument, whose
decoding of a deposit's argument bytes is `CodecSrv.lean`'s `decA_*` (Net's `argDec`); the call
obligation: `NewReply()`, then `Call` (the binding's method, calling its service: `isNodeSvc`,
`isCoordSvc`), whose reply's encoding is `CodecSrv.lean`'s `enc_*`, or an error answer (the
services' errors have non-empty messages, which the deposit's `errOk` accepts).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.CodecSrv
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace netrpcP

/-- The generated `Method` of the functions named `na`, `nr`, `cl`. -/
abbrev mOf [GooseExts] [GoSemanticsFunctions] [GoGlobalContext] (na nr cl : GoString) : net.rpc.Method :=
  net.rpc.Method.mk (functions na []) (functions nr []) (functions cl [])

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

set_option goose.wp.extras true

/-- What a method's `NewArg` must meet (`methodOk`'s body). -/
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

/-- The binding `b` of the node service `svc` at `a`, and the packages (persistent). -/
def nodeB (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet ∗
    net.rpc.codecSet craqCodec ∗
    b ↦□ transport.netrpc.NodeBinding.mk svc ∗ isNodeSvc cfg svc a)

instance nodeB_persistent (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    Persistent (nodeB (hG := hG) cfg b svc a) := by
  unfold nodeB; infer_instance

/-- The argument encodings are injective (under the bound a decoding gives), and a decoding
gives the bound (`CodecSrvProof.lean`). -/
structure ArgFacts : Prop where
  encString_inj : ∀ s s' : GoString, encString s = encString s' → s = s'
  encMeta_inj : ∀ m m' : MetaV, (encMeta m).length < 2 ^ 63 → encMeta m = encMeta m' → m = m'
  encCommitArgs_inj : ∀ (k k' : GoString) (v v' : w64), (encCommitArgs k v).length < 2 ^ 63 →
    encCommitArgs k v = encCommitArgs k' v' → k = k' ∧ v = v'
  encWriteArgs_inj : ∀ (k k' x x' : GoString) (v v' : w64), (encWriteArgs k x v).length < 2 ^ 63 →
    encWriteArgs k x v = encWriteArgs k' x' v' → k = k' ∧ x = x' ∧ v = v'
  encClientWriteArgs_inj : ∀ (k k' x x' : GoString), (encClientWriteArgs k x).length < 2 ^ 63 →
    encClientWriteArgs k x = encClientWriteArgs k' x' → k = k' ∧ x = x'
  encPropReq_inj : ∀ (req req' : GMap GoString w64) (bs : List w8), bs.length < 2 ^ 63 →
    encPropReq req bs → encPropReq req' bs → req = req'

/-- A decoding gives the bytes' bound. -/
abbrev decLen.spec : Prop :=
  ∀ (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF),
    (⌜bs.length < 2 ^ 63⌝ -∗ craqCodec.dec bs ptr Ψ) ⊢
      craqCodec.dec bs ptr (fun ok => iprop(⌜bs.length < 2 ^ 63⌝ ∗ Ψ ok))

theorem newArg_Ping (L : SrvCodecLaws (GF := GF)) (cfg : Cfg GF) (b : Loc) (svc : GoInterface)
    (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"Ping")
      (mOf examples.craqnet.rpcNewArg_r0_Ping examples.craqnet.rpcNewReply_r0_Ping
        examples.craqnet.rpcCall_r0_Ping) := by
  iintro #Hb
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface transport.netrpc.EmptyArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  unfold nodeB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.netrpc.EmptyArgs.ty p)
      (p ↦ transport.netrpc.EmptyArgs.mk) (nodeSpec cfg.γ cfg.chain a go!"Ping")
      (fun _ _ => p ↦ transport.netrpc.EmptyArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Ping]
    icases HS with ⟨%Hargs, HS⟩
    isplitl [HS]
    · isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_EmptyArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  iStructNamed Hbs
  wp_auto
  unfold isNodeSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨#HPing, -⟩
  wp_apply HPing as %err Herr
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  rw [nodeSpec_Ping]
  icases HS with ⟨-, HS⟩
  unfold errNE
  icases Herr with (%Herr | ⟨%msg, %Hmsg, #Hem⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_EmptyReply
    isplitr [HΦ]
    · iexact «$r0»
    iintro _
    iexact HΦ
  · iright
    iexists msg
    iframe Hem
    rw [if_neg Hmsg]
    icases HS with ⟨-, HΦ⟩
    unfold errOk
    iapply HΦ
    ipureintro; exact Hmsg

theorem newArg_Update (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"Update")
      (mOf examples.craqnet.rpcNewArg_r0_Update examples.craqnet.rpcNewReply_r0_Update
        examples.craqnet.rpcCall_r0_Update) := by
  iintro #Hb
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface transport.NodeMeta.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  unfold nodeB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.NodeMeta.ty p)
      (metaPtr p (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩)
      (nodeSpec cfg.γ cfg.chain a go!"Update")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ m : MetaV, ⌜args = encMeta m⌝ ∗
        metaPtr p (DFrac.own 1) m else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Update]
    icases HS with ⟨%md, %r, %Hargs, HS⟩
    isplitl [HS]
    · iexists md, r
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_NodeMeta _ _ md
    iframe
    isplitr
    · ipureintro; exact Hargs.1
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists md
      iframe
      ipureintro; exact Hargs.1
  ihave Hp : metaPtr p (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩ $$ [Hp]
  · unfold metaPtr; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%m, %Hm, Hp⟩
  rw [nodeSpec_Update]
  icases HS with ⟨%md, %r, ⟨%Hargs, %Hok⟩, Hr, Hdep, HS⟩
  have hmd : m = md := I.encMeta_inj m md (Hm ▸ Hl) (Hm ▸ Hargs)
  subst hmd
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  iStructNamed Hbs
  wp_auto
  unfold isNodeSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, #HUpd, -⟩
  wp_apply HUpd $$ %p %(DFrac.own 1) %m %r %_ %Hok Hp Hr Hdep as %err Hp Herr
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  unfold errNE
  icases Herr with (⟨%Herr, Hpost⟩ | ⟨%msg, %Hmsg, #Hem⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_EmptyReply
    isplitr [HΦ Hpost]
    · iexact «$r0»
    iintro _
    iapply HΦ $$ Hpost
  · iright
    iexists msg
    iframe Hem
    rw [if_neg Hmsg]
    icases HS with ⟨-, HΦ⟩
    unfold errOk
    iapply HΦ
    ipureintro; exact Hmsg

theorem newArg_Write (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"Write")
      (mOf examples.craqnet.rpcNewArg_r0_Write examples.craqnet.rpcNewReply_r0_Write
        examples.craqnet.rpcCall_r0_Write) := by
  iintro #Hb
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  unfold nodeB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface transport.netrpc.WriteArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.netrpc.WriteArgs.ty p)
      (p ↦ transport.netrpc.WriteArgs.mk go!"" slice.nil (W64 0))
      (nodeSpec cfg.γ cfg.chain a go!"Write")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ (k x : GoString) (v : w64)
        (sl : GoSlice), ⌜args = encWriteArgs k x v⌝ ∗ p ↦ transport.netrpc.WriteArgs.mk k sl v ∗
        sl ↦* x else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Write]
    icases HS with ⟨%k, %x, %v, %Hargs, HS⟩
    isplitl [HS]
    · iexists k, x, v
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_WriteArgs _ _ k x v
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      icases Hp with ⟨%sl, Hp, Hsl⟩
      iexists k, x, v, sl
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ transport.netrpc.WriteArgs.mk go!"" slice.nil (W64 0) $$ [Hp]
  · rw [show transport.netrpc.WriteArgs.mk go!"" slice.nil (W64 0) = zero_val transport.netrpc.WriteArgs from rfl]; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%k, %x, %v, %sl, %Hm, Hp, Hsl⟩
  rw [nodeSpec_Write]
  icases HS with ⟨%k', %x', %v', %Hargs, Hve, HS⟩
  obtain ⟨rfl, rfl, rfl⟩ := I.encWriteArgs_inj k k' x x' v v' (Hm ▸ Hl) (Hm ▸ Hargs)
  unfold net.rpc.callObl
  imod ownSlice_persist $$ Hsl with #Hsl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  iStructNamed Hbs
  wp_auto
  unfold isNodeSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, -, #HW, -⟩
  iStructNamed Hp
  (try wp_auto)
  wp_apply HW $$ %k %sl %x %v %_ Hsl Hve as %err Herr
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  unfold errNE
  icases Herr with (⟨%Herr, Hpost⟩ | ⟨%msg, %Hmsg, #Hem⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_EmptyReply
    isplitr [HΦ Hpost]
    · iexact «$r0»
    iintro _
    iapply HΦ $$ Hpost
  · iright
    iexists msg
    iframe Hem
    rw [if_neg Hmsg]
    icases HS with ⟨-, HΦ⟩
    unfold errOk
    iapply HΦ
    ipureintro; exact Hmsg

theorem newArg_Commit (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"Commit")
      (mOf examples.craqnet.rpcNewArg_r0_Commit examples.craqnet.rpcNewReply_r0_Commit
        examples.craqnet.rpcCall_r0_Commit) := by
  iintro #Hb
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  unfold nodeB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface transport.netrpc.CommitArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.netrpc.CommitArgs.ty p)
      (p ↦ transport.netrpc.CommitArgs.mk go!"" (W64 0))
      (nodeSpec cfg.γ cfg.chain a go!"Commit")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ (k : GoString) (v : w64),
        ⌜args = encCommitArgs k v⌝ ∗ p ↦ transport.netrpc.CommitArgs.mk k v else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Commit]
    icases HS with ⟨%k, %v, %Hargs, HS⟩
    isplitl [HS]
    · iexists k, v
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_CommitArgs _ _ k v
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists k, v
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ transport.netrpc.CommitArgs.mk go!"" (W64 0) $$ [Hp]
  · rw [show transport.netrpc.CommitArgs.mk go!"" (W64 0) = zero_val transport.netrpc.CommitArgs from rfl]; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%k, %v, %Hm, Hp⟩
  rw [nodeSpec_Commit]
  icases HS with ⟨%k', %v', %Hargs, Hcv, HS⟩
  obtain ⟨rfl, rfl⟩ := I.encCommitArgs_inj k k' v v' (Hm ▸ Hl) (Hm ▸ Hargs)
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  iStructNamed Hbs
  wp_auto
  unfold isNodeSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, -, -, #HC, -⟩
  iStructNamed Hp
  (try wp_auto)
  wp_apply HC $$ %k %v %_ Hcv as %err Herr
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  unfold errNE
  icases Herr with (%Herr | ⟨%msg, %Hmsg, #Hem⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_EmptyReply
    isplitr [HΦ]
    · iexact «$r0»
    iintro _
    iexact HΦ
  · iright
    iexists msg
    iframe Hem
    rw [if_neg Hmsg]
    icases HS with ⟨-, HΦ⟩
    unfold errOk
    iapply HΦ
    ipureintro; exact Hmsg

theorem newArg_LatestVersion (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"LatestVersion")
      (mOf examples.craqnet.rpcNewArg_r0_LatestVersion examples.craqnet.rpcNewReply_r0_LatestVersion
        examples.craqnet.rpcCall_r0_LatestVersion) := by
  iintro #Hb
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  unfold nodeB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface go.string p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface go.string p) (p ↦ (go!"" : GoString))
      (nodeSpec cfg.γ cfg.chain a go!"LatestVersion")
      (fun args ok => iprop(if ok then ∃ k : GoString, ⌜args = encString k⌝ ∗ p ↦ k else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_LatestVersion]
    icases HS with ⟨%k, %Q, %Hargs, HS⟩
    isplitl [HS]
    · iexists k, Q
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_string _ _ k
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists k
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ (go!"" : GoString) $$ [Hp]
  · rw [show (go!"" : GoString) = zero_val GoString from rfl]; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  simp only [ite_true]
  icases Hp with ⟨%k, %Hm, Hp⟩
  rw [nodeSpec_LatestVersion]
  icases HS with ⟨%k', %Q, %Hargs, HAU, HS⟩
  have hk : k = k' := I.encString_inj k k' (Hm ▸ Hargs)
  subst hk
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  iStructNamed Hbs
  wp_auto
  unfold isNodeSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, -, -, -, #HL, -⟩
  wp_apply HL $$ %k %Q %_ HAU as %k' %v %err Herr
  (try wp_auto)
  unfold errNE
  icases Herr with (⟨⟨%Herr, %Hk⟩, %σ, HQ, Hrf⟩ | ⟨%msg, %Hmsg, #Hem⟩)
  · subst Herr Hk
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    ileft
    isplitr
    · ipureintro; rfl
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_VersionResponse _ _ k' v
    isplitr [HΦ HQ Hrf]
    · iexact «$r0»
    iintro _
    iapply HΦ $$ HQ Hrf
  · unfold net.rpc.errMsg
    icases Hem with ⟨%ee, %Hee, %Hty, #HE⟩
    subst Hee
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    iright
    iexists msg
    isplitr [HS]
    · unfold net.rpc.errMsg
      iexists ee
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact Hty
      iexact HE
    rw [if_neg Hmsg]
    icases HS with ⟨-, HΦ⟩
    unfold errOk
    iapply HΦ
    ipureintro; exact Hmsg

theorem newArg_Read (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"Read")
      (mOf examples.craqnet.rpcNewArg_r0_Read examples.craqnet.rpcNewReply_r0_Read
        examples.craqnet.rpcCall_r0_Read) := by
  iintro #Hb
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  unfold nodeB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface go.string p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface go.string p) (p ↦ (go!"" : GoString))
      (nodeSpec cfg.γ cfg.chain a go!"Read")
      (fun args ok => iprop(if ok then ∃ k : GoString, ⌜args = encString k⌝ ∗ p ↦ k else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Read]
    icases HS with ⟨%k, %Q, %Hargs, HS⟩
    isplitl [HS]
    · iexists k, Q
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_string _ _ k
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists k
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ (go!"" : GoString) $$ [Hp]
  · rw [show (go!"" : GoString) = zero_val GoString from rfl]; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  simp only [ite_true]
  icases Hp with ⟨%k, %Hm, Hp⟩
  rw [nodeSpec_Read]
  icases HS with ⟨%k', %Q, %Hargs, HAU, HS⟩
  have hk : k = k' := I.encString_inj k k' (Hm ▸ Hargs)
  subst hk
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  iStructNamed Hbs
  wp_auto
  unfold isNodeSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, -, -, -, -, #HR, -⟩
  wp_apply HR $$ %k %Q %_ HAU as %k' %sl %err Herr
  (try wp_auto)
  unfold readCont
  icases Herr with (⟨⟨%Herr, %Hk⟩, %x, %σ, #Hsl, HQ, %Hσ⟩ | ⟨#Hem, %σ, HQ, %Hσ⟩ | ⟨%msg, ⟨%Hmsg, %Hnf⟩, #Hem⟩)
  · subst Herr Hk
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    ileft
    isplitr
    · ipureintro; rfl
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_Item _ _ k' sl _ x
    isplitl [«$r0»]
    · iexact «$r0»
    isplitr [HΦ HQ]
    · iexact Hsl
    iintro _ _
    iapply HΦ $$ HQ
    ipureintro; exact Hσ
  · unfold net.rpc.errMsg
    icases Hem with ⟨%ee, %Hee, %Hty, #HE⟩
    subst Hee
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    iright
    iexists notFoundMsg
    isplitr [HS HQ]
    · unfold net.rpc.errMsg
      iexists ee
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact Hty
      iexact HE
    rw [if_neg (by decide)]
    icases HS with ⟨-, HΦ, -⟩
    iapply HΦ $$ HQ
    ipureintro; exact Hσ
  · unfold net.rpc.errMsg
    icases Hem with ⟨%ee, %Hee, %Hty, #HE⟩
    subst Hee
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    iright
    iexists msg
    isplitr [HS]
    · unfold net.rpc.errMsg
      iexists ee
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact Hty
      iexact HE
    rw [if_neg Hmsg]
    icases HS with ⟨-, -, HΦ⟩
    iapply HΦ
    ipureintro; exact ⟨Hmsg, Hnf⟩

end proofs

end netrpcP

end github_com.despreston.go_craq

end Perennial
