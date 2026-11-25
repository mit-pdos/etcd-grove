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
    ileft
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
    ileft
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
    ileft
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
    icases HS with ⟨%k, %v, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists k, v
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
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
  icases HS with ⟨%k', %v', ⟨%Hargs, %Hko⟩, Hcv, HS⟩
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
    ileft
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
    icases HS with ⟨%k, %Q, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists k, Q
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
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
  icases HS with ⟨%k', %Q, ⟨%Hargs, %Hko⟩, HAU, HS⟩
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
    ileft
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
    icases HS with ⟨%k, %Q, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists k, Q
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
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
  icases HS with ⟨%k', %Q, ⟨%Hargs, %Hko⟩, HAU, HS⟩
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
  wp_apply HR $$ %k %Q %_ %Hko HAU as %k' %sl %err Herr
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
    ileft
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
    ileft
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

theorem newArg_FwdPropagate (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"FwdPropagate")
      (mOf examples.craqnet.rpcNewArg_r0_FwdPropagate examples.craqnet.rpcNewReply_r0_FwdPropagate
        examples.craqnet.rpcCall_r0_FwdPropagate) := by
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
  have hne : ptrIface transport.PropagateRequest.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.PropagateRequest.ty p) (p ↦ (null : Loc))
      (nodeSpec cfg.γ cfg.chain a go!"FwdPropagate")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ req : GMap GoString w64,
        ⌜encPropReq req args⌝ ∗ reqPtr p (DFrac.own 1) req else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Fwd]
    icases HS with ⟨%req, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists req
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_PropagateRequest _ _ req
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists req
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ (null : Loc) $$ [Hp]
  · iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%req, %Hm, Hp⟩
  rw [nodeSpec_Fwd]
  icases HS with ⟨%req', ⟨%Hargs, %Hko⟩, HS⟩
  have hreq : req = req' := I.encPropReq_inj req req' args Hl Hm Hargs
  subst hreq
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := transport.PropagateResponse.ty)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) _ _) as %mp0 Hmp0
  (try wp_auto)
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
  icases Hm with ⟨-, -, -, -, -, -, #HP, -⟩
  wp_apply HP $$ %p %(DFrac.own 1) %req %_ Hp as %rp %err Hp Herr
  (try wp_auto)
  unfold errNE
  icases Herr with (⟨%Herr, %resp, Hrp, Hri⟩ | ⟨%msg, %Hmsg, #Hem⟩)
  · subst Herr
    unfold respPtr
    icases Hrp with ⟨%mp, %m, Hrp, Hrest⟩
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    ileft
    isplitr
    · ipureintro; rfl
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_PropagateResponse _ resp
    isplitr [HΦ Hri]
    · unfold respPtr
      iexists mp, m
      iframe
    iintro _ %bs %Henc
    iapply HΦ $$ %resp %bs %Henc Hri
  · unfold net.rpc.errMsg
    icases Hem with ⟨%ee, %Hee, %Hty, #HE⟩
    subst Hee
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    iright
    ileft
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

theorem newArg_BackPropagate (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"BackPropagate")
      (mOf examples.craqnet.rpcNewArg_r0_BackPropagate examples.craqnet.rpcNewReply_r0_BackPropagate
        examples.craqnet.rpcCall_r0_BackPropagate) := by
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
  have hne : ptrIface transport.PropagateRequest.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.PropagateRequest.ty p) (p ↦ (null : Loc))
      (nodeSpec cfg.γ cfg.chain a go!"BackPropagate")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ req : GMap GoString w64,
        ⌜encPropReq req args⌝ ∗ reqPtr p (DFrac.own 1) req else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [nodeSpec_Back]
    icases HS with ⟨%req, %Lg, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists req, Lg
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_PropagateRequest _ _ req
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists req
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ (null : Loc) $$ [Hp]
  · iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%req, %Hm, Hp⟩
  rw [nodeSpec_Back]
  icases HS with ⟨%req', %Lg, ⟨%Hargs, %Hko⟩, HL, HS⟩
  have hreq : req = req' := I.encPropReq_inj req req' args Hl Hm Hargs
  subst hreq
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := transport.PropagateResponse.ty)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) _ _) as %mp0 Hmp0
  (try wp_auto)
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
  icases Hm with ⟨-, -, -, -, -, -, -, #HP⟩
  wp_apply HP $$ %p %(DFrac.own 1) %req %Lg %_ Hp HL as %rp %err Hp Herr
  (try wp_auto)
  unfold errNE
  icases Herr with (⟨%Herr, %resp, Hrp, Hri, Hrc, %Hcov⟩ | ⟨%msg, %Hmsg, #Hem⟩)
  · subst Herr
    unfold respPtr
    icases Hrp with ⟨%mp, %m, Hrp, Hrest⟩
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    ileft
    isplitr
    · ipureintro; rfl
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_PropagateResponse _ resp
    isplitr [HΦ Hri Hrc]
    · unfold respPtr
      iexists mp, m
      iframe
    iintro _ %bs %Henc
    iapply HΦ $$ %resp %bs %Henc Hri Hrc %Hcov
  · unfold net.rpc.errMsg
    icases Hem with ⟨%ee, %Hee, %Hty, #HE⟩
    subst Hee
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    iright
    ileft
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

theorem nodeSpec_ClientWrite (γ : CraqNames) (ch : List GoString) (a : GoString) (args : List w8)
    (Φ : List w8 → GoString → IProp GF) :
    nodeSpec γ ch a go!"ClientWrite" args Φ = iprop(False) := by
  unfold nodeSpec; simp

theorem newArg_ClientWrite (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"ClientWrite")
      (mOf examples.craqnet.rpcNewArg_r0_ClientWrite examples.craqnet.rpcNewReply_r0_ClientWrite
        examples.craqnet.rpcCall_r0_ClientWrite) := by
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
  have hne : ptrIface transport.netrpc.ClientWriteArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.netrpc.ClientWriteArgs.ty p) iprop(True)
      (nodeSpec cfg.γ cfg.chain a go!"ClientWrite") (fun _ _ => iprop(True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro _ %args %Φ HS
    rw [nodeSpec_ClientWrite]
    icases HS with ⟨⟩
  iapply HΨ $$ %_ %_ %_ %hne Hdec []
  · itrivial
  iintro %args %Φ HS _
  rw [nodeSpec_ClientWrite]
  icases HS with ⟨⟩

theorem nodeSpec_ReadAll (γ : CraqNames) (ch : List GoString) (a : GoString) (args : List w8)
    (Φ : List w8 → GoString → IProp GF) :
    nodeSpec γ ch a go!"ReadAll" args Φ = iprop(False) := by
  unfold nodeSpec; simp

theorem newArg_ReadAll (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
      (nodeSpec cfg.γ cfg.chain a go!"ReadAll")
      (mOf examples.craqnet.rpcNewArg_r0_ReadAll examples.craqnet.rpcNewReply_r0_ReadAll
        examples.craqnet.rpcCall_r0_ReadAll) := by
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
  have hne : ptrIface transport.netrpc.EmptyArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.netrpc.EmptyArgs.ty p) iprop(True)
      (nodeSpec cfg.γ cfg.chain a go!"ReadAll") (fun _ _ => iprop(True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro _ %args %Φ HS
    rw [nodeSpec_ReadAll]
    icases HS with ⟨⟩
  iapply HΨ $$ %_ %_ %_ %hne Hdec []
  · itrivial
  iintro %args %Φ HS _
  rw [nodeSpec_ReadAll]
  icases HS with ⟨⟩

theorem nodeB_nn (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢ ⌜b ≠ null⌝ := by
  unfold nodeB
  iintro ⟨-, -, -, #Hbs, -⟩
  iapply typedPointsto_not_null _ _ _ $$ Hbs

theorem craqCodec_rcv_eq (rcvr : GoInterface) (Ψ : Loc → IProp GF) :
    craqCodec.rcv rcvr Ψ = iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
      WP (App (Val #(functions examples.craqnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }}) := rfl

theorem nodeRcv (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) (a : GoString) :
    nodeB cfg b svc a ⊢
    craqCodec.rcv (ptrIface transport.netrpc.NodeBinding.ty b)
      (net.rpc.rcvrIs craqCodec (ptrIface transport.netrpc.NodeBinding.ty b)
        (nodeSpec cfg.γ cfg.chain a) go!"NodeBinding" false) := by
  iintro #Hb
  rw [craqCodec_rcv_eq]
  iintro %Φ HΦ
  ihave %Hnn := nodeB_nn $$ Hb
  iapply wp_fupd
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) _ _) as %mp Hm
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m0 as H0
  ipersist H0
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m1 as H1
  ipersist H1
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m2 as H2
  ipersist H2
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m3 as H3
  ipersist H3
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m4 as H4
  ipersist H4
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m5 as H5
  ipersist H5
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m6 as H6
  ipersist H6
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m7 as H7
  ipersist H7
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m8 as H8
  ipersist H8
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m9 as H9
  ipersist H9
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  ipersist «$r0»
  imod ownMap_persist $$ Hm with #Hm
  iapply HΦ
  unfold net.rpc.rcvrIs
  iexists _, _
  iframe «$r0» Hm
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_⟩
    · simp [Hnn]
    · exact GMap.map_size_ne_0_lookup_2 _ (GMap.lookup_insert _ _ _)
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H9
    iapply newArg_Write L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H8
    iapply newArg_Update L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H7
    iapply newArg_ReadAll $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H6
    iapply newArg_Read L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H5
    iapply newArg_Ping L $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H4
    iapply newArg_LatestVersion L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H3
    iapply newArg_FwdPropagate L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H2
    iapply newArg_Commit L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H1
    iapply newArg_ClientWrite $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.NodeBinding.ty b) (nodeSpec cfg.γ cfg.chain a m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply newArg_BackPropagate L I Hlen $$ Hb
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

/-- The binding `b` of the coordinator service `svc`, and the packages (persistent). -/
def coordB (cfg : Cfg GF) (b : Loc) (svc : GoInterface) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet ∗
    net.rpc.codecSet craqCodec ∗
    b ↦□ transport.netrpc.CoordinatorBinding.mk svc ∗ isCoordSvc cfg svc)

instance coordB_persistent (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    Persistent (coordB (hG := hG) cfg b svc) := by
  unfold coordB; infer_instance

theorem coordB_nn (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    coordB cfg b svc ⊢ ⌜b ≠ null⌝ := by
  unfold coordB
  iintro ⟨-, -, -, #Hbs, -⟩
  iapply typedPointsto_not_null _ _ _ $$ Hbs

theorem cnewArg_AddNode (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    coordB cfg b svc ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (coordSpec cfg.γ cfg.chain go!"AddNode")
      (mOf examples.craqnet.rpcNewArg_r1_AddNode examples.craqnet.rpcNewReply_r1_AddNode
        examples.craqnet.rpcCall_r1_AddNode) := by
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
  unfold coordB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface go.string p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface go.string p) (p ↦ (go!"" : GoString))
      (coordSpec cfg.γ cfg.chain go!"AddNode")
      (fun args ok => iprop(if ok then ∃ k : GoString, ⌜args = encString k⌝ ∗ p ↦ k else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [coordSpec_AddNode]
    icases HS with ⟨%k, %Hargs, HS⟩
    isplitl [HS]
    · iexists k
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_string _ _ k
    iframe
    isplitr
    · ipureintro; exact Hargs.1
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists k
      iframe
      ipureintro; exact Hargs.1
  ihave Hp : p ↦ (go!"" : GoString) $$ [Hp]
  · rw [show (go!"" : GoString) = zero_val GoString from rfl]; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  simp only [ite_true]
  icases Hp with ⟨%k, %Hm, Hp⟩
  rw [coordSpec_AddNode]
  icases HS with ⟨%k', ⟨%Hargs, %Hin⟩, Hjt, HS⟩
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
  unfold isCoordSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨#HA, -⟩
  wp_apply HA $$ %k %_ %Hin Hjt as %mp %err Herr
  (try wp_auto)
  unfold errNE
  icases Herr with (⟨%Herr, %md, Hmp⟩ | ⟨%msg, %Hmsg, #Hem⟩)
  · subst Herr
    unfold metaPtr
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    ileft
    isplitr
    · ipureintro; rfl
    icases HS with ⟨HΦ, -⟩
    iapply L.enc_NodeMeta _ _ md
    isplitr [HΦ]
    · unfold metaPtr
      iexact «$r0»
    iintro _
    iapply HΦ
  · unfold net.rpc.errMsg
    icases Hem with ⟨%ee, %Hee, %Hty, #HE⟩
    subst Hee
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    unfold net.rpc.callRet
    iright
    ileft
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

theorem cnewArg_Write (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    coordB cfg b svc ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (coordSpec cfg.γ cfg.chain go!"Write")
      (mOf examples.craqnet.rpcNewArg_r1_Write examples.craqnet.rpcNewReply_r1_Write
        examples.craqnet.rpcCall_r1_Write) := by
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
  unfold coordB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface transport.netrpc.ClientWriteArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface transport.netrpc.ClientWriteArgs.ty p)
      (p ↦ transport.netrpc.ClientWriteArgs.mk go!"" slice.nil)
      (coordSpec cfg.γ cfg.chain go!"Write")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ (k x : GoString) (sl : GoSlice),
        ⌜args = encClientWriteArgs k x⌝ ∗ p ↦ transport.netrpc.ClientWriteArgs.mk k sl ∗
        sl ↦* x else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [coordSpec_Write]
    icases HS with ⟨%k, %x, %Q, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists k, x, Q
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_ClientWriteArgs _ _ k x
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      icases Hp with ⟨%sl, Hp, Hsl⟩
      iexists k, x, sl
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ transport.netrpc.ClientWriteArgs.mk go!"" slice.nil $$ [Hp]
  · rw [show transport.netrpc.ClientWriteArgs.mk go!"" slice.nil = zero_val transport.netrpc.ClientWriteArgs from rfl]; iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%k, %x, %sl, %Hm, Hp, Hsl⟩
  rw [coordSpec_Write]
  icases HS with ⟨%k', %x', %Q, ⟨%Hargs, %Hko⟩, HAU, HS⟩
  obtain ⟨rfl, rfl⟩ := I.encClientWriteArgs_inj k k' x x' (Hm ▸ Hl) (Hm ▸ Hargs)
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
  unfold isCoordSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, #HW, -⟩
  iStructNamed Hp
  (try wp_auto)
  wp_apply HW $$ %k %sl %x %Q %_ %Hko Hsl HAU as %err Herr
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
    ileft
    iexists msg
    iframe Hem
    rw [if_neg Hmsg]
    icases HS with ⟨-, HΦ⟩
    unfold errOk
    iapply HΦ
    ipureintro; exact Hmsg

/-- `RemoveNode` (finding F1, discharged): `CoordinatorBinding.RemoveNode` returns
`coordinator.RemoveNode`'s error, which may be a net/rpc client error (`models_lab.errAny`, its
message not fixed); `callRet`'s `errAny` branch takes it, with the spec's answer for any message
(the empty one: the reply's encoding, `Φ encEmptyReply []`). -/
theorem cnewArg_RemoveNode (L : SrvCodecLaws (GF := GF)) (I : ArgFacts)
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    coordB cfg b svc ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (coordSpec cfg.γ cfg.chain go!"RemoveNode")
      (mOf examples.craqnet.rpcNewArg_r1_RemoveNode examples.craqnet.rpcNewReply_r1_RemoveNode
        examples.craqnet.rpcCall_r1_RemoveNode) := by
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
  unfold coordB
  icases Hb with ⟨#Hpn, #Hpk, #Hcs, #Hbs, #Hsvc⟩
  have hne : ptrIface go.string p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec craqCodec (ptrIface go.string p) (p ↦ (go!"" : GoString))
      (coordSpec cfg.γ cfg.chain go!"RemoveNode")
      (fun args ok => iprop(if ok then ∃ k : GoString, ⌜args = encString k⌝ ∗ p ↦ k else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [coordSpec_RemoveNode]
    icases HS with ⟨%k, ⟨%Hargs, %Hko⟩, HS⟩
    isplitl [HS]
    · iexists k
      isplitr
      · ipureintro; exact ⟨Hargs, Hko⟩
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
  rw [coordSpec_RemoveNode]
  icases HS with ⟨%k', ⟨%Hargs, %Hko⟩, HS⟩
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
  unfold isCoordSvc
  icases Hsvc with ⟨%e, %He, #Hm⟩
  subst He
  icases Hm with ⟨-, -, #HR⟩
  (try wp_auto)
  wp_apply HR $$ %k as %err Herr
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  icases Herr with (%Herr | #Hany)
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
    iright
    isplitr
    · iapply models_lab.errPlain_errAny $$ Hany
    iintro %msg
    by_cases hmsg : msg = []
    · rw [if_pos hmsg]
      icases HS with ⟨HΦ, -⟩
      iapply L.enc_EmptyReply
      isplitr [HΦ]
      · iexact «$r0»
      iintro _
      iexact HΦ
    · rw [if_neg hmsg]
      icases HS with ⟨-, HΦ⟩
      iapply HΦ

theorem coordRcv (L : SrvCodecLaws (GF := GF)) (I : ArgFacts) (Hlen : decLen.spec (GF := GF))
    (cfg : Cfg GF) (b : Loc) (svc : GoInterface) :
    coordB cfg b svc ⊢
    craqCodec.rcv (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (net.rpc.rcvrIs craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
        (coordSpec cfg.γ cfg.chain) go!"CoordinatorBinding" false) := by
  iintro #Hb
  rw [craqCodec_rcv_eq]
  iintro %Φ HΦ
  ihave %Hnn := coordB_nn $$ Hb
  iapply wp_fupd
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) _ _) as %mp Hm
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m0 as H0
  ipersist H0
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m1 as H1
  ipersist H1
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m2 as H2
  ipersist H2
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  ipersist «$r0»
  imod ownMap_persist $$ Hm with #Hm
  iapply HΦ
  unfold net.rpc.rcvrIs
  iexists _, _
  iframe «$r0» Hm
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_⟩
    · simp [Hnn]
    · exact GMap.map_size_ne_0_lookup_2 _ (GMap.lookup_insert _ _ _)
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.CoordinatorBinding.ty b) (coordSpec cfg.γ cfg.chain m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H2
    iapply cnewArg_Write L I Hlen $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.CoordinatorBinding.ty b) (coordSpec cfg.γ cfg.chain m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H1
    iapply cnewArg_RemoveNode L I $$ Hb
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk craqCodec
    (ptrIface transport.netrpc.CoordinatorBinding.ty b) (coordSpec cfg.γ cfg.chain m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply cnewArg_AddNode L I Hlen $$ Hb
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

end proofs

end netrpcP

end github_com.despreston.go_craq

end Perennial
