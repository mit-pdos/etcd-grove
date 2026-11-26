/-
The receivers (`NetRpc/Specs.lean`: `masterRcv.spec`, `replicaRcv.spec`): the generated
`rpcReceiver` (`examples/epaxosnet/rpc_model_gen.go`) on a `*master.Master` or a
`*epaxos.Replica` gives a `*Receiver` meeting Net's `rcvrIs` for the service's spec (`masterSvc`,
`replicaSvc`). Per method (`methodOk`): `NewArg()` allocates the argument, whose decoding of a
deposit's argument bytes is `CodecSrv.lean`'s `decA_*` (Net's `argDec`); the call obligation:
`NewReply()`, then `Call`, the receiver's method, whose spec (`masterRegister.spec`, ...,
hypotheses over the abstract persistent handle `isM`/`isR`) leaves the reply that
`CodecSrv.lean`'s `enc_*` encodes into the method spec's success answer. As dsv-craq's
`Craq/Netrpc/Bindings.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos

/-- The generated `Method` of the functions named `na`, `nr`, `cl`. -/
abbrev mOf [GooseExts] [GoSemanticsFunctions] [GoGlobalContext] (na nr cl : GoString) :
    net.rpc.Method :=
  net.rpc.Method.mk (functions na []) (functions nr []) (functions cl [])

section bindings
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

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
    (Sm : net.rpc.MSpec GF) (v : net.rpc.Method) :
    Persistent (newArgOk (hG := hG) C rcvr Sm v) := by
  unfold newArgOk; infer_instance

theorem methodOk_of (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (mm : Loc) (v : net.rpc.Method) :
    mm ↦□ v ∗ newArgOk C rcvr Sm v ⊢ net.rpc.methodOk C rcvr Sm mm := by
  unfold net.rpc.methodOk newArgOk
  iintro ⟨#Hm, #Hn⟩
  iexists v
  iframe Hm
  iexact Hn

theorem masterSvc_GetLeader (γ : EpNames) (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    masterSvc γ go!"GetLeader" args Φ = anySpec encGetLeaderArgs args Φ := by
  unfold masterSvc; rw [if_neg (by decide), if_pos rfl]

theorem masterSvc_GetReplicaList (γ : EpNames) (args : List w8)
    (Φ : List w8 → GoString → IProp GF) :
    masterSvc γ go!"GetReplicaList" args Φ = anySpec encGetReplicaListArgs args Φ := by
  unfold masterSvc; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem masterSvc_Register (γ : EpNames) (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    masterSvc γ go!"Register" args Φ = registerSpec γ args Φ := by
  unfold masterSvc; rw [if_pos rfl]

theorem replicaSvc_BeTheLeader (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"BeTheLeader" args Φ = btlSpec args Φ := by
  unfold replicaSvc; rw [if_pos rfl]

theorem replicaSvc_Ping (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"Ping" args Φ = pingSpec args Φ := by
  unfold replicaSvc; rw [if_neg (by decide), if_pos rfl]

theorem newArg_GetLeader (L : SrvCodecLaws (GF := GF)) (γ : EpNames) (isM : Loc → IProp GF)
    [hM : ∀ m, Persistent (isM m)] (HGL : masterGetLeader.spec isM) (m : Loc) :
    net.rpc.codecSet epCodec ∗ isM m ⊢
    newArgOk epCodec (ptrIface master.Master.ty m) (masterSvc γ go!"GetLeader")
      (mOf examples.epaxosnet.rpcNewArg_r0_GetLeader examples.epaxosnet.rpcNewReply_r0_GetLeader
        examples.epaxosnet.rpcCall_r0_GetLeader) := by
  iintro ⟨#Hcs, #HM⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface replica.defs.GetLeaderArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec epCodec (ptrIface replica.defs.GetLeaderArgs.ty p)
      (p ↦ replica.defs.GetLeaderArgs.mk) (masterSvc γ go!"GetLeader")
      (fun _ _ => p ↦ replica.defs.GetLeaderArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [masterSvc_GetLeader]
    unfold anySpec
    icases HS with ⟨%Hargs, HS⟩
    isplitl [HS]
    · isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_GetLeaderArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  rw [masterSvc_GetLeader]
  unfold anySpec
  icases HS with ⟨-, HS⟩
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
  ihave Hr : «$r0_ptr» ↦ replica.defs.GetLeaderReply.mk (W64 0) $$ [«$r0»]
  · rw [show replica.defs.GetLeaderReply.mk (W64 0) = zero_val replica.defs.GetLeaderReply
      from rfl]
    iexact «$r0»
  wp_apply (HGL m p «$r0_ptr») $$ [Hp Hr] as ⟨%id, Hr⟩
  · iframe; iexact HM
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply L.enc_GetLeaderReply
  iframe
  iintro _
  iapply HS

theorem newArg_GetReplicaList (L : SrvCodecLaws (GF := GF)) (γ : EpNames)
    (isM : Loc → IProp GF) [hM : ∀ m, Persistent (isM m)] (HGR : masterGetReplicaList.spec isM)
    (m : Loc) :
    net.rpc.codecSet epCodec ∗ isM m ⊢
    newArgOk epCodec (ptrIface master.Master.ty m) (masterSvc γ go!"GetReplicaList")
      (mOf examples.epaxosnet.rpcNewArg_r0_GetReplicaList
        examples.epaxosnet.rpcNewReply_r0_GetReplicaList
        examples.epaxosnet.rpcCall_r0_GetReplicaList) := by
  iintro ⟨#Hcs, #HM⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface replica.defs.GetReplicaListArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec epCodec (ptrIface replica.defs.GetReplicaListArgs.ty p)
      (p ↦ replica.defs.GetReplicaListArgs.mk) (masterSvc γ go!"GetReplicaList")
      (fun _ _ => p ↦ replica.defs.GetReplicaListArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [masterSvc_GetReplicaList]
    unfold anySpec
    icases HS with ⟨%Hargs, HS⟩
    isplitl [HS]
    · isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_GetReplicaListArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  rw [masterSvc_GetReplicaList]
  unfold anySpec
  icases HS with ⟨-, HS⟩
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
  ihave Hr : «$r0_ptr» ↦ replica.defs.GetReplicaListReply.mk slice.nil slice.nil false $$ [«$r0»]
  · rw [show replica.defs.GetReplicaListReply.mk slice.nil slice.nil false =
      zero_val replica.defs.GetReplicaListReply from rfl]
    iexact «$r0»
  wp_apply (HGR m p «$r0_ptr») $$ [Hp Hr] as ⟨%sr, %sa, %rl, %al, %r, Hr, Hsr, Hsa⟩
  · iframe; iexact HM
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply L.enc_GetReplicaListReply
  iframe
  iintro _ _ _
  iapply HS

theorem newArg_Register (L : SrvCodecLaws (GF := GF)) (I : ArgFacts)
    (Hlen : decLen.spec (GF := GF)) (γ : EpNames)
    (isM : Loc → IProp GF) [hM : ∀ m, Persistent (isM m)] (HReg : masterRegister.spec γ isM)
    (m : Loc) :
    net.rpc.codecSet epCodec ∗ isM m ⊢
    newArgOk epCodec (ptrIface master.Master.ty m) (masterSvc γ go!"Register")
      (mOf examples.epaxosnet.rpcNewArg_r0_Register examples.epaxosnet.rpcNewReply_r0_Register
        examples.epaxosnet.rpcCall_r0_Register) := by
  iintro ⟨#Hcs, #HM⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface replica.defs.RegisterArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec epCodec (ptrIface replica.defs.RegisterArgs.ty p)
      (p ↦ replica.defs.RegisterArgs.mk go!"" (W64 0)) (masterSvc γ go!"Register")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ (addr : GoString) (port : w64),
        ⌜args = encRegisterArgs addr port⌝ ∗ p ↦ replica.defs.RegisterArgs.mk addr port
        else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [masterSvc_Register]
    unfold registerSpec
    icases HS with ⟨%k, %Hargs, HS⟩
    isplitl [HS]
    · iexists k
      isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply Hlen
    iintro %_
    iapply L.decA_RegisterArgs _ _ (replicaIp k) (portOf k)
    iframe
    isplitr
    · ipureintro; exact Hargs.2
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists (replicaIp k), (portOf k)
      iframe
      ipureintro; exact Hargs.2
  ihave Hp : p ↦ replica.defs.RegisterArgs.mk go!"" (W64 0) $$ [Hp]
  · rw [show replica.defs.RegisterArgs.mk go!"" (W64 0) = zero_val replica.defs.RegisterArgs
      from rfl]
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%addr, %port, %Hm, Hp⟩
  rw [masterSvc_Register]
  unfold registerSpec
  icases HS with ⟨%k, ⟨%hk, %Hargs⟩, HS⟩
  obtain ⟨rfl, rfl⟩ := I.encRegisterArgs_inj addr (replicaIp k) port (portOf k) (Hm ▸ Hl)
    (Hm ▸ Hargs)
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
  ihave Hr : «$r0_ptr» ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false $$ [«$r0»]
  · rw [show replica.defs.RegisterReply.mk (W64 0) slice.nil false false =
      zero_val replica.defs.RegisterReply from rfl]
    iexact «$r0»
  wp_apply (HReg m k p «$r0_ptr» hk) $$ [Hp Hr]
    as ⟨%id, %sl, %dq, %nl, %r, %il, Hr, Hsl, #Hok⟩
  · iframe; iexact HM
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  icases HS with ⟨HΦ, -⟩
  iapply L.enc_RegisterReply
  iframe
  iintro _ _
  iapply HΦ
  iexact Hok

theorem newArg_BeTheLeader (L : SrvCodecLaws (GF := GF)) (isR : Loc → IProp GF)
    [hR : ∀ r, Persistent (isR r)] (HB : replicaBtl.spec isR) (r : Loc) :
    net.rpc.codecSet epCodec ∗ isR r ⊢
    newArgOk epCodec (ptrIface epaxos.Replica.ty r) (replicaSvc go!"BeTheLeader")
      (mOf examples.epaxosnet.rpcNewArg_r1_BeTheLeader
        examples.epaxosnet.rpcNewReply_r1_BeTheLeader
        examples.epaxosnet.rpcCall_r1_BeTheLeader) := by
  iintro ⟨#Hcs, #HR⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface replica.defs.BeTheLeaderArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec epCodec (ptrIface replica.defs.BeTheLeaderArgs.ty p)
      (p ↦ replica.defs.BeTheLeaderArgs.mk) (replicaSvc go!"BeTheLeader")
      (fun _ _ => p ↦ replica.defs.BeTheLeaderArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [replicaSvc_BeTheLeader]
    unfold btlSpec
    icases HS with ⟨%Hargs, HS⟩
    isplitl [HS]
    · isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_BtlArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  rw [replicaSvc_BeTheLeader]
  unfold btlSpec
  icases HS with ⟨-, HS⟩
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
  ihave Hr : «$r0_ptr» ↦ replica.defs.BeTheLeaderReply.mk (W32 0) (W32 0) $$ [«$r0»]
  · rw [show replica.defs.BeTheLeaderReply.mk (W32 0) (W32 0) =
      zero_val replica.defs.BeTheLeaderReply from rfl]
    iexact «$r0»
  wp_apply (HB r p «$r0_ptr») $$ [Hp Hr] as Hr
  · iframe; iexact HR
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  icases HS with ⟨HΦ, -⟩
  iapply L.enc_BtlReply
  iframe
  iintro _
  rw [show encBtlReply (W32 0) (W32 0) = btlReplyBytes from rfl]
  iexact HΦ

theorem newArg_Ping (L : SrvCodecLaws (GF := GF)) (isR : Loc → IProp GF)
    [hR : ∀ r, Persistent (isR r)] (HP : replicaPing.spec isR) (r : Loc) :
    net.rpc.codecSet epCodec ∗ isR r ⊢
    newArgOk epCodec (ptrIface epaxos.Replica.ty r) (replicaSvc go!"Ping")
      (mOf examples.epaxosnet.rpcNewArg_r1_Ping examples.epaxosnet.rpcNewReply_r1_Ping
        examples.epaxosnet.rpcCall_r1_Ping) := by
  iintro ⟨#Hcs, #HR⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface replica.defs.PingArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec epCodec (ptrIface replica.defs.PingArgs.ty p)
      (p ↦ replica.defs.PingArgs.mk (W8 0)) (replicaSvc go!"Ping")
      (fun _ ok => if ok then p ↦ replica.defs.PingArgs.mk (W8 0) else iprop(True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    rw [replicaSvc_Ping]
    unfold pingSpec
    icases HS with ⟨%Hargs, HS⟩
    isplitl [HS]
    · isplitr
      · ipureintro; exact Hargs
      iexact HS
    iapply L.decA_PingArgs _ _ (W8 0)
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]; iexact Hp
  ihave Hp : p ↦ replica.defs.PingArgs.mk (W8 0) $$ [Hp]
  · rw [show replica.defs.PingArgs.mk (W8 0) = zero_val replica.defs.PingArgs from rfl]
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  simp only [ite_true]
  rw [replicaSvc_Ping]
  unfold pingSpec
  icases HS with ⟨-, HS⟩
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
  ihave Hr : «$r0_ptr» ↦ replica.defs.PingReply.mk $$ [«$r0»]
  · rw [show replica.defs.PingReply.mk = zero_val replica.defs.PingReply from rfl]
    iexact «$r0»
  wp_apply (HP r p «$r0_ptr» (W8 0)) $$ [Hp Hr] as Hr
  · iframe; iexact HR
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  icases HS with ⟨HΦ, -⟩
  iapply L.enc_PingReply
  iframe
  iintro _
  rw [show encPingReply = pingReplyBytes from rfl]
  iexact HΦ

theorem epCodec_rcv_eq (rcvr : GoInterface) (Ψ : Loc → IProp GF) :
    epCodec.rcv rcvr Ψ = iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
      WP (App (Val #(functions examples.epaxosnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }}) := rfl

theorem masterRcv_holds (L : SrvCodecLaws (GF := GF)) (I : ArgFacts)
    (Hlen : decLen.spec (GF := GF)) (γ : EpNames) (isM : Loc → IProp GF)
    [hM : ∀ m, Persistent (isM m)] (HReg : masterRegister.spec γ isM)
    (HGL : masterGetLeader.spec isM) (HGR : masterGetReplicaList.spec isM) :
    masterRcv.spec γ isM := by
  intro m
  iintro ⟨%Hnn, #Hcs, #HM⟩
  rw [epCodec_rcv_eq]
  iintro %Φ HΦ
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
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk epCodec
    (ptrIface master.Master.ty m) (masterSvc γ k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H2
    iapply newArg_Register L I Hlen γ isM HReg m
    iframe Hcs HM
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk epCodec
    (ptrIface master.Master.ty m) (masterSvc γ k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H1
    iapply newArg_GetReplicaList L γ isM HGR m
    iframe Hcs HM
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk epCodec
    (ptrIface master.Master.ty m) (masterSvc γ k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply newArg_GetLeader L γ isM HGL m
    iframe Hcs HM
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

theorem replicaRcv_holds (L : SrvCodecLaws (GF := GF)) (isR : Loc → IProp GF)
    [hR : ∀ r, Persistent (isR r)] (HB : replicaBtl.spec isR) (HP : replicaPing.spec isR) :
    replicaRcv.spec isR := by
  intro r
  iintro ⟨%Hnn, #Hcs, #HR⟩
  rw [epCodec_rcv_eq]
  iintro %Φ HΦ
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
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk epCodec
    (ptrIface epaxos.Replica.ty r) (replicaSvc k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H1
    iapply newArg_Ping L isR HP r
    iframe Hcs HR
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk epCodec
    (ptrIface epaxos.Replica.ty r) (replicaSvc k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply newArg_BeTheLeader L isR HB r
    iframe Hcs HR
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

end bindings

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial
