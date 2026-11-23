/-
The master's receiver (`master.rcvr.spec`, `Proof/master/Run.lean`): the generated `rpcReceiver`
(`examples/swiftnet/rpc_model_gen.go`) on a `*master.Master` gives a `*Receiver` meeting Net's
`rcvrIs` for `withErr sp.masterSpec` under the name `"Master"`. Per method (`methodOk`):
`NewArg()` allocates the argument, whose decoding of a deposit's argument bytes is
`swiftSrvCodecLaws`' `decA_*` (Net's `argDec`); the call obligation: `NewReply()`, then `Call`,
the master's method (`master.Master.Register.wp_proof`, `GetLeader`, `GetReplicaList`), whose
reply `swiftSrvCodecLaws`' `enc_*` encodes into the method spec's success answer. As dsv-epaxos's
`NetRpc/Bindings.lean` (`masterRcv_holds`). Replaces the lab's proof (lab master 915f964,
`Proof/master/Rcvr.lean`) through kitgen's dispatch `rpcCall` and its codec functions' specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RegisterDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.MethodsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RunVocab
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.Bind
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecSrvProof

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open netrpcw

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions]

set_option goose.wp.extras true

theorem master.masterSpec_GL_args (γc γm : GName) (args : List w8)
    (Φ : List w8 → GoString → IProp netDistGF) :
    sp.masterSpec γc γm go!"GetLeader" args Φ ⊢ ⌜args = encGetLeaderArgs⌝ :=
  (sp.masterSpec_getLeader args Φ).1.trans (by iintro ⟨%h, -⟩; ipureintro; exact h)

theorem master.masterSpec_GRL_args (γc γm : GName) (args : List w8)
    (Φ : List w8 → GoString → IProp netDistGF) :
    sp.masterSpec γc γm go!"GetReplicaList" args Φ ⊢ ⌜args = encGetReplicaListArgs⌝ :=
  (sp.masterSpec_getReplicaList args Φ).1.trans (by iintro ⟨%h, -⟩; ipureintro; exact h)

theorem master.masterSpec_Reg_args (γc γm : GName) (args : List w8)
    (Φ : List w8 → GoString → IProp netDistGF) :
    sp.masterSpec γc γm go!"Register" args Φ ⊢
      ⌜∃ (ip : GoString) (port : w64), args = encRegisterArgs ip port⌝ :=
  (sp.masterSpec_register args Φ).1.trans (by
    iintro ⟨%ip, %port, %c, %k, ⟨%h, -⟩, -⟩
    ipureintro; exact ⟨ip, port, h⟩)

theorem master.newArg_GetLeader (wp_GL : master.Master.GetLeader.spec (hG := hG))
    (γc γm : GName) (N : Nat) (m : Loc) :
    net.rpc.codecSet swiftCodec ∗ master.isMaster m γc γm N ⊢
    newArgOk swiftCodec (ptrIface master.Master.ty m)
      (withErr (sp.masterSpec γc γm) go!"GetLeader")
      (mOf examples.swiftnet.rpcNewArg_r0_GetLeader examples.swiftnet.rpcNewReply_r0_GetLeader
        examples.swiftnet.rpcCall_r0_GetLeader) := by
  iintro ⟨#Hcs, #HM⟩
  ihave #Hpm := master.isMaster_pkg m γc γm N $$ HM
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
  ihave #Hdec : net.rpc.argDec swiftCodec (ptrIface replica.defs.GetLeaderArgs.ty p)
      (p ↦ replica.defs.GetLeaderArgs.mk) (withErr (sp.masterSpec γc γm) go!"GetLeader")
      (fun _ _ => p ↦ replica.defs.GetLeaderArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    icases withErr_pure _ _ _ _ _ (master.masterSpec_GL_args γc γm args Φ) $$ HS
      with ⟨%Hargs, HS⟩
    iframe HS
    iapply (swiftSrvCodecLaws (GF := netDistGF)).decA_GetLeaderArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  unfold withErr
  icases HS with ⟨HS, -⟩
  ihave HS := (sp.masterSpec_getLeader (γc := γc) (γm := γm) args Φ).1 $$ HS
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
  wp_apply (wp_GL m γc γm N p «$r0_ptr» _) $$ [$Hpm $HM $«$r0»]
    as ⟨%id, Hr⟩
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply (swiftSrvCodecLaws (GF := netDistGF)).enc_GetLeaderReply
  iframe
  iintro _
  rw [show encGetLeaderReply id = (sp.KitVal.getLeaderReply id).encode from rfl]
  iapply HS

theorem master.newArg_GetReplicaList
    (wp_GRL : master.Master.GetReplicaList.spec (hG := hG))
    (γc γm : GName) (N : Nat) (m : Loc) :
    net.rpc.codecSet swiftCodec ∗ master.isMaster m γc γm N ⊢
    newArgOk swiftCodec (ptrIface master.Master.ty m)
      (withErr (sp.masterSpec γc γm) go!"GetReplicaList")
      (mOf examples.swiftnet.rpcNewArg_r0_GetReplicaList
        examples.swiftnet.rpcNewReply_r0_GetReplicaList
        examples.swiftnet.rpcCall_r0_GetReplicaList) := by
  iintro ⟨#Hcs, #HM⟩
  ihave #Hpm := master.isMaster_pkg m γc γm N $$ HM
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
  ihave #Hdec : net.rpc.argDec swiftCodec (ptrIface replica.defs.GetReplicaListArgs.ty p)
      (p ↦ replica.defs.GetReplicaListArgs.mk)
      (withErr (sp.masterSpec γc γm) go!"GetReplicaList")
      (fun _ _ => p ↦ replica.defs.GetReplicaListArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    icases withErr_pure _ _ _ _ _ (master.masterSpec_GRL_args γc γm args Φ) $$ HS
      with ⟨%Hargs, HS⟩
    iframe HS
    iapply (swiftSrvCodecLaws (GF := netDistGF)).decA_GetReplicaListArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  unfold withErr
  icases HS with ⟨HS, -⟩
  ihave HS := (sp.masterSpec_getReplicaList (γc := γc) (γm := γm) args Φ).1 $$ HS
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
  wp_apply (wp_GRL m γc γm N p «$r0_ptr» _)
    $$ [$Hpm $HM $«$r0»] as ⟨%s1, %s2, %nodes, %alive, Hr, Hs1, Hs2, #Hcfg, %Hal⟩
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply (swiftSrvCodecLaws (GF := netDistGF)).enc_GetReplicaListReply
  iframe
  iintro _ _ _
  rw [show encGetReplicaListReply nodes alive true =
    (sp.KitVal.getReplicaListReply nodes alive true).encode from rfl]
  iapply HS $$ Hcfg
  ipureintro; exact Hal

theorem master.newArg_Register
    (wp_Reg : master.Master.Register.spec (hG := hG))
    (γc γm : GName) (N : Nat) (m : Loc) :
    net.rpc.codecSet swiftCodec ∗ master.isMaster m γc γm N ⊢
    newArgOk swiftCodec (ptrIface master.Master.ty m)
      (withErr (sp.masterSpec γc γm) go!"Register")
      (mOf examples.swiftnet.rpcNewArg_r0_Register examples.swiftnet.rpcNewReply_r0_Register
        examples.swiftnet.rpcCall_r0_Register) := by
  iintro ⟨#Hcs, #HM⟩
  ihave #Hpm := master.isMaster_pkg m γc γm N $$ HM
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
  ihave #Hdec : net.rpc.argDec swiftCodec (ptrIface replica.defs.RegisterArgs.ty p)
      (p ↦ replica.defs.RegisterArgs.mk go!"" (W64 0))
      (withErr (sp.masterSpec γc γm) go!"Register")
      (fun args ok => iprop(⌜args.length < 2 ^ 63⌝ ∗ if ok then ∃ (addr : GoString) (port : w64),
        ⌜args = encRegisterArgs addr port⌝ ∗ p ↦ replica.defs.RegisterArgs.mk addr port
        else True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    icases withErr_pure _ _ _ _ _ (master.masterSpec_Reg_args γc γm args Φ) $$ HS
      with ⟨%Hargs, HS⟩
    obtain ⟨ip, port, Hargs⟩ := Hargs
    iframe HS
    iapply swiftDecLen
    iintro %_
    iapply (swiftSrvCodecLaws (GF := netDistGF)).decA_RegisterArgs _ _ ip port
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]
      iexists ip, port
      iframe
      ipureintro; exact Hargs
  ihave Hp : p ↦ replica.defs.RegisterArgs.mk go!"" (W64 0) $$ [Hp]
  · rw [show replica.defs.RegisterArgs.mk go!"" (W64 0) = zero_val replica.defs.RegisterArgs
      from rfl]
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS ⟨%Hl, Hp⟩
  simp only [ite_true]
  icases Hp with ⟨%addr, %port', %Hm, Hp⟩
  unfold withErr
  icases HS with ⟨HS, -⟩
  ihave HS := (sp.masterSpec_register (γc := γc) (γm := γm) args Φ).1 $$ HS
  icases HS with ⟨%ip, %port, %c, %k, %Hargs, #Hc, HΦ⟩
  obtain ⟨Hargs, Hk, Hkc⟩ := Hargs
  obtain ⟨rfl, rfl⟩ := swiftArgFacts.encRegisterArgs_inj addr ip port' port
    (by rw [← Hm]; exact Hl) (Hm.symm.trans Hargs)
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
  wp_apply (wp_Reg m γc γm N p «$r0_ptr» addr port' c k _)
    $$ [$Hpm $HM $Hp $«$r0» $Hc] as ⟨%rv', Hr, Hready⟩
  · ipureintro; exact ⟨Hk, Hkc⟩
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  obtain ⟨id, nlS, ready, isL⟩ := rv'
  cases ready
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hready with %Hrv
    simp only [replica.defs.RegisterReply.mk.injEq] at Hrv
    obtain ⟨rfl, rfl, -, rfl⟩ := Hrv
    ihave Hnil := ownSlice_nil (V := GoString) (GF := netDistGF) (DFrac.own 1)
    iapply (swiftSrvCodecLaws (GF := netDistGF)).enc_RegisterReply
    iframe Hr Hnil
    iintro _ _
    rw [show ∀ i nl r l, encRegisterReply i nl r l = (sp.KitVal.registerReply i nl r l).encode
      from fun _ _ _ _ => rfl]
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · simp only [↓reduceIte]
    icases Hready with ⟨%nodes, #Hnodes, #Hcfg, %Hid⟩
    iapply (swiftSrvCodecLaws (GF := netDistGF)).enc_RegisterReply
    iframe Hr Hnodes
    iintro _ _
    rw [show ∀ i nl r l, encRegisterReply i nl r l = (sp.KitVal.registerReply i nl r l).encode
      from fun _ _ _ _ => rfl]
    iapply HΦ
    simp only [↓reduceIte]
    icases Hcfg with ⟨%fr, #Hcfg⟩
    iexists fr
    iframe Hcfg
    ipureintro; exact Hid

set_option maxHeartbeats 4000000 in
theorem master.rcvr.wp_proof
    (wp_GL : master.Master.GetLeader.spec (hG := hG))
    (wp_GRL : master.Master.GetReplicaList.spec (hG := hG))
    (wp_Reg : master.Master.Register.spec (hG := hG)) :
    master.rcvr.spec := by
  intro m γc γm N
  rw [rpcCodec_spec_eq]
  iintro ⟨%Hnn, #Hcs, #HM⟩
  rw [swiftCodec_rcv_eq]
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
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk swiftCodec
    (ptrIface master.Master.ty m) (withErr (sp.masterSpec γc γm) k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H2
    iapply master.newArg_Register wp_Reg γc γm N m
    iframe Hcs HM
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk swiftCodec
    (ptrIface master.Master.ty m) (withErr (sp.masterSpec γc γm) k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H1
    iapply master.newArg_GetReplicaList wp_GRL γc γm N m
    iframe Hcs HM
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk swiftCodec
    (ptrIface master.Master.ty m) (withErr (sp.masterSpec γc γm) k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply master.newArg_GetLeader wp_GL γc γm N m
    iframe Hcs HM
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
