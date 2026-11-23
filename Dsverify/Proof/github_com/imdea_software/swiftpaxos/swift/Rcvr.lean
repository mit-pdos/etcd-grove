/-
The replica's receiver (`swift.rcvr.spec`, `Spec/.../swift/New.lean`): the generated `rpcReceiver`
(`examples/swiftnet/rpc_model_gen.go`) on a `*swift.Replica` gives a `*Receiver` meeting Net's
`rcvrIs` for `withErr sp.replicaRpcSpec` under the name `"Replica"`, which `rpc.Register(rep)`
asks of the codec. Per method (`methodOk`): `NewArg()` allocates the argument, whose decoding of
a deposit's argument bytes is `swiftSrvCodecLaws`' `decA_*` (Net's `argDec`); the call
obligation: `NewReply()`, then `Call`, the replica's method (`BeTheLeader`, through its spec, a
premise; `Ping`, the embedded `*replica.Replica`'s, which does nothing), whose reply
`swiftSrvCodecLaws`' `enc_*` encodes into the method spec's success answer. As dsv-epaxos's
`NetRpc/Bindings.lean` (`replicaRcv_holds`). Replaces the lab's proof (lab master 915f964,
`Proof/swift/Rcvr.lean`) through kitgen's dispatch `rpcCall` and its codec functions' specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BeTheLeader
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.New
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [examples.swiftnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions]

set_option goose.wp.extras true

theorem swift.replicaRpcSpec_BTL_args (γc γm : GName) (args : List w8)
    (Φ : List w8 → GoString → IProp netDistGF) :
    sp.replicaRpcSpec γc γm go!"BeTheLeader" args Φ ⊢ ⌜args = encBtlArgs⌝ :=
  (sp.replicaRpcSpec_beTheLeader args Φ).1.trans (by iintro ⟨%h, -⟩; ipureintro; exact h)

theorem swift.replicaRpcSpec_Ping_args (γc γm : GName) (args : List w8)
    (Φ : List w8 → GoString → IProp netDistGF) :
    sp.replicaRpcSpec γc γm go!"Ping" args Φ ⊢ ⌜∃ a : w8, args = encPingArgs a⌝ :=
  (sp.replicaRpcSpec_ping args Φ).1.trans (by
    iintro ⟨%a, %h, -⟩; ipureintro; exact ⟨a, h⟩)

theorem swift.newArg_BeTheLeader (wp_BTL : swift.Replica.BeTheLeader.spec)
    (γc γm : GName) (r : Loc) :
    net.rpc.codecSet swiftCodec ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.rcvrRes r γc γm ⊢
    newArgOk swiftCodec (ptrIface swift.Replica.ty r)
      (withErr (sp.replicaRpcSpec γc γm) go!"BeTheLeader")
      (mOf examples.swiftnet.rpcNewArg_r1_BeTheLeader
        examples.swiftnet.rpcNewReply_r1_BeTheLeader
        examples.swiftnet.rpcCall_r1_BeTheLeader) := by
  iintro ⟨#Hcs, #Hpkg, #HR⟩
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
  ihave #Hdec : net.rpc.argDec swiftCodec (ptrIface replica.defs.BeTheLeaderArgs.ty p)
      (p ↦ replica.defs.BeTheLeaderArgs.mk)
      (withErr (sp.replicaRpcSpec γc γm) go!"BeTheLeader")
      (fun _ _ => p ↦ replica.defs.BeTheLeaderArgs.mk) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    icases withErr_pure _ _ _ _ _ (swift.replicaRpcSpec_BTL_args γc γm args Φ) $$ HS
      with ⟨%Hargs, HS⟩
    iframe HS
    iapply (swiftSrvCodecLaws (GF := netDistGF)).decA_BtlArgs
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  unfold withErr
  icases HS with ⟨HS, -⟩
  ihave HS := (sp.replicaRpcSpec_beTheLeader (γc := γc) (γm := γm) args Φ).1 $$ HS
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
  wp_apply (wp_BTL r γc γm p «$r0_ptr» _) $$ [$Hpkg $HR $«$r0»] as ⟨%ld, %nl, Hr, Hok⟩
  (try wp_auto)
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply (swiftSrvCodecLaws (GF := netDistGF)).enc_BtlReply
  iframe Hr
  iintro _
  rw [show encBtlReply ld nl = (sp.KitVal.beTheLeaderReply ld nl).encode from rfl]
  iapply HS $$ Hok

theorem swift.newArg_Ping (γc γm : GName) (r : Loc) :
    net.rpc.codecSet swiftCodec ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.rcvrRes r γc γm ⊢
    newArgOk swiftCodec (ptrIface swift.Replica.ty r)
      (withErr (sp.replicaRpcSpec γc γm) go!"Ping")
      (mOf examples.swiftnet.rpcNewArg_r1_Ping examples.swiftnet.rpcNewReply_r1_Ping
        examples.swiftnet.rpcCall_r1_Ping) := by
  iintro ⟨#Hcs, #Hpkg, #HR⟩
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
  ihave #Hdec : net.rpc.argDec swiftCodec (ptrIface replica.defs.PingArgs.ty p)
      (p ↦ replica.defs.PingArgs.mk (W8 0)) (withErr (sp.replicaRpcSpec γc γm) go!"Ping")
      (fun _ ok => if ok then iprop(∃ a : w8, p ↦ replica.defs.PingArgs.mk a)
        else iprop(True)) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    icases withErr_pure _ _ _ _ _ (swift.replicaRpcSpec_Ping_args γc γm args Φ) $$ HS
      with ⟨%Hargs, HS⟩
    obtain ⟨a, Hargs⟩ := Hargs
    iframe HS
    iapply (swiftSrvCodecLaws (GF := netDistGF)).decA_PingArgs _ _ a
    iframe
    isplitr
    · ipureintro; exact Hargs
    iintro %ok Hp
    cases ok
    · simp only [Bool.false_eq_true, ite_false]; itrivial
    · simp only [ite_true]; iexists a; iexact Hp
  ihave Hp : p ↦ replica.defs.PingArgs.mk (W8 0) $$ [Hp]
  · rw [show replica.defs.PingArgs.mk (W8 0) = zero_val replica.defs.PingArgs from rfl]
    iexact Hp
  iapply HΨ $$ %_ %_ %_ %hne Hdec Hp
  iintro %args %Φ HS Hp
  simp only [ite_true]
  unfold withErr
  icases HS with ⟨HS, -⟩
  ihave HS := (sp.replicaRpcSpec_ping (γc := γc) (γm := γm) args Φ).1 $$ HS
  icases HS with ⟨%a, -, HΦ⟩
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
  iunfold swift.rcvrRes at HR
  icases HR with ⟨%rr, %N, %fr, %l, %me, %dm, %qs, %rc, %γrc, %γdl, #Hrr, -⟩
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply (swiftSrvCodecLaws (GF := netDistGF)).enc_PingReply
  iframe
  iintro _
  rw [show encPingReply = sp.KitVal.pingReply.encode from rfl]
  iexact HΦ

set_option maxHeartbeats 4000000 in
theorem swift.rcvr.wp_proof (wp_BTL : swift.Replica.BeTheLeader.spec) :
    swift.rcvr.spec := by
  intro r γc γm
  rw [rpcCodec_spec_eq]
  iintro ⟨%Hnn, #Hcs, #Hpkg, #HR⟩
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
    (ptrIface swift.Replica.ty r) (withErr (sp.replicaRpcSpec γc γm) k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H1
    iapply swift.newArg_Ping γc γm r
    iframe Hcs Hpkg HR
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun k mm => net.rpc.methodOk swiftCodec
    (ptrIface swift.Replica.ty r) (withErr (sp.replicaRpcSpec γc γm) k) mm) ?_).2
  · rfl
  isplitr
  · iapply methodOk_of
    iframe H0
    iapply swift.newArg_BeTheLeader wp_BTL γc γm r
    iframe Hcs Hpkg HR
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
