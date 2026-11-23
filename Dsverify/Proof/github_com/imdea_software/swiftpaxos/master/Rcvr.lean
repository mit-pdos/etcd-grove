/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Rcvr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The master's receiver meets `sp.masterSpec` through the kit's dispatch (`master.rcvr.spec`,
`Proof/master/Run.lean`), over the master's method specs and the specs of the kit's codec
functions it calls (`rpc_gen.go`: decoding the arguments, encoding the replies). The latter are
the codec group's (`examples/swiftnet`): hypotheses, stated in `Spec/swiftnet/CodecFns.lean`
(change log C7, request 6), not unfolded.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Register
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Methods
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Run
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.CodecFns

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem master.enc_registerReply (i : w64) (ns : List GoString) (r l : Bool) :
    (sp.KitVal.registerReply i ns r l).encode =
      sp.cU64 (W64 2) ++ (sp.cU64 i ++ sp.cList sp.cBytes ns ++ sp.cBool r ++ sp.cBool l) := rfl

theorem master.enc_getReplicaListReply (rs : List GoString) (al : List Bool) (r : Bool) :
    (sp.KitVal.getReplicaListReply rs al r).encode =
      sp.cU64 (W64 6) ++ (sp.cList sp.cBytes rs ++ sp.cList sp.cBool al ++ sp.cBool r) := rfl

theorem master.enc_getLeaderReply (i : w64) :
    (sp.KitVal.getLeaderReply i).encode = sp.cU64 (W64 4) ++ sp.cU64 i := rfl

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.model.Assumptions]

set_option maxHeartbeats 4000000 in
theorem master.rcvr.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_decRA : examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.spec) (wp_decGRL : examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.spec)
    (wp_decGL : examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.spec) (wp_put : examples.swiftnet.rpcPutU64.specNil)
    (wp_encRR : examples.swiftnet.rpcEnc_defs_RegisterReply.spec)
    (wp_encGRL : examples.swiftnet.rpcEnc_defs_GetReplicaListReply.spec)
    (wp_encGL : examples.swiftnet.rpcEnc_defs_GetLeaderReply.spec) :
    master.rcvr.spec := by
  intro m γc γm N
  iintro #Hm
  ihave #Hpm := master.isMaster_pkg m γc γm N $$ Hm
  unfold net.rpc.rcvrOk
  imodintro
  iintro %meth %args %Φ HS
  unfold net.rpc.RpcCodec.call kitCodec
  simp only
  iintro %s %dq Hs
  have hfn : net.rpc.kitFn go!"rpcCall" = functions examples.swiftnet.rpcCall [] := rfl
  rw [hfn]
  wp_func_call
  wp_call
  wp_auto
  wp_if_destruct
  · -- Register
    ihave HS := (sp.masterSpec_register (γc := γc) (γm := γm) args Φ).1 $$ HS
    icases HS with ⟨%ip, %port, %c, %k, %Hargs, #Hc, HΦ⟩
    obtain ⟨rfl, Hk⟩ := Hargs
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_decRA $$ [$Hs] as Hs
    wp_apply master.Master.Register.wp_proof wp_Printf m γc γm N _ _ ip port c k _
      $$ [$Hm $a $«$r0» $Hc] as ⟨%rv', Hrep, Hready⟩
    · ipureintro; exact Hk
    wp_apply wp_put as %b ⟨Hb, Hcb⟩
    obtain ⟨id, nlS, ready, isL⟩ := rv'
    cases ready
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hready with %Hrv
      simp only [replica.defs.RegisterReply.mk.injEq] at Hrv
      obtain ⟨rfl, rfl, -, rfl⟩ := Hrv
      ihave Hnil := ownSlice_nil (V := GoString) (GF := netDistGF) (DFrac.own 1)
      wp_apply wp_encRR b _ _ [] (DFrac.own 1) $$ [$Hb $Hcb Hnil] as %b' ⟨Hb', Hcb', -⟩
      · iexact Hnil
      simp only [master.enc_registerReply]
      iexists b', _, [], true
      isplitr
      · ipureintro; rfl
      isplitl [Hb']
      · iexact Hb'
      isplitr
      · ipureintro; rfl
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    · simp only [↓reduceIte]
      icases Hready with ⟨%nodes, #Hnodes, #Hcfg, %Hid⟩
      wp_apply wp_encRR b _ _ nodes DFrac.discard $$ [$Hb $Hcb] as %b' ⟨Hb', Hcb', -⟩
      · iexact Hnodes
      simp only [master.enc_registerReply]
      iexists b', _, [], true
      isplitr
      · ipureintro; rfl
      isplitl [Hb']
      · iexact Hb'
      isplitr
      · ipureintro; rfl
      iapply HΦ
      simp only [↓reduceIte]
      icases Hcfg with ⟨%fr, #Hcfg⟩
      iexists fr
      iframe Hcfg
      ipureintro; exact Hid
    done
  wp_if_destruct
  · -- GetLeader
    ihave HS := (sp.masterSpec_getLeader (γc := γc) (γm := γm) args Φ).1 $$ HS
    icases HS with ⟨%Hargs, HΦ⟩
    subst Hargs
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_decGL $$ [$Hs] as Hs
    wp_apply master.Master.GetLeader.wp_proof m γc γm N _ _ _ $$ [$Hm $«$r0»] as ⟨%id, Hrep⟩
    wp_apply wp_put as %b ⟨Hb, Hcb⟩
    wp_apply wp_encGL $$ [$Hb $Hcb] as %b' ⟨Hb', Hcb'⟩
    simp only [master.enc_getLeaderReply]
    iexists b', _, [], true
    isplitr
    · ipureintro; rfl
    isplitl [Hb']
    · iexact Hb'
    isplitr
    · ipureintro; rfl
    iapply HΦ
  wp_if_destruct
  · -- GetReplicaList
    ihave HS := (sp.masterSpec_getReplicaList (γc := γc) (γm := γm) args Φ).1 $$ HS
    icases HS with ⟨%Hargs, HΦ⟩
    subst Hargs
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_decGRL $$ [$Hs] as Hs
    wp_apply master.Master.GetReplicaList.wp_proof wp_Printf m γc γm N _ _ _ $$ [$Hm $«$r0»]
      as ⟨%s1, %s2, %nodes, %alive, Hrep, Hs1, Hs2, #Hcfg, %Hal⟩
    wp_apply wp_put as %b ⟨Hb, Hcb⟩
    wp_apply wp_encGRL b _ _ nodes alive (DFrac.own 1) (DFrac.own 1) $$ [$Hb $Hcb Hs1 Hs2]
      as %b' ⟨Hb', Hcb', -⟩
    · isplitl [Hs1]
      · iexact Hs1
      iexact Hs2
    simp only [master.enc_getReplicaListReply]
    iexists b', _, [], true
    isplitr
    · ipureintro; rfl
    isplitl [Hb']
    · iexact Hb'
    isplitr
    · ipureintro; rfl
    iapply HΦ $$ Hcfg
    ipureintro; exact Hal
  -- another method: excluded by the spec
  iexfalso
  iapply sp.masterSpec_other (γc := γc) (γm := γm) meth args Φ ⟨by assumption, by assumption,
    by assumption⟩ $$ HS

end proof

end Perennial.github_com.imdea_software.swiftpaxos
