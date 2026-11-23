/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Run.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.Run()` (the frozen spec `Spec/master/Master__Run.lean`), proved from the master's full
creation (`master.createdFull`) and the specs of `run` and of the receiver (`rcvrOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Master__Run
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NameOkFor
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitLike

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions]

/-- The receiver `m` meets the master's service spec through the kit's dispatch, once the
master's persistent facts hold (`Proof/master/Rcvr.lean`). -/
abbrev master.rcvr.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat),
  master.isMaster m γc γm N ⊢
    net.rpc.rcvrOk (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
      (sp.masterSpec γc γm)

end spec

/-! The specs below are over a codec `C` (decision D6, Proof/swiftnet/KitLike.lean): at
`kitCodec` for the frozen statement, at `kitCodecC` for the link. -/

section specC
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF]

/-- `m.run()` (the goroutine): waits for the replicas, dials them, makes the first leader, pings
them forever. It owns `nodes`' contents and `nextLeader`. -/
abbrev master.Master.run.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF) (nodesS : GoSlice)
    (nl : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ master.fld m go!"nodes" ↦□ nodesS ∗
      nodesS ↦* List.replicate N null ∗ master.fld m go!"nextLeader" ↦ nl ∗
      ([∗list] a ∈ replicaRpcAddrs, net.rpc.rpcAddr W a) ∗
      ⌜(∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)) ∧
        nl = W64 (-1)⌝ ∗
      net.rpc.codecSet ∗ net.rpc.kitCodecOk }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"run")) (Val #()))
  {{ RET #(); False }}

/-- `Run` from `master.createdFull`. -/
abbrev master.Master.Run.specFull : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.createdFull m γc γm N (W64 7001) ∗ addrTok masterAddr ∗ nodeIp go!"10.77.0.17" ∗
      net.http.muxOwner [] ∗
      ([∗list] a ∈ rpcAddrs, net.rpc.rpcAddr W a) ∗
      ⌜(∀ svc, W.SS masterAddr svc =
          if svc = go!"Master" then some (sp.masterSpec γc γm) else none) ∧
        ∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)⌝ ∗
      net.rpc.codecSet ∗ net.rpc.kitCodecOk }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); False }}

/-- The frozen `Run.spec` without `kitNameOk` (false for the kit's `rpcName` on an unlisted
receiver, the codec group's HUB-REQUEST 1): the registration uses `nameOkFor` at the master
(`kitNameOkFor_master`). The link uses this one. -/
abbrev master.Master.Run.spec' : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.created m γc γm N (W64 7001) ∗ addrTok masterAddr ∗ nodeIp go!"10.77.0.17" ∗
      net.http.muxOwner [] ∗
      ([∗list] a ∈ rpcAddrs, net.rpc.rpcAddr W a) ∗
      ⌜(∀ svc, W.SS masterAddr svc =
          if svc = go!"Master" then some (sp.masterSpec γc γm) else none) ∧
        ∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)⌝ ∗
      net.rpc.codecSet ∗ net.rpc.kitCodecOk }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); False }}

end specC

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.FieldAssumptions]
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

set_option maxHeartbeats 4000000 in
theorem master.Master.Run.wp_proof_full
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_run : master.Master.run.spec) (rcvr_ok : master.rcvr.spec) :
    master.Master.Run.specFull := fun m γc γm N W => by
  wp_start as ⟨Hcr, Htok, %Hip, Hmux, Haddrs, %HSS, #Hcs, #Hko⟩
  unfold master.createdFull master.createdBody
  icases Hcr with ⟨%v, %c, %fr, Hm, #Hq, #Hc, Hauth, Hnl, Hal, Hpl, Hcnl, Hcal, Hcpl, Hnodes,
    Hleaders, Halives, Hlats, #Hplain, Hlk, #Hcd, %Hp⟩
  ihave %Hv := confIs_valid γc c $$ Hc
  have hN5 : N ≤ 5 := by rcases Hv.1 with h | h <;> omega
  have hN3 : 3 ≤ N := by rcases Hv.1 with h | h <;> omega
  icases typedPointsto_split _ _ _ $$ Hm with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨Logger, N, port, nodeList, addrList, portList, lock, nodes, leader, alive,
    latencies, finishInit, initCond, nextLeader, config, -⟩
  imod sync.init_Mutex (master.lockInv m γm N v.leader' v.alive' v.latencies') ⊤ v.lock' $$ Hlk
    [nodeList addrList portList Hnl Hal Hpl Hcnl Hcal Hcpl Hauth Hleaders Halives Hlats finishInit]
    with #Hmu
  · inext
    unfold master.lockInv
    iexists v.nodeList', v.addrList', v.portList', [], [], [], List.replicate N false,
      List.replicate N false, List.replicate N (W64 0), false
    unfold master.lists
    rw [if_neg (by simp; omega)]
    rw [Hp.2.2.2.1]
    simp only [named]
    iframe
    ipureintro
    refine ⟨⟨Hp.2.2.2.2.2.1, Hp.2.2.2.2.2.2.1, Hp.2.2.2.2.2.2.2.1⟩, ?_, ?_⟩
    · refine ⟨rfl, rfl, by simp, rfl, List.nodup_nil, by simp⟩
    · simp
  ipersist Logger
  ipersist N
  ipersist port
  ipersist lock
  ipersist nodes
  ipersist leader
  ipersist alive
  ipersist latencies
  ipersist initCond
  ipersist config
  ihave #HisM : master.isMaster m γc γm N $$ []
  · unfold master.isMaster
    iexists v.Logger', v.lock', v.initCond', v.config', v.nodes', v.leader', v.alive',
      v.latencies', c, fr
    rw [Hp.2.1]
    simp only [named]
    iframe Logger N lock initCond nodes leader alive latencies config Hq Hplain Hc Hmu Hcd Hpkg
    ipureintro; exact ⟨Hp.1, hN5⟩
  rw [Hp.2.1, Hp.2.2.1]
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #(W64 7001)]
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨-, -⟩
  wp_auto
  wp_apply master.wp_Printf wp_Printf $$ [$Logger $Hq]
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #(W64 N)]
  isplitr
  · ipureintro; rfl
  iintro %s2 ⟨-, -⟩
  wp_auto
  wp_apply master.wp_Printf wp_Printf $$ [$Logger $Hq]
  ipersist master
  ihave #Hkn : net.rpc.nameOkFor (GF := netDistGF) (net.rpc.kitFn go!"rpcName")
      (interface.mkOk (go.GoType.PointerType master.Master.ty) #m) $$ []
  · iapply kitNameOkFor_master
  wp_apply net.rpc.Register.wp_proof' (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
    $$ [$Hcs $Hko $Hkn] as %rerr Hreg
  · iapply methods_of C
    unfold net.rpc.RpcCodec.methods kitCodec
    ipureintro; exact ⟨m, Or.inl rfl⟩
  icases Hreg with (⟨%Hrerr, #Hreg⟩ | %Hrerr)
  rotate_left
  · -- the registration failed (unreachable in Go; the harness's model allows it): the
    -- fork's workaround blocks
    rcases rerr with ei | _
    · try wp_auto
      wp_apply wp_slice_literal (V := GoInterface)
        [interface.mkOk go.string #(go!"master register error:"), interface.ok ei]
      isplitr
      · ipureintro; rfl
      iintro %s6 ⟨-, -⟩
      wp_auto
      wp_apply master.wp_Fatal wp_Fatal $$ [$Logger $Hq]
      wp_for
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · exact absurd rfl Hrerr
  have hname : net.rpc.RpcNames.name (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
      = go!"Master" := by
    simp only [net.rpc.RpcNames.name]
    rw [if_pos ⟨m, rfl⟩]
  rw [hname]
  subst Hrerr
  try wp_auto
  wp_apply net.rpc.HandleHTTP.wp_proof [] $$ [Hmux] as ⟨-, %srv, #Hsrv, #Hroute⟩
  · iframe; ipureintro; simp
  have hdec : decimal 7001 = go!"7001" := by simp [decimal, decimalNat_eq, digitByte]
  have hport : go!":" ++ decimal (sint.Z (W64 7001)) = ([] : GoString) ++ go!":" ++ go!"7001" := by
    rw [show sint.Z (W64 7001) = (7001 : Int) from rfl, hdec]; rfl
  have hmaddr : masterAddr = go!"10.77.0.17" ++ go!":" ++ go!"7001" := rfl
  have hwild : ([] : GoString) ∈ wildcardHosts := by simp [wildcardHosts]
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #(W64 7001)]
  isplitr
  · ipureintro; rfl
  iintro %s3 ⟨Hs3, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf _ _ _ _ (ArgsWf.cons_int _ _ _ (IntArgValue.int (W64 7001)) ArgsWf.nil)
    $$ [$Hs3] as %str ⟨-, %Hstr⟩
  rw [master.sprintf_colon_d _ _ Hstr, hport]
  rw [hmaddr]
  wp_apply net.ListenWild.wp_proof go!"10.77.0.17" [] go!"7001" hwild $$ [Htok] as %lv %lerr ⟨Htok, Hl⟩
  · iframe; ipureintro; exact Hip
  -- the retry loop: listen until it succeeds
  ihave HI : (∃ (lv lerr : GoInterface), l_ptr ↦ lv ∗ err_ptr ↦ lerr ∗
      addrTok (go!"10.77.0.17" ++ go!":" ++ go!"7001") ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            lerr = interface.nil⌝ ∗ net.ownListener l lid (go!"10.77.0.17" ++ go!":" ++ go!"7001")) ∨
       (∃ i, ⌜lv = interface.nil ∧ lerr = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code lerr)) : IProp netDistGF)
    $$ [l err Htok Hl]
  · iexists lv, lerr
    iframe
  wp_for
  icases HI with ⟨%lv', %lerr', l, err, Htok, Hl⟩
  icases Hl with (⟨%l0, %lid, %Hlv, Hl⟩ | ⟨%i, %Hlv, Herr⟩)
  · obtain ⟨rfl, rfl⟩ := Hlv
    wp_auto
    wp_if_destruct
    · exact absurd (go.intoVal_inj Hif) (by decide)
    · -- listening: the run goroutine, then serve
      try simp only [_root_.decide_true, ↓reduceIte]
      try wp_auto
      rw [show rpcAddrs = masterAddr :: replicaRpcAddrs from rfl]
      icases BigSepL.bigSepL_cons.1 $$ Haddrs with ⟨Hma, Hra⟩
      wp_apply wp_fork $$ [Hnodes nextLeader Hra]
      · wp_apply wp_run m γc γm N W v.nodes' v.nextLeader' $$ [$HisM $nodes $Hnodes $nextLeader $Hra
          $Hcs $Hko]
        · ipureintro; exact ⟨HSS.2, Hp.2.2.2.2.1⟩
        iintro %Hf; exact Hf.elim
      -- the master's service, registered
      ihave #Hok := rcvr_ok m γc γm N $$ HisM
      ihave #Hok := rcvrOk_of C _ _ $$ Hok
      ihave #Hds := net.rpc.defaultServes_intro W masterAddr $$ []
      · isplitr
        · iPkgInit
        imodintro
        iintro %svc %S %HS
        by_cases hsvc : svc = go!"Master"
        · subst hsvc
          rw [HSS.1, if_pos rfl] at HS
          cases HS
          iexists (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
          iframe Hreg Hok
        · -- no other service at the master's address (change log C7)
          rw [HSS.1, if_neg hsvc] at HS
          cases HS
      rw [← hmaddr]
      icases net.rpc.rpc_Serve_pre W masterAddr srv l0 lid $$ [Hl Hma] with
        ⟨#Hhttp, Hl, #Hpr, #Hr, #Hh, %Hwfp⟩
      · iframe Hl Hma Hds Hcs Hko Hsrv Hroute
        iPkgInit
      wp_apply net.http.Serve.wp_proof l0 lid masterAddr _ _ _ _ $$ [$Hhttp $Hl $Hpr $Hr $Hh]
      · ipureintro; exact Hwfp
      iintro %err %Hf
      exact Hf.elim
  · obtain ⟨rfl, rfl⟩ := Hlv
    wp_auto
    wp_if_destruct
    · try simp only [_root_.decide_true, ↓reduceIte]
      try wp_auto
      wp_apply wp_slice_literal (V := GoInterface)
        [interface.mkOk go.string #(go!"master listen error:"), interface.ok i]
      isplitr
      · ipureintro; rfl
      iintro %s4 ⟨-, -⟩
      wp_auto
      wp_apply master.wp_Fatal wp_Fatal $$ [$Logger $Hq]
      wp_apply time.wp_Sleep
      wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #(W64 7001)]
      isplitr
      · ipureintro; rfl
      iintro %s5 ⟨Hs5, -⟩
      wp_auto
      wp_apply fmt.wp_Sprintf _ _ _ _ (ArgsWf.cons_int _ _ _ (IntArgValue.int (W64 7001))
        ArgsWf.nil) $$ [$Hs5] as %str' ⟨-, %Hstr'⟩
      rw [master.sprintf_colon_d _ _ Hstr', hport]
      wp_apply net.ListenWild.wp_proof go!"10.77.0.17" [] go!"7001" hwild $$ [Htok]
        as %lv2 %lerr2 ⟨Htok, Hl⟩
      · iframe; ipureintro; exact Hip
      wp_for_post
      iframe
      iexists lv2, lerr2
      iframe
    · exact absurd rfl Hif

/-- `Run.spec'` (no `kitNameOk`), through `master.created_full` (HUB-REQUEST 1). -/
theorem master.Master.Run.wp_proof'
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_run : master.Master.run.spec) (rcvr_ok : master.rcvr.spec) :
    master.Master.Run.spec' := fun m γc γm N W => by
  iintro %Φ ⟨#Hpkg, Hcr, Hrest⟩ HΦ
  iapply master.Master.Run.wp_proof_full wp_Printf wp_Fatal wp_run rcvr_ok m γc γm N W $$
    [Hcr Hrest] HΦ
  iframe Hpkg Hrest
  iapply master.created_full $$ Hcr

end proof

section frozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.FieldAssumptions]

/-- The frozen spec (`Spec/master/Master__Run.lean`): `Run.spec'`, `kitNameOk` unused. -/
theorem master.Master.Run.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_run : master.Master.run.spec) (rcvr_ok : master.rcvr.spec) :
    master.Master.Run.spec := fun m γc γm N W => by
  iintro %Φ ⟨#Hpkg, Hcr, Htok, Hip, Hmux, Haddrs, HSS, #Hcs, #Hko, -⟩ HΦ
  iapply master.Master.Run.wp_proof' wp_Printf wp_Fatal wp_run rcvr_ok m γc γm N W $$
    [Hcr Htok Hip Hmux Haddrs HSS] HΦ
  iframe
  iframe Hpkg Hcs Hko

end frozen

end Perennial.github_com.imdea_software.swiftpaxos
