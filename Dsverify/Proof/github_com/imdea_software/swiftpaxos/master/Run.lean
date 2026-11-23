/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Run.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.Run()` (the spec `Spec/master/Master__Run.lean`), proved from the master's full creation
(`master.createdFull`), the specs of `run` and of the receiver (`master.rcvr.spec`: what
`rpc.Register` asks of the codec's `Receiver` for `*Master`), over net/rpc's HTTP path
(`RpcHttpHyp`: `Register_spec`, `HandleHTTP_spec`, `Serve_spec`) and `Net/`'s wildcard `Listen`
(`net.Listen.labProof` over the `lisProto` that `rpcLisP` gives).
-/
module

public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetLab
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Master__Run

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [H : RpcHttpHyp netDistGF]

/-- `rpc.Register`'s obligation on the codec's `Receiver` for the master `m`, once the master's
persistent facts hold: it returns a `*Receiver` serving `withErr masterSpec` under the name
`"Master"` (`Net/`'s `rcvrIs`). To be proved of the kit's rpcgen codec (`master/Rcvr.lean`). -/
abbrev master.rcvr.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat),
  master.isMaster m γc γm N ⊢
    net.rpc.RpcCodec.spec.rcv (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
      (net.rpc.rcvrIs net.rpc.RpcCodec.spec
        (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
        (withErr (sp.masterSpec γc γm)) go!"Master" false)

/-- `m.run()` (the goroutine): waits for the replicas, dials them (over HTTP), makes the first
leader, pings them forever. It owns `nodes`' contents and `nextLeader`. -/
abbrev master.Master.run.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF) (nodesS : GoSlice)
    (nl : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ master.fld m go!"nodes" ↦□ nodesS ∗
      nodesS ↦* List.replicate N null ∗ master.fld m go!"nextLeader" ↦ nl ∗
      ([∗list] a ∈ replicaRpcAddrs, rpcHttp W a) ∗
      ⌜(∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)) ∧
        nl = W64 (-1)⌝ ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"run")) (Val #()))
  {{ RET #(); False }}

/-- `Run` from `master.createdFull`. -/
abbrev master.Master.Run.specFull : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.createdFull m γc γm N (W64 7001) ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net.http ∗
      ⌜threadBound netDistGF ≤ 2 ^ 31⌝ ∗ net.rpc.srvEnv ∗
      H.rpcLisP W go!":7001" (connectReq defaultRPCPath) connectAns ∗
      ([∗list] a ∈ replicaRpcAddrs, rpcHttp W a) ∗ ⌜master.worldOk γc γm W⌝ ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [net.Assumptions]
variable [H : RpcHttpHyp netDistGF]

set_option maxHeartbeats 4000000 in
theorem master.Master.Run.wp_proof_full
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_run : master.Master.run.spec) (rcvr_ok : master.rcvr.spec) :
    master.Master.Run.specFull := fun m γc γm N W => by
  wp_start as ⟨Hcr, #Hrpc, #Hhttp, %Hthr, #Henv, #Hlp, Haddrs, %HSS, #Hcs⟩
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
  -- rpc.Register(master), on DefaultServer
  ihave #Hds0 := H.defaultServer_init $$ Hrpc
  icases Hds0 with ⟨%γs, #Hds⟩
  ihave Hrc := rcvr_ok m γc γm N $$ HisM
  wp_apply H.Register_spec γs net.rpc.RpcCodec.spec
    (interface.mkOk (go.GoType.PointerType master.Master.ty) #m) (withErr (sp.masterSpec γc γm))
    go!"Master" (W8 77) go!"aster" rfl ⟨by decide, by decide⟩ $$ [$Hrpc $Hds $Hcs $Hrc]
    as %rerr Hreg
  icases Hreg with (⟨%Hrerr, #Hreg⟩ | %Hrerr)
  rotate_left
  · -- the registration failed (not in Go; the spec allows it): the fork's workaround blocks
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
  subst Hrerr
  try wp_auto
  -- rpc.HandleHTTP(): every address the wildcard takes serves the master's service
  ihave #Hsrv : □ ∀ a, ⌜lisAccepts go!":7001" a⌝ →
      net.rpc.srvServes γs net.rpc.RpcCodec.spec W a $$ []
  · iintro !> %a %Ha
    unfold net.rpc.srvServes
    iintro !> %svc %S %HS
    rw [HSS.1 a svc Ha] at HS
    by_cases hsvc : svc = go!"Master"
    · subst hsvc
      rw [if_pos rfl] at HS
      cases HS
      iframe Hreg
      iapply withErr_errOk
    · rw [if_neg hsvc] at HS
      cases HS
  wp_apply H.HandleHTTP_spec γs net.rpc.RpcCodec.spec W (lisAccepts go!":7001")
    $$ [$Hrpc $Hds $Hsrv $Henv $Hcs] as #Hmux
  · ipureintro; exact Hthr
  have hdec : decimal 7001 = go!"7001" := by simp [decimal, decimalNat_eq, digitByte]
  have hport : go!":" ++ decimal (sint.Z (W64 7001)) = go!":7001" := by
    rw [show sint.Z (W64 7001) = (7001 : Int) from rfl, hdec]; rfl
  ihave #Hlis := H.rpcLisP_lis W go!":7001" _ _ $$ Hlp
  icases Hlis with ⟨%P, %Q, #Hlis⟩
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #(W64 7001)]
  isplitr
  · ipureintro; rfl
  iintro %s3 ⟨Hs3, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (ArgsWf.cons_int _ _ _ (IntArgValue.int (W64 7001)) ArgsWf.nil)
    $$ [$Hs3] as %str ⟨-, %Hstr⟩
  rw [master.sprintf_colon_d _ _ Hstr, hport]
  wp_apply net.Listen.labProof go!":7001" P Q $$ Hlis as %lv %lerr Hl
  -- the retry loop: listen until it succeeds
  ihave HI : (∃ (lv lerr : GoInterface), l_ptr ↦ lv ∗ err_ptr ↦ lerr ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            lerr = interface.nil⌝ ∗ net.ownListener l lid go!":7001") ∨
       (∃ i, ⌜lerr = interface.ok i⌝)) : IProp netDistGF)
    $$ [l err Hl]
  · iexists lv, lerr
    iframe
  wp_for
  icases HI with ⟨%lv', %lerr', l, err, Hl⟩
  icases Hl with (⟨%l0, %lid, %Hlv, #Hl⟩ | ⟨%i, %Hlv⟩)
  · obtain ⟨rfl, rfl⟩ := Hlv
    wp_auto
    wp_if_destruct
    · exact absurd (go.intoVal_inj Hif) (by decide)
    · -- listening: the run goroutine, then serve
      try simp only [_root_.decide_true, ↓reduceIte]
      try wp_auto
      wp_apply wp_fork $$ [Hnodes nextLeader Haddrs]
      · wp_apply wp_run m γc γm N W v.nodes' v.nextLeader' $$ [$HisM $nodes $Hnodes $nextLeader
          $Haddrs $Hcs]
        · ipureintro; exact ⟨HSS.2, Hp.2.2.2.2.1⟩
        iintro %Hf; exact Hf.elim
      iunfold net.ownListener at Hl
      icases Hl with ⟨%x, #Hat, #Hon, #Hinv⟩
      wp_apply H.Serve_spec W go!":7001" defaultRPCPath _ lid $$ [$Hhttp $Hlp $Hmux $Hon $Hinv]
      · isplitr
        · ipureintro; exact Hthr
        unfold net.isListener
        iexists l0, x
        iframe Hat
        ipureintro; rfl
      iintro %err -
      wp_auto
      iapply HΦ
      itrivial
  · obtain rfl := Hlv
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
      wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (ArgsWf.cons_int _ _ _ (IntArgValue.int (W64 7001))
        ArgsWf.nil) $$ [$Hs5] as %str' ⟨-, %Hstr'⟩
      rw [master.sprintf_colon_d _ _ Hstr', hport]
      wp_apply net.Listen.labProof go!":7001" P Q $$ Hlis as %lv2 %lerr2 Hl
      wp_for_post
      iframe
      iexists lv2, lerr2
      iframe
    · exact absurd rfl Hif

end proof

section frozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [net.Assumptions]
variable [H : RpcHttpHyp netDistGF]

/-- The spec (`Spec/master/Master__Run.lean`), through `master.created_full`. -/
theorem master.Master.Run.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_run : master.Master.run.spec) (rcvr_ok : master.rcvr.spec) :
    master.Master.Run.spec := fun m γc γm N W => by
  iintro %Φ ⟨#Hpkg, Hcr, Hrest⟩ HΦ
  iapply master.Master.Run.wp_proof_full wp_Printf wp_Fatal wp_run rcvr_ok m γc γm N W $$
    [Hcr Hrest] HΦ
  iframe Hpkg Hrest
  iapply master.created_full $$ Hcr

end frozen

end Perennial.github_com.imdea_software.swiftpaxos
