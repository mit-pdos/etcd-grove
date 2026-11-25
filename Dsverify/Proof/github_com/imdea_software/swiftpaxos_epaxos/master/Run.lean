/-
`m.Run()` (`Master.Run.specM`) on the master `New` built: it sets up the lock (`masterLockInv`,
from the fresh fields and `listUnset`), registers the master on net/rpc's `DefaultServer`
(`rpc.Register`; on its error `Run` returns), `rpc.HandleHTTP()` (the master's address is the only
address the wildcard `":7501"` takes with a service in `rpcSS`: `srvServes` holds at every address
the listener takes), listens on `":7501"` (on an error `Run` returns), forks `run()` and serves
(`http.Serve(l, nil)`, which returns only on a listener error).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs
public import GooseLang.Ext.Net.Decide
public import Proof.fmt.SprintfPure
public import Perennial.Proof.fmt.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net



section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions] [RA : RpcHttpAddr GF] [RH : RpcHttpHyp GF]

/-- The wildcard `":7501"` takes no replica rpc address (their ports are 8502..8506). -/
theorem wild_not_replicaRpc (a : GoString) (ha : lisAccepts go!":7501" a)
    (hr : a ∈ replicaRpcAddrs) : False := by
  have hb := (lisAcceptsB_iff (la := go!":7501") (a := a)).mpr ha
  rw [replicaRpcAddrs_lit] at hr
  simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> revert hb <;> decide

/-- Every address the master's listener takes is served by the `DefaultServer` once the master is
registered as `"Master"`. -/
theorem master_srvServes (γ : EpNames) (W : net.rpc.RpcWorld GF) (γs : GName)
    (hW : W.SS = rpcSS γ) :
    net.rpc.svcReg γs epCodec go!"Master" (masterSvc γ) ⊢
      □ ∀ a, ⌜lisAccepts go!":7501" a⌝ → net.rpc.srvServes γs epCodec W a := by
  iintro #Hreg
  imodintro
  iintro %a %ha
  unfold net.rpc.srvServes
  imodintro
  iintro %svc %S %hS
  rw [hW] at hS
  rcases rpcSS_only γ _ _ _ hS with ⟨-, rfl, rfl⟩ | ⟨ha', -, -⟩
  · iframe Hreg
    iapply masterSvc_errOk
  · exact (wild_not_replicaRpc a ha ha').elim

/-- `lisInv_alloc` at the node's local state. -/
theorem lisInv_alloc_m (l : w64) (a : GoString) :
    netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ={⊤}=∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l a := by
  iintro H
  iapply (lisInv_alloc (Gg := hG.goose_globalGS) ⊤ _ l a true) $$ H

set_option goose.wp.extras true in
set_option maxHeartbeats 1600000 in
theorem Master.Run.wp_proof (hP : dlog.Logger.Printf.spec (GF := GF))
    (hF : dlog.Logger.Fatal.spec (GF := GF)) (hListen : net.Listen.spec (GF := GF) (hG := hG))
    (γ : EpNames) (W : net.rpc.RpcWorld GF)
    (hRcv : masterRcv.spec (GF := GF) γ (isMaster γ))
    (hRun : Master.run.specM (GF := GF) γ W) :
    Master.Run.specM (GF := GF) γ W := by
  intro m cfg logger
  wp_start as ⟨Hfresh, Hunset, %HW, #Hlis, #Hrpcs, Hmux, Hds0, Htok, #Hready, #Hsrv, #Hde, %Hbnd⟩
  unfold masterFresh
  icases Hfresh with ⟨%x, %c, Hm, %Hx, Hnl, Hnlc, Hal, Halc, Hpl, Hplc, Hnds, Hld, Halv, Hlat, Hmu,
    #Hcond, #Hlog, #Hcfg, %Hleader⟩
  ihave %Hmnn := typedPointsto_not_null _ _ _ $$ Hm
  obtain ⟨hlogger, hN, hport, hcfg, hfi, hnext, hnlc, halc, hplc⟩ := Hx
  icases (ownSlice_halves _ _).1 $$ Halv with ⟨Halv, Halv2⟩
  iStructNamed Hm
  rw [hlogger, hN, hport, hcfg, hfi, hnext] at *
  ipersist Logger
  ipersist N
  ipersist lock
  ipersist initCond
  ipersist config
  ipersist leader
  ipersist alive
  ipersist latencies
  imod sync.init_Mutex (masterLockInv γ m) ⊤ x.lock' $$ Hmu
    [nodeList Hnl Hnlc addrList Hal Halc portList Hpl Hplc Hunset Hld Halv Hlat finishInit] with #Hmutex
  · inext
    unfold masterLockInv masterLists
    iexists [], x.nodeList', x.addrList', x.portList', x.leader', x.alive', x.latencies',
      List.replicate 5 false, List.replicate 5 false, List.replicate 5 (W64 0), false
    simp only [List.length_nil, List.map_nil, Nat.zero_lt_succ, ↓reduceIte]
    iframe
    iframe leader alive latencies
    ipureintro
    refine ⟨List.nodup_nil, by simp, by word, by word, by word, by simp, by simp, by simp⟩
  ihave #HisM : isMaster γ m $$ []
  · unfold isMaster
    iframe Hpkg
    iexists x.lock', cfg, logger, x.initCond', c
    iframe lock Hmutex initCond Hcond N config Hcfg Logger Hlog
    ipureintro; exact Hleader
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hrpcpkg : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · unfold rpcReady; icases Hready with ⟨#H, -⟩; iexact H
  ihave #Hcodec : net.rpc.codecSet (GF := GF) epCodec $$ []
  · unfold rpcReady; icases Hready with ⟨-, #H⟩; iexact H
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #(W64 7501)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl1 ⟨-, -⟩
  wp_auto
  wp_apply (wp_Master_Printf hP) $$ [$Logger $Hlog]
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #(W64 5)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl2 ⟨-, -⟩
  wp_auto
  wp_apply (wp_Master_Printf hP) $$ [$Logger $Hlog]
  unfold defaultSrvFresh
  icases Hds0 with ⟨%γs, %γf, #Hds, Hsown⟩
  ihave Hrcvm := hRcv m $$ []
  · iframe HisM Hcodec; ipureintro; exact Hmnn
  wp_apply (RH.Register_spec γs γf ∅ epCodec (ptrIface master.Master.ty m) (masterSvc γ)
    go!"Master" (W8 77) go!"aster" rfl (by decide)) $$ [$Hds $Hsown $Hcodec $Hrcvm]
    as %err ⟨%Herr, #Hsvc, -⟩
  · ipureintro; simp [GMap.mem_iff]
  subst Herr
  wp_auto
  ihave #Hserves0 := master_srvServes γ W γs HW $$ Hsvc
  ihave #Hserves : □ ∀ a, ⌜addrOk a = true ∧ lisAccepts go!":7501" a⌝ →
      net.rpc.srvServes γs epCodec W a ∗ ⌜W.hs a ≠ [] ∧ W.hsAns a = net.rpc.connectAns⌝ $$ []
  · iintro !> %a %Ha
    isplitr
    · iapply Hserves0; ipureintro; exact Ha.2
    · iapply rpcLisP_hs W go!":7501" a Ha $$ Hlis
  ihave #Hdsa := net.rpc.defaultServerO_any γs γf $$ Hds
  ihave #Hde' := Hde
  iunfold dialEnv at Hde'
  icases Hde' with ⟨#Hhe, #Hcon⟩
  wp_apply (RH.HandleHTTP_spec γs epCodec W (fun a => addrOk a = true ∧ lisAccepts go!":7501" a)
      [] (by simp) (by simp))
    $$ [$Hpkg2 $Hmux $Hdsa $Hserves $Hsrv $Hcodec $Hcon] as ⟨Hmux, #Hmh⟩
  · ipureintro; exact Hbnd.1
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #(W64 7501)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl3 ⟨Hsl3, -⟩
  wp_auto
  wp_apply _root_.Perennial.EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!":%d"
      [.lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      _ _ _ _ (by fmt_encode) (by fmt_fits) (.int _ _ _ _ (.int _)
      .nil) $$ [$Hfmt $Hsl3] as %addr ⟨-, %Haddr⟩
  have haddr := sprintf_colon_int _ _ Haddr
  have h7501 : go!":" ++ fmt.decimal (sint.Z (W64 7501)) = go!":7501" := by
    rw [show sint.Z (W64 7501) = 7501 by rfl]
    simp [fmt.decimal, fmt.decimalNat_of_ge, fmt.decimalNat_of_lt, fmt.digitByte]
  rw [h7501] at haddr
  subst haddr
  wp_apply (hListen go!"tcp" net.tcpNet_tcp go!":7501") $$ [] as %li %err Hres
  · isplitr
    · ipureintro; decide
    iapply RpcHttpAddr.rpcLisP_lis; iexact Hlis
  icases Hres with (⟨%He, %l, #Hli, Hnl, #Hlon⟩ | ⟨%xa, -, #HE⟩)
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl4 ⟨-, -⟩
    wp_auto
    wp_apply (wp_Master_Fatal hF) $$ [$Logger $Hlog]
    iapply HΦ; itrivial
  subst He
  wp_auto
  ihave #Hcenv : net.rpc.cliEnv (GF := GF) $$ []
  · unfold net.rpc.srvEnv; icases Hsrv with ⟨#H, -⟩; iexact H
  wp_apply wp_fork $$ [Hnds nodes nextLeader Halv2]
  · wp_apply hRun m $$ [Hnds nodes nextLeader Halv2]
    · iframe HisM
      unfold runRes
      iexists x.nodes', x.alive'
      iframe
      iframe alive Hrpcs Hready Hcenv Hde
      ipureintro; exact ⟨HW, Hbnd.2⟩
    itrivial
  imod lisInv_alloc_m l go!":7501" $$ Hnl with #Hlinv
  ihave #Hlisn := RpcHttpAddr.rpcLisP_net W go!":7501" _ _ $$ Hlis
  wp_apply (RH.Serve_spec W go!":7501" net.rpc.defaultRPCPath li l
      net.rpc.litPattern_rpc net.rpc.defaultRPCPath_short)
    $$ [$Hpkg2 $Hhe $Hlisn $Hmh $Hli $Hlon $Hlinv $Htok] as %e -
  · ipureintro; exact Hbnd.1
  iapply HΦ; itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
