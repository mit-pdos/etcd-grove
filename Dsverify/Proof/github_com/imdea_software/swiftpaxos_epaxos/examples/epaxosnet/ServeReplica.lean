/-
`serve(k, sl, 7500)`'s proof for replica node `k` (`ServeDefs.lean`'s `serveReplica.spec`; the
lab's `wp_serve_replica`): `Register()` (the kit's codec), `nodeConfig`, `host` of the server
address, `register` with the master (node `k`'s token for replica id `i`'s token and start
resources), `epaxos.New` (the replica handle), `rpc.Register(rep)` (`replicaRcv.spec`: the
`"Replica"` service on `DefaultServer`), `rpc.HandleHTTP()` (`DefaultServeMux` routes the rpc path
to it at `rpcAddrOf k`, the one address of `W` it serves, whose only service is `"Replica"`:
`rpcSS_only`), `net.Listen` at `ip + ":" + itoa(port + 1000)` = `rpcAddrOf k` (the right to
listen from `rpcLisP`'s `lisProto`), `http.Serve`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServeDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true in
theorem serveReplica.wp_proof [RpcHttpAddr GF] [RpcHttpHyp GF]
    (isRep : EpNames → Nat → Loc → IProp GF)
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_nodeConfig : nodeConfig.spec (GF := GF) (hG := hG))
    (wp_host : host.spec (GF := GF) (hG := hG))
    (wp_itoa : itoa.spec (GF := GF) (hG := hG))
    (wp_register : register.spec (GF := GF) (hG := hG))
    (wp_New : epaxosNew.spec isRep)
    (rcv : ∀ γ i, replicaRcv.spec (isRep γ i))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG)) :
    serveReplica.spec (GF := GF) (hG := hG) := by
  intro γ W k sl hk
  wp_start as ⟨Hcf, Hmux, #Hsrv, %Hb, #Hsl, %HSS, #Hma, #Hlis, Hnt, #Hrx, #Hci⟩
  wp_auto
  wp_apply (wp_Register wp_SetCodec) $$ [$Hcf] as #Hcs
  wp_apply wp_nodeConfig as %cfg ⟨%c, Hcfg, Hprx, %Hc⟩
  have hk1 : W64 (k : Int) ≠ W64 1 := by
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [decide_eq_false hk1]
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hlen6 : sint.Z sl.len = 6 := by
    have h1 : serverAddrs.length = sint.nat sl.len := Hlen.1
    have : serverAddrs.length = 6 := rfl
    have h2 := Hlen.2
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    omega
  have hkm : sint.Z (W64 (k : Int) - W64 1) = (k : Int) - 1 := by
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hk26 : 2 ≤ k ∧ k ≤ 6 := by
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk; omega
  have hidx : 0 ≤ sint.Z (W64 (k : Int) - W64 1) ∧ sint.Z (W64 (k : Int) - W64 1) < sint.Z sl.len := by
    rw [hkm, hlen6]; omega
  simp only [hidx, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl _ serverAddrs _ (peerAddrOf k) (by rw [hkm]; omega) $$ [Hsl] as _
  · iframe #; ipureintro
    rw [hkm, show ((k : Int) - 1).toNat = k - 1 by omega]
    exact serverAddrs_peer k hk
  wp_apply wp_host
  rw [hostB_peer k hk]
  (try wp_auto)
  have hidx0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    rw [hlen6]; decide
  simp only [hidx0, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl _ serverAddrs _ masterAddr (by decide) $$ [Hsl] as _
  · iframe #; ipureintro; rfl
  have hport : (W64 7500 + W64 (k : Int) : w64) = portOf k := by
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hport]
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · iPkgInit
  ihave #Hce : net.rpc.cliEnv $$ []
  · unfold net.rpc.srvEnv; icases Hsrv with ⟨H, -⟩; iexact H
  wp_apply (wp_register γ W k hk (HSS ▸ rpcSS_master γ)) $$ [$Hnt]
    as %rid %nl ⟨%L, #Hlf, HL, %HLk, Hid, Hst⟩
  · iframe #
    isplitr
    · unfold rpcReady; iframe #
    ipureintro; exact Hb.2
  have hN := wp_New γ k (uint.nat rid) L nl cfg «$a10_ptr» c
  rw [show (W64 ((uint.nat rid : Nat) : Int)) = rid from by word] at hN
  rw [show (W64 5 - W64 1) / W64 2 = W64 2 from rfl]
  ihave #Hep : isPkgInit (PROP := IProp GF)
    pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos $$ []
  · iPkgInit
  unfold repStart
  icases Hst with ⟨Hfw, Hes⟩
  wp_apply hN $$ [$Hep $Hid $Hfw $Hes $Hlf $HL $Hci $Hcfg $Hprx $«$a10»] as %r ⟨Hr, %Hnn⟩
  · ipureintro
    refine ⟨⟨hk, HLk⟩, Hc.2.2.2, ?_⟩
    rw [Hc.2.2.1, hport]; rfl
  ihave Hrc := rcv γ (uint.nat rid) r $$ [$Hr]
  · iframe #; ipureintro; exact Hnn
  ihave ⟨%γs, #Hds⟩ := RpcHttpHyp.defaultServer_init $$ Hrpc
  wp_apply (RpcHttpHyp.Register_spec γs epCodec (ptrIface epaxos.Replica.ty r) replicaSvc
      go!"Replica" (W8 82) _ rfl ⟨by decide, by decide⟩) $$ [$Hrpc $Hds $Hcs $Hrc] as %e Hreg
  icases Hreg with (⟨%He, #Hsr⟩ | %He)
  rotate_left
  · rcases e with ei | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl He
  subst He
  wp_auto
  ihave #Hss : (□ ∀ a, ⌜lisAccepts (rpcAddrOf k) a⌝ → net.rpc.srvServes γs epCodec W a :
      IProp GF) $$ []
  · iintro !> %a %ha
    have ha' := (lisAccepts_rpcAddrOf k hk a).1 ha
    subst ha'
    unfold net.rpc.srvServes
    iintro !> %svc %S %hS
    rw [HSS] at hS
    rcases rpcSS_only γ _ svc S hS with ⟨hm, -, -⟩ | ⟨-, rfl, rfl⟩
    · have := masterAddr_not_replicaRpc (hm ▸ rpcAddrOf_mem k hk)
      contradiction
    · iframe Hsr; iapply replicaSvc_errOk
  wp_apply (RpcHttpHyp.HandleHTTP_spec γs epCodec W (lisAccepts (rpcAddrOf k)) [])
    $$ [$Hrpc $Hmux $Hds $Hss $Hsrv $Hcs] as ⟨-, #Hmh⟩
  · ipureintro
    exact ⟨Hb.1, by simp, by simp⟩
  wp_apply wp_itoa as %bsl Hbs
  wp_apply wp_bytes_to_string $$ [$Hbs] as -
  (try wp_auto)
  have hn : uint.nat (portOf k + W64 1000) = 8500 + k := by
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hn, listenAddr_eq k]
  wp_apply (wp_Listen go!"tcp" net.tcpNet_tcp (rpcAddrOf k)) as %lv %err Hl
  · isplitr
    · ipureintro; exact rpcAddrOf_listenOk k hk
    iapply RpcHttpAddr.rpcLisP_lis
    iexact Hlis
  icases Hl with (⟨%He, %l, Hli, Hnl, #Hon⟩ | ⟨%x, -, #Hre⟩)
  rotate_left
  · ihave %Hne := net.resErr_netErr $$ Hre
    have hne := net.netErr_ne_nil (Hne.2 (by simp))
    rcases err with ei | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl hne
  subst He
  wp_auto
  iapply fupd_wp
  imod (lisInv_alloc ⊤ _ l (rpcAddrOf k) true) $$ Hnl with #Hli2
  imodintro
  ihave #Hhttp : isPkgInit (PROP := IProp GF) pkg_id.net.http $$ []
  · iPkgInit
  wp_apply (RpcHttpHyp.Serve_spec W (rpcAddrOf k) defaultRPCPath lv l)
    $$ [$Hhttp $Hlis $Hmh $Hli $Hon $Hli2] as %e2 -
  · ipureintro; exact Hb.1
  iapply HΦ; itrivial

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
