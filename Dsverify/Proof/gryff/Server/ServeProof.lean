/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/ServeProof.lean (run gryff-bump-1,
lab master 915f964; notes/dsv-gryff.md).

`serverlib.Serve(port)` on replica node `k` (`port = 8502 + k`): `rpc.HandleHTTP()` (the machine's
`DefaultServer`, which serves `"Replica"`: Net's `HandleHTTP.spec`, on the machine's
`DefaultServeMux` with nothing registered), the listener at `replicaRpcLis k = ":850(2+k)"`
(retried; `Listen.spec` with `rpcLisP_lis`'s update), then `http.Serve(l, nil)` (Net's
`http.Serve.spec_rpc`, on the calling thread's token, which returns only on a listener error: the
lab's postcondition `False` is `True` here).
-/
module

public import Dsverify.Proof.gryff.Server.MasterNew
public import Dsverify.GeneratedProof.gryff.src.serverlib
public import Net.Spec.net.rpc.HandleHTTP
public import Net.Spec.net.http.Serve
public import Net.Proof.net.rpc.HTTPPaths

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net fmt

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [sA : gryff.src.serverlib.Assumptions]
variable [net.rpc.Assumptions] [net.http.Assumptions] [RA : RpcHttpAddr GF]
variable [nS : netN.NetSpecs GF]
variable (wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG))
variable (wp_Serve : net.http.Serve.spec_rpc (GF := GF) (hG := hG))

omit sA nS [net.http.Assumptions] in
/-- The services of an address replica node `k`'s rpc listener takes: the replicas'. -/
theorem rpcServices_replica (γ : GryffNames GF) (hw : worldOk γ) (k : Nat) (hk : k < 3)
    (a : GoString) (ha : lisAccepts (replicaRpcLis k) a) (svc : GoString)
    (S : net.rpc.MethodSpec GF) (h : γ.rpc.SS a svc = some S) :
    svc = go!"Replica" ∧ S = replicaSvc := by
  rw [hw.1] at h
  unfold rpcServicesDef at h
  have h1 : ¬ (lisAccepts masterRpcLis a ∧ svc = go!"Master") := by
    rintro ⟨hm, -⟩; exact master_not_replica_lis k hk a hm ha
  rw [if_neg h1] at h
  by_cases h2 : (∃ k, k < 3 ∧ lisAccepts (replicaRpcLis k) a) ∧ svc = go!"Replica"
  · rw [if_pos h2] at h; exact ⟨h2.2, (Option.some.inj h).symm⟩
  · rw [if_neg h2] at h; cases h

theorem colon_rpcPort (k : Nat) (hk : k < 3) (port : w64) (hport : sint.Z port = 8502 + k) :
    W8 58 :: decimalPad 0 (sint.Z port) = replicaRpcLis k := by
  rw [hport]
  rcases k with _|_|_|k
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, replicaRpcLis]
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, replicaRpcLis]
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, replicaRpcLis]
  · omega

set_option goose.wp.extras true

include wp_HandleHTTP wp_Serve in
theorem wp_Serve' (γ : GryffNames GF) (k : Nat) (hk : k < 3) (port : w64)
    (hport : sint.Z port = 8502 + k) (γs : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib ∗
        net.rpc.codecSet gryffCodec ∗ net.rpc.srvEnv ∗
        net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) [] ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ net.http.httpSrvEnv ∗
        globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus ∗
        net.rpc.defaultServerAny γs ∗ net.rpc.svcReg γs gryffCodec go!"Replica" replicaSvc ∗
        RA.rpcLisP γ.rpc (replicaRpcLis k) (net.rpc.connectReq net.rpc.defaultRPCPath)
          net.rpc.connectAns ∗
        ⌜worldOk γ ∧ threadBound GF ≤ 2 ^ 31⌝ ∗ threadTok }}
      (App (Val (@! gryff.src.serverlib.Serve)) (Val #port))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcs, #Hse, Hmux, #Hhttp, #Hhe, #Hcon, #Hds, #Hsreg, #Hrl, %Hw, Htok⟩
  ihave #Hss : iprop(□ ∀ a, ⌜lisAccepts (replicaRpcLis k) a⌝ →
      net.rpc.srvServes γs gryffCodec γ.rpc a ∗
        ⌜γ.rpc.hs a ≠ [] ∧ γ.rpc.hsAns a = net.rpc.connectAns⌝) $$ []
  · iintro !> %a %ha
    have hhs := Hw.1.2 a (Or.inr ⟨k, hk, ha⟩)
    isplitl
    · unfold net.rpc.srvServes
      iintro !> %svc %S %HS
      obtain ⟨rfl, rfl⟩ := rpcServices_replica γ Hw.1 k hk a ha _ _ HS
      iframe Hsreg
      unfold replicaSvc
      iapply withErr_errOk
    ipureintro
    exact ⟨by rw [hhs.1]; simp [net.rpc.connectReq], hhs.2⟩
  wp_auto
  wp_apply (wp_HandleHTTP γs gryffCodec γ.rpc (lisAccepts (replicaRpcLis k)) [] (by simp)
      (by simp)) $$ [Hmux] as ⟨-, #Hroute⟩
  · iframe Hhttp Hmux Hds Hss Hse Hcs Hcon
    ipureintro; exact Hw.2
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %psl ⟨Hpsl, -⟩
  wp_apply log.wp_Printf _ _ _ _ (.cons_int _ _ _ (.int port) .nil) $$ [Hpsl] as -
  · iframe
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %ssl ⟨Hssl, -⟩
  ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · first | iPkgInit | iframe
  wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!":%d"
    [.lit go!":", .dir none _root_.Perennial.fmt.verb_d]
    _ _ _ _ (by fmt_encode) ?fits ?pa $$ [$HfmtS $Hssl] as %sp ⟨-, %Hsp⟩
  case pa => exact .int _ _ _ _ (.int _) .nil
  case fits => fmt_fits
  rw [sprintf_colon_port _ _ Hsp, colon_rpcPort k hk port hport]
  ihave %hlok := RA.rpcLisP_ok _ _ _ _ $$ Hrl
  wp_apply (nS.listen go!"tcp" Perennial.net.tcpNet_tcp (replicaRpcLis k)) $$ [] as %lv %err Hl
  · isplitr
    · ipureintro; exact hlok
    iapply RA.rpcLisP_lis $$ Hrl
  ihave IHL : iprop(∃ (lv' e' : GoInterface),
      "l" ∷ l_ptr ↦ lv' ∗ "err" ∷ err_ptr ↦ e' ∗
      "Hl" ∷ ((⌜e' = interface.nil⌝ ∗ ∃ l, Perennial.net.isListener lv' l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l (replicaRpcLis k) true ∗
          netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l (replicaRpcLis k)) ∨
        (⌜e' ≠ interface.nil⌝ ∗ models_lab.errAny e'))) $$ [l err Hl]
  · iexists lv, err; iframe
    icases Hl with (⟨%He, Hl⟩ | ⟨%x, -, #Hre⟩)
    · ileft; iframe Hl; ipureintro; exact He
    · iright
      ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
      · iPkgInit
      ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsy
      ihave #Ha := resErr_errAny_m _ _ _ _ _ _ _ $$ [$Hre $Hsys]
      ihave %Hne := models_lab.errAny_ne_nil _ $$ Ha
      iframe Ha; ipureintro; exact Hne
  wp_for IHL
  icases Hl with (⟨%He, %l, #Hli, Hnl, #Hon⟩ | ⟨%He, #HeA⟩)
  rotate_left
  · obtain ⟨i, rfl⟩ : ∃ i, e' = interface.ok i := by
      cases e' with
      | nil => exact absurd rfl He
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (by simp)]
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %lsl1 ⟨Hlsl1, -⟩
    wp_apply log.wp_Println_logArg _ _ _ $$ [Hlsl1] as -
    · iframe
      iintro !>
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_string
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ HeA
    wp_apply time.wp_Sleep
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %ssl2 ⟨Hssl2, -⟩
    ihave #HfmtS : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · first | iPkgInit | iframe
    wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!":%d"
      [.lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      _ _ _ _ (by fmt_encode) ?fits ?pa $$ [$HfmtS $Hssl2] as %sp2 ⟨-, %Hsp2⟩
    case pa => exact .int _ _ _ _ (.int _) .nil
    case fits => fmt_fits
    rw [sprintf_colon_port _ _ Hsp2, colon_rpcPort k hk port hport]
    wp_apply (nS.listen go!"tcp" Perennial.net.tcpNet_tcp (replicaRpcLis k)) $$ [] as %lv2 %err2 Hl
    · isplitr
      · ipureintro; exact hlok
      iapply RA.rpcLisP_lis $$ Hrl
    wp_for_post
    iframe
    iexists lv2, err2
    iframe
    icases Hl with (⟨%He, Hl⟩ | ⟨%x, -, #Hre⟩)
    · ileft; iframe Hl; ipureintro; exact He
    · iright
      ihave #Hsy : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
      · iPkgInit
      ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsy
      ihave #Ha := resErr_errAny_m _ _ _ _ _ _ _ $$ [$Hre $Hsys]
      ihave %Hne := models_lab.errAny_ne_nil _ $$ Ha
      iframe Ha; ipureintro; exact Hne
  subst He
  wp_auto
  rw [if_neg (by simpa using (show (#false : val) ≠ #true from
    fun h => absurd (go.intoVal_inj h) (by decide))), if_pos (by simp)]
  wp_auto
  iapply fupd_wp
  imod lisInv_alloc ⊤ (extLocalGS netExt (L := hG.goose_localGS)) l (replicaRpcLis k) true $$ Hnl
    with #Hlinv
  imodintro
  wp_apply (wp_Serve γ.rpc (replicaRpcLis k) net.rpc.defaultRPCPath lv' l
      net.rpc.litPattern_rpc net.rpc.defaultRPCPath_short) $$ [Htok] as %e -
  · iframe Hhttp Hhe Hli Hon Hlinv Htok
    isplitr
    · ipureintro; exact Hw.2
    isplitr
    · iapply RA.rpcLisP_net $$ Hrl
    iapply muxRpc_mono _ _ _ _ _ (fun a ha => ha.2) $$ Hroute
  wp_end

end proof

end Perennial.gryff
