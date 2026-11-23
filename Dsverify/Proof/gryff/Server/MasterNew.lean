/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/MasterNew.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md); the lab's `Server/RawServer.lean` (its own net/rpc server
model) is folded in, over `Net/`'s net/rpc and `RpcHttpHyp`.

`masterlib.NewMaster(3, 7501)` (U2): the master with its own `rpc.Server` (a fresh server,
`RpcHttpHyp.NewServer_fresh_spec`; the master registered on it, `Server_Register_fresh_spec` with
`master_rcv`; `HandleHTTP` at `defaultRPCPath`, consuming the machine's `muxFree`), its listener at
`masterRpcLis = ":7501"` (retried; `Listen.spec` with `rpcLisP_lis`'s update), and its `Run`
goroutine (`wp_Master_Run'`). It returns a master with `masterOkDef` (what `Serve` asks).
-/
module

public import Dsverify.Proof.gryff.Server.MasterRun
public import Dsverify.Proof.gryff.Server.MasterServe
public import Dsverify.Proof.gryff.N.NetSpecs
public import Dsverify.Proof.gryff.N.ConnErr
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net fmt

attribute [local instance] GooseGlobalGS.gooseInvGS

section pure
variable [GooseExts] [GoGlobalContext]

/-- `Sprintf(":%d", port)`. -/
theorem sprintf_colon_port [GooseSemantics] [GooseInterp] [HasExt netExt] {GF : BundledGFunctors}
    [hG : HeapGS .hasLC GF] [NetProtoGS] [sem : go.Semantics] (pv : w64) (s : GoString)
    (h : SprintfOut go!":%d" [interface.mkOk go.int #pv] s) :
    s = W8 58 :: decimalPad 0 (sint.Z pv) := by
  have hf : go!":%d" = W8 58 :: W8 37 :: go!"d" := rfl
  rw [hf] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.byte_inv (by decide) h
  have hp : parseIntVerb go!"d" = some (0, []) := by decide
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.int_inv hp (IntArgValue.int pv)
    (fun z' hz' => intArg_int_uniq _ _ hz') h1
  rw [SprintfOut.done_inv h2, List.append_nil]

theorem colon_7501 : W8 58 :: decimalPad 0 (sint.Z (W64 7501)) = masterRpcLis := by
  have : sint.Z (W64 7501) = 7501 := by word
  rw [this]
  simp [decimalPad, padZeros, decimalNat_eq, digitByte, masterRpcLis]

/-- No address is taken by both the master's rpc listener and a replica's. -/
theorem master_not_replica_lis (k : Nat) (hk : k < 3) (a : GoString)
    (h1 : lisAccepts masterRpcLis a) : ¬ lisAccepts (replicaRpcLis k) a := by
  have hwm : wildPort masterRpcLis = some go!"7501" := by decide
  have hpm : ∀ p, portOf masterRpcLis = some p → p = go!"7501" := by
    intro p hp; have : portOf masterRpcLis = some go!"7501" := by decide
    rw [this] at hp; exact (Option.some.inj hp).symm
  obtain ⟨p', hwr, hne, hpr, hlne⟩ : ∃ p', wildPort (replicaRpcLis k) = some p' ∧ p' ≠ go!"7501" ∧
      (∀ p, portOf (replicaRpcLis k) = some p → p = p') ∧ replicaRpcLis k ≠ masterRpcLis := by
    rcases k with _|_|_|k
    · refine ⟨go!"8502", by decide, by decide, fun p hp => ?_, by decide⟩
      have : portOf (replicaRpcLis 0) = some go!"8502" := by decide
      rw [this] at hp; exact (Option.some.inj hp).symm
    · refine ⟨go!"8503", by decide, by decide, fun p hp => ?_, by decide⟩
      have : portOf (replicaRpcLis 1) = some go!"8503" := by decide
      rw [this] at hp; exact (Option.some.inj hp).symm
    · refine ⟨go!"8504", by decide, by decide, fun p hp => ?_, by decide⟩
      have : portOf (replicaRpcLis 2) = some go!"8504" := by decide
      rw [this] at hp; exact (Option.some.inj hp).symm
    · omega
  intro h2
  unfold lisAccepts at h1 h2
  rcases h1 with rfl | ⟨p, hp, ha⟩ <;> rcases h2 with h2 | ⟨q, hq, hb⟩
  · exact hlne h2
  · rw [hwr] at hq; cases hq; exact hne (hpm _ hb)
  · subst h2; rw [hwm] at hp; cases hp; exact hne (hpr _ ha).symm
  · rw [hwm] at hp; cases hp; rw [hwr] at hq; cases hq; rw [ha] at hb; cases hb; exact hne rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [mA : gryff.src.masterlib.Assumptions] [kA : examples.gryffnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [H : RpcHttpHyp GF]
variable (L : CodecLaws (GF := GF)) (RL : RcvLaws (GF := GF))
variable (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
variable (wp_DialHTTP : net.rpc.DialHTTP.spec (GF := GF) (hG := hG))
variable [nS : netN.NetSpecs GF]

/-- A `Master`'s points-to, field by field. -/
theorem master_struct_split (p : Loc) (v : gryff.src.masterlib.Master) :
    (p ↦ v : IProp GF) ⊢
      structFieldRef gryff.src.masterlib.Master go!"N" p ↦ v.N' ∗
      structFieldRef gryff.src.masterlib.Master go!"nodeList" p ↦ v.nodeList' ∗
      structFieldRef gryff.src.masterlib.Master go!"addrList" p ↦ v.addrList' ∗
      structFieldRef gryff.src.masterlib.Master go!"portList" p ↦ v.portList' ∗
      structFieldRef gryff.src.masterlib.Master go!"lock" p ↦ v.lock' ∗
      structFieldRef gryff.src.masterlib.Master go!"nodes" p ↦ v.nodes' ∗
      structFieldRef gryff.src.masterlib.Master go!"leader" p ↦ v.leader' ∗
      structFieldRef gryff.src.masterlib.Master go!"alive" p ↦ v.alive' ∗
      structFieldRef gryff.src.masterlib.Master go!"l" p ↦ v.l' ∗
      structFieldRef gryff.src.masterlib.Master go!"server" p ↦ v.server' := by
  iintro H
  iStructNamed H
  iframe

omit mA kA nS in
/-- The services of an address the master's listener takes: the master's. -/
theorem rpcServices_master (γ : GryffNames GF) (hw : worldOk γ) (a : GoString)
    (ha : lisAccepts masterRpcLis a) (svc : GoString) (S : net.rpc.MethodSpec GF)
    (h : γ.rpc.SS a svc = some S) :
    svc = go!"Master" ∧ S = masterSvc γ.deploy (regCarry γ.proto) := by
  rw [hw.1] at h
  unfold rpcServicesDef at h
  by_cases h1 : lisAccepts masterRpcLis a ∧ svc = go!"Master"
  · rw [if_pos h1] at h; exact ⟨h1.2, (Option.some.inj h).symm⟩
  · rw [if_neg h1] at h
    have h2 : ¬ ((∃ k, k < 3 ∧ lisAccepts (replicaRpcLis k) a) ∧ svc = go!"Replica") := by
      rintro ⟨⟨k, hk, hr⟩, -⟩; exact master_not_replica_lis k hk a ha hr
    rw [if_neg h2] at h; cases h

omit mA kA nS in
/-- A `Listen` error is `errAny`. -/
theorem resErr_errAny_m [net.Assumptions] (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    Perennial.net.resErr (GF := GF) (some k) op src addr ed nm err ⊢ models_lab.errAny err := by
  unfold Perennial.net.resErr Perennial.net.opErr
  iintro ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩, -⟩
  subst Herr
  iapply netN.opErrPtr_errAny

set_option goose.wp.extras true

include L RL wp_Call wp_DialHTTP in
theorem wp_NewMaster' (γ : GryffNames GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗
        net.rpc.codecSet gryffCodec ∗ net.rpc.srvEnv ∗ H.muxFree net.rpc.defaultRPCPath ∗
        H.rpcLisP γ.rpc masterRpcLis (net.rpc.connectReq net.rpc.defaultRPCPath)
          net.rpc.connectAns ∗
        dialEnv (GF := GF) ∗ (□ [∗list] k ∈ [0, 1, 2], replicaRpcOk γ k) ∗
        regAuth γ.deploy (1 : Qp).half [] ∗ inv deployN (deployInv γ.deploy γ.proto) ∗
        gryffInv2 γ.proto ∗ ⌜worldOk γ ∧ threadBound GF ≤ 2 ^ 31⌝ ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http }}
      (App (App (Val (@! gryff.src.masterlib.NewMaster)) (Val #(W64 3))) (Val #(W64 7501)))
    {{ (m : Loc), RET #m; masterOkDef γ m }} := by
  wp_start as ⟨#Hcs, #Hse, Hmux, #Hrl, #Hde, #Hras, Hreg, #Hdep, #Hg, %Hw, #Hkit, #Hrpc,
    #Hhttp⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 3) (by decide)) as %nl0 ⟨Hnl0, Hcnl0, %Hc1⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 3) (by decide)) as %al0 ⟨Hal0, Hcal0, %Hc2⟩
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 3) (by decide)) as %pl0 ⟨Hpl0, Hcpl0, %Hc3⟩
  wp_apply (wp_slice_make2 (V := Loc) (W64 3)) as %nsl ⟨Hnsl, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := Bool) (W64 3)) as %lsl ⟨Hlsl, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := Bool) (W64 3)) as %asl ⟨Hasl, -⟩
  · ipureintro; word
  wp_apply H.NewServer_fresh_spec as %s ⟨%γs, #Hsv, Hfr⟩
  try wp_auto
  ihave ⟨«$r0», %Hmnn⟩ := persistent_entails_left (typedPointsto_not_null _ _ _) $$ «$r0»
  icases master_struct_split _ _ $$ «$r0»
    with ⟨HN, Hnlf, Half, Hplf, Hlkf, Hnodes, Hleader, Halive, Hlf, Hsrvf⟩
  dsimp only
  imod sync.init_Mutex (masterLockInv γ.deploy «$r0_ptr») ⊤ «$v4_ptr» $$ [«$v4»]
    [Hnlf Half Hplf Hnl0 Hal0 Hpl0 Hcnl0 Hcal0 Hcpl0 Hreg] with #Hmu
  · iexact «$v4»
  · inext
    unfold masterLockInv
    iexists [], nl0, al0, pl0
    rw [dqOf_open [] (by simp)]
    simp only [List.map_nil, List.replicate_zero]
    iframe
    isplitl [Hcnl0 Hcal0 Hcpl0]
    · iapply (capOwn_open [] nl0 al0 pl0 (by simp)).2; iframe
    ipureintro
    refine ⟨List.nodup_nil, by simp, by rw [Hc1]; rfl, by rw [Hc2]; rfl, by rw [Hc3]; rfl⟩
  ipersist HN
  ipersist Hlkf
  ipersist Hsrvf
  ihave #Hmreg : masterReg γ «$r0_ptr» $$ []
  · unfold masterReg; iexists «$v4_ptr»; iframe #
  try wp_auto
  wp_apply (H.Server_Register_fresh_spec s γs gryffCodec (ptrIface src.masterlib.Master.ty «$r0_ptr»)
    (masterSvc γ.deploy (regCarry γ.proto)) go!"Master" (W8 77) go!"aster" rfl (by decide))
    $$ [Hfr] as %err0 ⟨-, #Hsreg⟩
  · iframe Hsv Hfr Hcs
    iapply master_rcv L RL γ «$r0_ptr» Hmnn
    iframe #
  ihave #Hss : iprop(□ ∀ a, ⌜lisAccepts masterRpcLis a⌝ → net.rpc.srvServes γs gryffCodec γ.rpc a)
    $$ []
  · iintro !> %a %ha
    unfold net.rpc.srvServes
    iintro !> %svc %S %HS
    obtain ⟨rfl, rfl⟩ := rpcServices_master γ Hw.1 a ha _ _ HS
    iframe Hsreg
    unfold masterSvc
    iapply withErr_errOk
  try wp_auto
  have hHH := H.Server_HandleHTTP_spec s γs gryffCodec γ.rpc (lisAccepts masterRpcLis)
    go!"/debug/rpc"
  rw [show net.rpc.defaultRPCPath = go!"/_goRPC_" from rfl] at hHH
  unfold net.rpc.defaultRPCPath
  wp_apply hHH $$ [Hmux] as #Hroute
  · iframe Hmux Hsv Hss Hse Hcs
    ipureintro; exact Hw.2
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %ssl ⟨Hssl, -⟩
  wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (.cons_int _ _ _ (.int _) .nil) $$ [Hssl] as %sp ⟨-, %Hsp⟩
  · iframe
  rw [sprintf_colon_port _ _ Hsp, colon_7501]
  ihave %hlok := H.rpcLisP_ok _ _ _ _ $$ Hrl
  wp_apply (nS.listen go!"tcp" Perennial.net.tcpNet_tcp masterRpcLis) $$ [] as %lv %err Hl
  · isplitr
    · ipureintro; exact hlok
    iapply H.rpcLisP_lis $$ Hrl
  ihave IHL : iprop(∃ (lv' e' : GoInterface),
      "Hlf" ∷ structFieldRef gryff.src.masterlib.Master go!"l" «$r0_ptr» ↦ lv' ∗
      "err" ∷ err_ptr ↦ e' ∗
      "Hl" ∷ ((⌜e' = interface.nil⌝ ∗ ∃ l, Perennial.net.isListener lv' l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l masterRpcLis true ∗
          netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l masterRpcLis) ∨
        (⌜e' ≠ interface.nil⌝ ∗ models_lab.errAny e'))) $$ [Hlf err Hl]
  · iexists lv, err; iframe
    icases Hl with (⟨%He, Hl⟩ | ⟨%x, -, #Hre⟩)
    · ileft; iframe Hl; ipureintro; exact He
    · iright; ihave #Ha := resErr_errAny_m _ _ _ _ _ _ _ $$ Hre
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
    wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (.cons_int _ _ _ (.int _) .nil) $$ [Hssl2]
      as %sp2 ⟨-, %Hsp2⟩
    · iframe
    rw [sprintf_colon_port _ _ Hsp2, colon_7501]
    wp_apply (nS.listen go!"tcp" Perennial.net.tcpNet_tcp masterRpcLis) $$ [] as %lv2 %err2 Hl
    · isplitr
      · ipureintro; exact hlok
      iapply H.rpcLisP_lis $$ Hrl
    wp_for_post
    iframe
    iexists lv2, err2
    iframe
    icases Hl with (⟨%He, Hl⟩ | ⟨%x, -, #Hre⟩)
    · ileft; iframe Hl; ipureintro; exact He
    · iright; ihave #Ha := resErr_errAny_m _ _ _ _ _ _ _ $$ Hre
      ihave %Hne := models_lab.errAny_ne_nil _ $$ Ha
      iframe Ha; ipureintro; exact Hne
  subst He
  wp_auto
  rw [if_neg (by simpa using (show (#false : val) ≠ #true from
    fun h => absurd (go.intoVal_inj h) (by decide))), if_pos (by simp)]
  wp_auto
  iapply fupd_wp
  imod lisInv_alloc ⊤ (extLocalGS netExt (L := hG.goose_localGS)) l masterRpcLis true $$ Hnl
    with #Hlinv
  imodintro
  ipersist Hlf
  wp_apply wp_fork $$ [Hnodes Hleader Halive Hnsl Hlsl Hasl]
  · wp_apply (wp_Master_Run' L wp_Call wp_DialHTTP γ «$r0_ptr») $$ [Hnodes Hleader Halive Hnsl Hlsl Hasl]
    · unfold runPre
      iexists nsl, lsl, asl
      iframe
      iframe #
      ipureintro; exact Hw.1
    ipureintro; exact isPanic_intoVal ()
  iapply HΦ
  unfold masterOkDef net.rpc.defaultRPCPath
  iexists lv', l
  iframe #
  ipureintro; exact Hw.2

end proof

end Perennial.gryff
