/-
`m.run()` (`Master.run.specM`): waits for the five replicas, dials their rpc addresses, tells one
`BeTheLeader`, pings them for good. Phases: the wait loop (until five are registered: the lists
are then read-only), the dial loop (`clisOk`: the first `i` entries of `nodes` are clients of
replica rpc addresses; the `BeTheLeader` reply keeps `Leader = NextLeader = -1`, so `i` never goes
back and `nextLeader` stays `-1`), the first ping round under the lock (with both halves of
`alive`), `finishInit`, `Broadcast`, and the endless loop (ping round, `beTheLeader` reading
`alive[i]` with `run()`'s half, unlocked).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs
public import Proof.fmt.SprintfPure
public import Perennial.Proof.fmt.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions] [RA : RpcHttpAddr GF] [RH : RpcHttpHyp GF]

/-- A dialed replica client of `run()`. -/
def cliOk (W : net.rpc.RpcWorld GF) (c : Loc) : IProp GF :=
  iprop(∃ k : Nat, ⌜k ∈ replicaNodes⌝ ∗ net.rpc.isClient c W (rpcAddrOf k))

instance cliOk_persistent (W : net.rpc.RpcWorld GF) (c : Loc) : Persistent (cliOk W c) := by
  unfold cliOk; infer_instance

/-- The clients dialed so far: the first `n` entries of `nodes`. -/
def clisOk (W : net.rpc.RpcWorld GF) (ns : List Loc) (n : Nat) : IProp GF :=
  iprop(□ ∀ j : Nat, ⌜j < n⌝ -∗ ∃ c, ⌜ns[j]? = some c⌝ ∗ cliOk W c)

instance clisOk_persistent (W : net.rpc.RpcWorld GF) (ns : List Loc) (n : Nat) :
    Persistent (clisOk W ns n) := by
  unfold clisOk; infer_instance

theorem clisOk_set (W : net.rpc.RpcWorld GF) (ns : List Loc) (n : Nat) (c : Loc) :
    clisOk W ns n ⊢ clisOk W (ns.set n c) n := by
  unfold clisOk
  iintro #H
  imodintro
  iintro %j %hj
  ihave ⟨%c', %hc', #Hc⟩ := H $$ %j %hj
  iexists c'
  iframe Hc
  ipureintro
  rw [List.getElem?_set_ne (by omega)]; exact hc'

theorem clisOk_set_succ (W : net.rpc.RpcWorld GF) (ns : List Loc) (n : Nat) (c : Loc)
    (hn : n < ns.length) :
    clisOk W ns n ∗ cliOk W c ⊢ clisOk W (ns.set n c) (n + 1) := by
  unfold clisOk
  iintro ⟨#H, #Hc⟩
  imodintro
  iintro %j %hj
  by_cases hjn : j = n
  · subst hjn
    iexists c
    iframe Hc
    ipureintro
    simp [hn]
  · ihave ⟨%c', %hc', #Hc'⟩ := H $$ %j %(by omega)
    iexists c'
    iframe Hc'
    ipureintro
    rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hc'

theorem hssR {γ : EpNames} {W : net.rpc.RpcWorld GF} (hW : W.SS = rpcSS γ) (k : Nat)
    (hk : k ∈ replicaNodes) : W.SS (rpcAddrOf k) go!"Replica" = some replicaSvc := by
  rw [hW]; exact rpcSS_replica γ k hk

open replica.defs in
/-- `btlCall.spec` with the outcome dropped: the reply is as it was. -/
theorem wp_btl (hBtl : btlCall.spec (GF := GF)) (W : net.rpc.RpcWorld GF) (k : Nat)
    (cl la bl : Loc) (hk : k ∈ replicaNodes)
    (hss : W.SS (rpcAddrOf k) go!"Replica" = some replicaSvc) :
    {{ rpcReady ∗ net.rpc.isClient cl W (rpcAddrOf k) ∗ la ↦ BeTheLeaderArgs.mk ∗
        bl ↦ BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Replica.BeTheLeader")))
        (Val #(ptrIface BeTheLeaderArgs.ty la)))
        (Val #(ptrIface BeTheLeaderReply.ty bl)))
    {{ (err : GoInterface), RET #err; bl ↦ BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }} := by
  iintro %Φ Hpre HΦ
  wp_apply (hBtl W k cl la bl (W32 (-1)) (W32 (-1)) hk hss) $$ [$Hpre] as %err Hpost
  iapply HΦ
  icases Hpost with (⟨-, Hbl⟩ | ⟨-, Hbl⟩) <;> iexact Hbl

set_option goose.wp.extras true in
set_option maxHeartbeats 3200000 in
theorem Master.run.wp_proof (hP : dlog.Logger.Printf.spec (GF := GF))
    (hF : dlog.Logger.Fatal.spec (GF := GF)) (hNew : NewBeTheLeaderReply.specM (GF := GF))
    (hUpd : UpdateBeTheLeaderReply.specM (GF := GF)) (hBtl : btlCall.spec (GF := GF))
    (hPing : pingCall.spec (GF := GF)) (γ : EpNames) (W : net.rpc.RpcWorld GF) :
    Master.run.specM (GF := GF) γ W := by
  intro m
  wp_start as ⟨#Hm, Hr⟩
  unfold isMaster
  icases Hm with ⟨#Hpkg, %mu, %cfg, %logger, %ic, %c, #Hlock, #Hmu, #Hic, #Hcond, #HN, #Hcfgf, #Hcfg, %Hld, #Hlogf, #Hlog⟩
  ihave #Hdefs : isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs $$ []
  · iPkgInit
  unfold runRes
  icases Hr with ⟨%nds, %alsl0, Hndsf, Hnds, Hnext, #Half0, Halv0, #Hrpcs, %HW, #Hready, #Hcenv, #Hde⟩
  unfold dialEnv; icases Hde with ⟨#Hhe, #Hcon⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hrpcpkg : isPkgInit (PROP := IProp GF) pkg_id.net.rpc $$ []
  · unfold rpcReady; iintro; icases Hready with ⟨#H, -⟩; iexact H
  wp_auto
  wp_for
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  icases (masterLockInv_iff γ m).1 $$ Hinv with ⟨%ks, %nl, %al, %pl, %ldsl, %alsl, %latsl, %ld, %alv, %lat, %fi, %Hks, Hlists, #Hldf, Hld, #Half, Halv, #Hlatf, Hlat, Hfi⟩
  obtain ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩ := Hks
  have hks5 := ks_le ks hnd hsub
  by_cases h5 : ks.length < 5
  · unfold masterLists
    rw [ite_eq_left_of_eq_true _ _ (eq_true h5)]
    icases Hlists with ⟨Hnlf, Hnl, Hnlc, Hadf, Hal, Halc, Hplf, Hpl, Hplc, Hunset⟩
    ihave %Hnll := ownSlice_len _ _ _ $$ Hnl
    wp_auto
    rw [decide_eq_false (show ¬ nl.len = W64 5 by
      intro h; rw [h, List.length_map] at Hnll; have h1 := Hnll.1
      have : sint.nat (W64 5) = 5 := rfl
      omega)]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hld Halv Hlat Hfi Hnlf Hnl Hnlc Hadf Hal Halc
        Hplf Hpl Hplc Hunset]
    · iapply (masterLockInv_iff γ m).2
      iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, fi
      unfold masterLists
      rw [ite_eq_left_of_eq_true _ _ (eq_true h5)]
      iframe
      iframe Hldf Half Hlatf
      ipureintro; exact ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  · unfold masterLists
    rw [ite_eq_right_of_eq_false _ _ (eq_false h5)]
    icases Hlists with ⟨#Hnlf, #Hnl, #Hadf, #Hal, #Hplf, #Hpl, #Hlf⟩
    ihave %Hnll := ownSlice_len _ _ _ $$ Hnl
    have hk5 : ks.length = 5 := by omega
    wp_auto
    rw [decide_eq_true (show nl.len = W64 5 by
      rw [List.length_map, hk5] at Hnll; word)]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hld Halv Hlat Hfi]
    · iapply (masterLockInv_iff γ m).2
      iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, fi
      unfold masterLists
      rw [ite_eq_right_of_eq_false _ _ (eq_false h5)]
      iframe
      iframe Hldf Half Hlatf Hnlf Hnl Hadf Hal Hplf Hpl Hlf
      ipureintro; exact ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩
    wp_for_post
    wp_apply time.wp_Sleep
    ihave HI : (∃ (iw : w64) (ns : List Loc),
        "i" ∷ i_ptr ↦ iw ∗ "Hndsf" ∷ mfld m go!"nodes" ↦ nds ∗ "Hnds" ∷ nds ↦* ns ∗
        "Hnext" ∷ mfld m go!"nextLeader" ↦ W64 (-1) ∗
        "#Hcl" ∷ clisOk W ns (sint.nat iw) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z iw ∧ sint.Z iw ≤ 5 ∧ ns.length = 5⌝ : IProp GF)
        $$ [i Hndsf Hnds Hnext]
    · iexists (W64 0), _
      iframe
      isplitl
      · unfold clisOk; imodintro; iintro %j %hj
        exfalso; simp at hj; omega
      ipureintro; simp
    wp_for HI
    wp_if_destruct
    · have hlt : sint.Z iw < 5 := by
        have h5' : sint.Z (W64 5) = 5 := rfl
        omega
      have hkl : sint.nat iw < ks.length := by rw [hk5]; word
      obtain ⟨k, hkget⟩ : ∃ k, ks[sint.nat iw]? = some k := ⟨_, List.getElem?_eq_getElem hkl⟩
      have hkr : k ∈ replicaNodes := hsub k (List.mem_of_getElem? hkget)
      ihave %Hall := ownSlice_len _ _ _ $$ Hal
      ihave %Hpll := ownSlice_len _ _ _ $$ Hpl
      simp only [List.length_map, hk5] at Hall Hpll
      rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z al.len by word)]
      wp_apply wp_load_slice_index al (sint.Z iw) _ _ (replicaIp k) (by word) $$ [$Hal] as _
      · ipureintro; simp [sint.nat] at hkget ⊢; simp [hkget]
      rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z pl.len by word)]
      wp_apply wp_load_slice_index pl (sint.Z iw) _ _ (portOf k) (by word) $$ [$Hpl] as _
      · ipureintro; simp [sint.nat] at hkget ⊢; simp [hkget]
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
        [interface.mkOk go.string #(replicaIp k), interface.mkOk go.int #(portOf k + W64 1000)]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %fa ⟨Hfa, -⟩
      wp_apply _root_.Perennial.EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s:%d"
          [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d]
          _ [interface.mkOk go.string #(replicaIp k), interface.mkOk go.int #(portOf k + W64 1000)] _ _
          (by fmt_encode) (by fmt_fits) (.str _ _ _ (.int _ _ _ _ (.int _) .nil))
          $$ [$Hfmt $Hfa] as %out ⟨-, %Hout⟩
      have hout := sprintf_str_colon_int _ _ _ Hout
      have hk6 : k ≤ 6 := by
        simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hkr; omega
      have hz : sint.Z (portOf k + W64 1000) = 8500 + (k : Int) := by unfold portOf; word
      have hra : out = rpcAddrOf k := by
        rw [hout, rpcAddrOf_fmt k, hz]
      subst hra
      ihave %Hndsl := ownSlice_len _ _ _ $$ Hnds
      rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z nds.len by
        rw [Hi.2.2] at Hndsl; word)]
      ihave #Hra : RpcHttpAddr.rpcAddrP W (rpcAddrOf k) (connectReq defaultRPCPath) connectAns $$ []
      · unfold replicaRpcs
        iapply (BigSepL.bigSepL_mem (Φ := fun k =>
          RpcHttpAddr.rpcAddrP W (rpcAddrOf k) (connectReq defaultRPCPath) connectAns) hkr)
        iexact Hrpcs
      wp_auto
      wp_apply (DialHTTP_kit W (rpcAddrOf k)) $$ [$Hcenv $Hhe $Hcon $Hra] as %cl %err Hd
      · ipureintro; exact HW.2
      wp_apply wp_store_slice_index nds (sint.Z iw) ns cl $$ [$Hnds] as Hnds
      · ipureintro; constructor <;> word
      icases Hd with (⟨%He, #Hcli⟩ | ⟨%He, -⟩)
      rotate_left
      · rcases err with ei | _
        rotate_left
        · exact absurd rfl He
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any)
          [interface.mkOk go.int #iw, interface.mkOk go.string #(rpcAddrOf k)]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %sl4 ⟨-, -⟩
        wp_auto
        wp_apply (wp_Master_Printf hP) $$ [$Hlogf $Hlog]
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
        iexists iw, _
        iframe
        isplitl
        · iapply clisOk_set; iexact Hcl
        ipureintro; simp [Hi]
      subst He
      wp_apply hNew $$ [$Hdefs] as %bl Hbl
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
      icases (masterLockInv_iff γ m).1 $$ Hinv with ⟨%ks', %nl', %al', %pl', %ldsl', %alsl', %latsl', %ld', %alv', %lat', %fi', %Hks', Hlists', #Hldf', Hld', #Half', Halv', #Hlatf', Hlat', Hfi'⟩
      icombine Hldf Hldf' gives %Hldeq
      subst Hldeq
      have hldl' : ld'.length = 5 := Hks'.2.2.2.2.2.1
      have hiw5 : sint.nat iw < ld'.length := by rw [hldl']; word
      obtain ⟨b, hb⟩ : ∃ b, ld'[sint.nat iw]? = some b := ⟨_, List.getElem?_eq_getElem hiw5⟩
      ihave %Hldl' := ownSlice_len _ _ _ $$ Hld'
      rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z ldsl.len by
        rw [hldl'] at Hldl'; word)]
      wp_apply wp_load_slice_index ldsl (sint.Z iw) _ _ b (by word) $$ [$Hld'] as Hld'
      · ipureintro; simpa [sint.nat] using hb
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists' Hld' Halv' Hlat' Hfi']
      · iapply (masterLockInv_iff γ m).2
        iexists ks', nl', al', pl', ldsl, alsl', latsl', ld', alv', lat', fi'
        iframe
        iframe Hldf Half' Hlatf'
        ipureintro; exact Hks'
      have hstep : sint.nat (iw + W64 1) = sint.nat iw + 1 := by word
      have hset : (sint.Z iw).toNat = sint.nat iw := rfl
      ihave #Hcl' : clisOk W (ns.set (sint.Z iw).toNat cl) (sint.nat (iw + W64 1)) $$ []
      · rw [hstep, hset]
        iapply clisOk_set_succ
        · rw [Hi.2.2]; word
        iframe Hcl
        unfold cliOk
        iexists k
        iframe Hcli
        ipureintro; exact hkr
      cases b
      · wp_auto
        wp_for_post
        iframe
        iexists (iw + W64 1), _
        iframe
        iframe Hcl'
        ipureintro; refine ⟨by word, by word, ?_⟩; simp [Hi.2.2]
      wp_auto
      wp_alloc la as Hla
      wp_auto
      ihave %Hndsl2 := ownSlice_len _ _ _ $$ Hnds
      rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z nds.len by
        rw [Hi.2.2] at Hndsl; word)]
      wp_apply wp_load_slice_index nds (sint.Z iw) _ _ cl (by word) $$ [$Hnds] as Hnds
      · ipureintro; rw [List.getElem?_set_self]; rw [Hi.2.2]; word
      wp_apply (wp_btl hBtl W k cl la bl hkr (hssR HW.1 k hkr)) $$ [$Hready $Hcli $Hla $Hbl] as %e Hbl
      rcases e with ei | _
      all_goals try (
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any)
          [interface.mkOk go.string #(go!"Not today Zurg!")]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %sl5 ⟨-, -⟩
        wp_auto
        wp_apply (wp_Master_Fatal hF) $$ [$Hlogf $Hlog])
      all_goals (try wp_auto)
      all_goals wp_apply (hUpd bl) $$ [$Hdefs $Hbl] as Hbl
      all_goals wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
      all_goals rw [show W64 (sint.Z (W32 (-1))) = W64 (-1) from rfl]
      all_goals wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked $Hinv]
      all_goals wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
          (Val (LiteralValueV _)))
      all_goals iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #iw]
      all_goals wp_auto
      all_goals isplitl []
      all_goals try (ipureintro; rfl)
      all_goals iintro %sl6 ⟨-, -⟩
      all_goals wp_auto
      all_goals wp_apply (wp_Master_Printf hP) $$ [$Hlogf $Hlog]
      all_goals wp_for_post
      all_goals iframe
      all_goals iexists (iw + W64 1), _
      all_goals iframe
      all_goals iframe Hcl'
      all_goals ipureintro; refine ⟨by word, by word, ?_⟩; simp [Hi.2.2]
    -- the dial loop is over: five clients
    have hiw5 : sint.nat iw = 5 := by word
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    icases (masterLockInv_iff γ m).1 $$ Hinv with ⟨%ks', %nl', %al', %pl', %ldsl', %alsl', %latsl', %ld', %alv', %lat', %fi', %Hks', Hlists', #Hldf', Hld', #Half', Halv', #Hlatf', Hlat', Hfi'⟩
    icombine Half0 Half' gives %Haleq
    subst Haleq
    icombine Halv0 Halv' gives %Halveq
    subst Halveq
    icombine Halv0 Halv' as Halv
    rename_i ivar_ptr
    irename : (ivar_ptr ↦ (zero_val w64) : IProp GF) => Hkey
    have hld5 : ld'.length = 5 := Hks'.2.2.2.2.2.1
    ihave HP : (∃ (jw kv : w64) (nv : Loc) (alv ld : List Bool) (nlb : Bool),
        "i" ∷ i_ptr ↦ jw ∗ "Hkey" ∷ ivar_ptr ↦ kv ∗ "node" ∷ node_ptr ↦ nv ∗
        "Halv" ∷ alsl0 ↦* alv ∗ "Hld'" ∷ ldsl' ↦* ld ∗ "new_leader" ∷ new_leader_ptr ↦ nlb ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z jw ∧ sint.Z jw ≤ 5 ∧ alv.length = 5 ∧ ld.length = 5⌝ : IProp GF)
        $$ [i Hkey node Halv Hld' new_leader]
    · iexists (W64 0), _, _, _, _, _
      iframe
      ipureintro; simp [hld5]
    ihave %Hndsl := ownSlice_len _ _ _ $$ Hnds
    wp_for HP
    irename i => Hctr
    wp_if_destruct
    · have hj5 : sint.nat jw < 5 := by rw [Hi.2.2] at Hndsl; word
      unfold clisOk
      ihave ⟨%cj, %Hcj, #Hcj⟩ := Hcl $$ %(sint.nat jw) %(by rw [hiw5]; exact hj5)
      unfold cliOk
      icases Hcj with ⟨%kj, %hkj, #Hclj⟩
      rw [ite_eq_left (show 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z nds.len by word)]
      wp_apply wp_load_slice_index nds (sint.Z jw) _ _ cj (by word) $$ [$Hnds] as Hnds
      · ipureintro; simpa [sint.nat] using Hcj
      wp_alloc_auto
      wp_auto
      wp_alloc_auto
      wp_auto
      rename_i pa pr
      irename : (pa ↦ (zero_val replica.defs.PingArgs) : IProp GF) => Hpa
      irename : (pr ↦ (zero_val replica.defs.PingReply) : IProp GF) => Hpr
      rw [show (zero_val replica.defs.PingArgs) = replica.defs.PingArgs.mk (W8 0) from rfl,
        show (zero_val replica.defs.PingReply) = replica.defs.PingReply.mk from rfl]
      wp_apply (hPing W kj cj pa pr hkj (hssR HW.1 kj hkj)) $$ [$Hready $Hclj $Hpa $Hpr] as %e -
      ihave %Halvl := ownSlice_len _ _ _ $$ Halv
      ihave %Hldl := ownSlice_len _ _ _ $$ Hld'
      have hja : 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z alsl0.len := by
        rw [Hj.2.2.1] at Halvl; word
      have hjl : 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z ldsl'.len := by
        rw [Hj.2.2.2] at Hldl; word
      rcases e with ei | _
      · wp_auto
        rw [ite_eq_left hja]
        wp_apply wp_store_slice_index alsl0 (sint.Z jw) alv false $$ [$Halv] as Halv
        · ipureintro; rw [Hj.2.2.1]; word
        obtain ⟨b, hb⟩ : ∃ b, ld[sint.nat jw]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by rw [Hj.2.2.2]; exact hj5)⟩
        rw [ite_eq_left hjl]
        wp_apply wp_load_slice_index ldsl' (sint.Z jw) _ _ b (by word) $$ [$Hld'] as Hld'
        · ipureintro; simpa [sint.nat] using hb
        cases b
        · wp_auto
          wp_for_post
          iframe
          iexists (jw + W64 1), _, _, _, _, _
          iframe
          ipureintro; refine ⟨by word, by word, ?_, Hj.2.2.2⟩; simp [Hj.2.2.1]
        · wp_auto
          rw [ite_eq_left hjl]
          wp_apply wp_store_slice_index ldsl' (sint.Z jw) ld false $$ [$Hld'] as Hld'
          · ipureintro; rw [Hj.2.2.2]; word
          wp_for_post
          iframe
          iexists (jw + W64 1), _, _, _, _, _
          iframe
          ipureintro; refine ⟨by word, by word, ?_, ?_⟩ <;> simp [Hj.2.2.1, Hj.2.2.2]
      · wp_auto
        rw [ite_eq_left hja]
        wp_apply wp_store_slice_index alsl0 (sint.Z jw) alv true $$ [$Halv] as Halv
        · ipureintro; rw [Hj.2.2.1]; word
        wp_for_post
        iframe
        iexists (jw + W64 1), _, _, _, _, _
        iframe
        ipureintro; refine ⟨by word, by word, ?_, Hj.2.2.2⟩; simp [Hj.2.2.1]
    -- initialization is finished
    wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
    icases (ownSlice_halves _ _).1 $$ Halv with ⟨Halv, Halv0⟩
    obtain ⟨hnd', hsub', hnlc', halc', hplc', -, -, hlatl'⟩ := Hks'
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists' Hld' Halv Hlat' Hfi']
    · iapply (masterLockInv_iff γ m).2
      iexists ks', nl', al', pl', ldsl', alsl0, latsl', ld, alv, lat', true
      iframe
      iframe Hldf' Half0 Hlatf'
      ipureintro; exact ⟨hnd', hsub', hnlc', halc', hplc', Hj.2.2.2, Hj.2.2.1, hlatl'⟩
    -- the endless loop
    have halvl : alv.length = 5 := Hj.2.2.1
    clear Hj
    ihave HL : (∃ (alv : List Bool) (nlb : Bool),
        "Halv0" ∷ alsl0 ↦*{DFrac.own (1 : Qp).half} alv ∗ "new_leader" ∷ new_leader_ptr ↦ nlb ∗
        "%Halvl" ∷ ⌜alv.length = 5⌝ : IProp GF) $$ [Halv0 new_leader]
    · iexists alv, nlb
      iframe
      ipureintro; exact halvl
    clear halvl
    wp_for HL
    wp_apply time.wp_Sleep
    rename_i ivar_ptr
    irename : (ivar_ptr ↦ (zero_val w64) : IProp GF) => Hkey
    ihave HP : (∃ (jw kv : w64) (nv : Loc) (alv : List Bool) (nlb : Bool),
        "i" ∷ i_ptr ↦ jw ∗ "Hkey" ∷ ivar_ptr ↦ kv ∗ "node" ∷ node_ptr ↦ nv ∗
        "Halv0" ∷ alsl0 ↦*{DFrac.own (1 : Qp).half} alv ∗ "new_leader" ∷ new_leader_ptr ↦ nlb ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z jw ∧ sint.Z jw ≤ 5 ∧ alv.length = 5⌝ : IProp GF)
        $$ [i Hkey node Halv0 new_leader]
    · iexists (W64 0), _, _, _, _
      iframe
      ipureintro; simp [Halvl]
    wp_for HP
    irename i => Hctr
    wp_if_destruct
    · have hj5 : sint.nat jw < 5 := by rw [Hi.2.2] at Hndsl; word
      unfold clisOk
      ihave ⟨%cj, %Hcj, #Hcj⟩ := Hcl $$ %(sint.nat jw) %(by rw [hiw5]; exact hj5)
      unfold cliOk
      icases Hcj with ⟨%kj, %hkj, #Hclj⟩
      rw [ite_eq_left (show 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z nds.len by word)]
      wp_apply wp_load_slice_index nds (sint.Z jw) _ _ cj (by word) $$ [$Hnds] as Hnds
      · ipureintro; simpa [sint.nat] using Hcj
      wp_alloc_auto
      wp_auto
      wp_alloc_auto
      wp_auto
      rename_i pa pr
      irename : (pa ↦ (zero_val replica.defs.PingArgs) : IProp GF) => Hpa
      irename : (pr ↦ (zero_val replica.defs.PingReply) : IProp GF) => Hpr
      rw [show (zero_val replica.defs.PingArgs) = replica.defs.PingArgs.mk (W8 0) from rfl,
        show (zero_val replica.defs.PingReply) = replica.defs.PingReply.mk from rfl]
      wp_apply (hPing W kj cj pa pr hkj (hssR HW.1 kj hkj)) $$ [$Hready $Hclj $Hpa $Hpr] as %e -
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
      icases (masterLockInv_iff γ m).1 $$ Hinv with ⟨%ks2, %nl2, %al2, %pl2, %ldsl2, %alsl2, %latsl2, %ld2, %alv2, %lat2, %fi2, %Hks2, Hlists2, #Hldf2, Hld2, #Half2, Halv2, #Hlatf2, Hlat2, Hfi2⟩
      icombine Half0 Half2 gives %Haleq
      subst Haleq
      icombine Halv0 Halv2 gives %Halveq
      subst Halveq
      icombine Halv0 Halv2 as Halv
      obtain ⟨hnd2, hsub2, hnlc2, halc2, hplc2, hld2, -, hlat2⟩ := Hks2
      ihave %Halvl := ownSlice_len _ _ _ $$ Halv
      ihave %Hldl := ownSlice_len _ _ _ $$ Hld2
      have hja : 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z alsl0.len := by
        rw [Hj.2.2] at Halvl; word
      have hjl : 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z ldsl2.len := by
        rw [hld2] at Hldl; word
      ihave HQ : (∃ (alv' ld' : List Bool) (nlb' : Bool),
          "Halv" ∷ alsl0 ↦* alv' ∗ "Hld2" ∷ ldsl2 ↦* ld' ∗ "new_leader" ∷ new_leader_ptr ↦ nlb' ∗
          "%Hl" ∷ ⌜alv'.length = 5 ∧ ld'.length = 5⌝ : IProp GF) $$ [Halv Hld2 new_leader]
      · iexists _, _, _
        iframe
        ipureintro; exact ⟨Hj.2.2, hld2⟩
      rcases e with ei | _
      icases HQ with ⟨%alq, %ldq, %nlq, Halv, Hld2, new_leader, %Hl⟩
      wp_auto
      rw [ite_eq_left hja]
      wp_apply wp_store_slice_index alsl0 (sint.Z jw) alq false $$ [$Halv] as Halv
      · ipureintro; rw [Hl.1]; word
      obtain ⟨b, hb⟩ : ∃ b, ldq[sint.nat jw]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by rw [Hl.2]; exact hj5)⟩
      rw [ite_eq_left hjl]
      wp_apply wp_load_slice_index ldsl2 (sint.Z jw) _ _ b (by word) $$ [$Hld2] as Hld2
      · ipureintro; simpa [sint.nat] using hb
      cases b
      wp_auto
      ihave HQ : (∃ (alv' ld' : List Bool) (nlb' : Bool),
          "Halv" ∷ alsl0 ↦* alv' ∗ "Hld2" ∷ ldsl2 ↦* ld' ∗ "new_leader" ∷ new_leader_ptr ↦ nlb' ∗
          "%Hl" ∷ ⌜alv'.length = 5 ∧ ld'.length = 5⌝ : IProp GF) $$ [Halv Hld2 new_leader]
      · iexists _, _, _
        iframe
        ipureintro; simp [Hl]
      rotate_left
      wp_auto
      rw [ite_eq_left hjl]
      wp_apply wp_store_slice_index ldsl2 (sint.Z jw) ldq false $$ [$Hld2] as Hld2
      · ipureintro; rw [Hl.2]; word
      ihave HQ : (∃ (alv' ld' : List Bool) (nlb' : Bool),
          "Halv" ∷ alsl0 ↦* alv' ∗ "Hld2" ∷ ldsl2 ↦* ld' ∗ "new_leader" ∷ new_leader_ptr ↦ nlb' ∗
          "%Hl" ∷ ⌜alv'.length = 5 ∧ ld'.length = 5⌝ : IProp GF) $$ [Halv Hld2 new_leader]
      · iexists _, _, _
        iframe
        ipureintro; simp [Hl]
      rotate_left
      icases HQ with ⟨%alq, %ldq, %nlq, Halv, Hld2, new_leader, %Hl⟩
      wp_auto
      rw [ite_eq_left hja]
      wp_apply wp_store_slice_index alsl0 (sint.Z jw) alq true $$ [$Halv] as Halv
      · ipureintro; rw [Hl.1]; word
      ihave HQ : (∃ (alv' ld' : List Bool) (nlb' : Bool),
          "Halv" ∷ alsl0 ↦* alv' ∗ "Hld2" ∷ ldsl2 ↦* ld' ∗ "new_leader" ∷ new_leader_ptr ↦ nlb' ∗
          "%Hl" ∷ ⌜alv'.length = 5 ∧ ld'.length = 5⌝ : IProp GF) $$ [Halv Hld2 new_leader]
      · iexists _, _, _
        iframe
        ipureintro; simp [Hl]
      rotate_left
      all_goals icases HQ with ⟨%alq, %ldq, %nlq, Halv, Hld2, new_leader, %Hl⟩
      all_goals icases (ownSlice_halves _ _).1 $$ Halv with ⟨Halv, Halv0⟩
      all_goals wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists2 Hld2 Halv Hlat2 Hfi2]
      all_goals try (iapply (masterLockInv_iff γ m).2
                     iexists ks2, nl2, al2, pl2, ldsl2, alsl0, latsl2, ldq, alq, lat2, fi2
                     iframe
                     iframe Hldf2 Half0 Hlatf2
                     ipureintro; exact ⟨hnd2, hsub2, hnlc2, halc2, hplc2, Hl.2, Hl.1, hlat2⟩)
      all_goals wp_for_post
      all_goals iframe
      all_goals iexists (jw + W64 1), _, _, _, _
      all_goals iframe
      all_goals ipureintro; exact ⟨by word, by word, Hl.1⟩
    cases nlb
    · wp_auto
      wp_for_post
      iframe
      iexists alv, false
      iframe
      ipureintro; exact Hj.2.2
    wp_auto
    rename_i ivar_ptr
    irename : (ivar_ptr ↦ (zero_val w64) : IProp GF) => Hkey
    have halv5 : alv.length = 5 := Hj.2.2
    clear Hj
    ihave HB : (∃ (jw kv : w64), "i" ∷ i_ptr ↦ jw ∗ "Hkey" ∷ ivar_ptr ↦ kv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z jw ∧ sint.Z jw ≤ 5⌝ : IProp GF) $$ [i Hkey]
    · iexists (W64 0), _
      iframe
      ipureintro; simp
    wp_for HB
    irename i => Hctr
    wp_if_destruct
    · have hj5 : sint.nat jw < 5 := by rw [Hi.2.2] at Hndsl; word
      unfold clisOk
      ihave ⟨%cj, %Hcj, #Hcj⟩ := Hcl $$ %(sint.nat jw) %(by rw [hiw5]; exact hj5)
      unfold cliOk
      icases Hcj with ⟨%kj, %hkj, #Hclj⟩
      rw [ite_eq_left (show 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z nds.len by word)]
      wp_apply wp_load_slice_index nds (sint.Z jw) _ _ cj (by word) $$ [$Hnds] as Hnds
      · ipureintro; simpa [sint.nat] using Hcj
      ihave %Halvl := ownSlice_len _ _ _ $$ Halv0
      obtain ⟨b, hb⟩ : ∃ b, alv[sint.nat jw]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by rw [halv5]; exact hj5)⟩
      rw [ite_eq_left (show 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z alsl0.len by rw [halv5] at Halvl; word)]
      wp_apply wp_load_slice_index alsl0 (sint.Z jw) _ _ b (by word) $$ [$Halv0] as Halv0
      · ipureintro; simpa [sint.nat] using hb
      ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
      · iPkgInit
      cases b
      · wp_auto
        wp_apply errors.wp_New $$ [] as %ee -
        wp_for_post
        iframe
        iexists (jw + W64 1), _
        iframe
        ipureintro; exact ⟨by word, by word⟩
      wp_apply hNew $$ [$Hdefs] as %bl Hbl
      wp_alloc_auto
      wp_auto
      rename_i la
      irename : (la ↦ (zero_val replica.defs.BeTheLeaderArgs) : IProp GF) => Hla
      rw [ite_eq_left (show 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z nds.len by word)]
      wp_apply wp_load_slice_index nds (sint.Z jw) _ _ cj (by word) $$ [$Hnds] as Hnds
      · ipureintro; simpa [sint.nat] using Hcj
      wp_apply (wp_btl hBtl W kj cj la bl hkj (hssR HW.1 kj hkj)) $$ [$Hready $Hclj $Hla $Hbl] as %e Hbl
      rcases e with ei | _
      · wp_auto
        wp_for_post
        iframe
        iexists (jw + W64 1), _
        iframe
        ipureintro; exact ⟨by word, by word⟩
      wp_auto
      wp_apply (hUpd bl) $$ [$Hdefs $Hbl] as Hbl
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
      icases (masterLockInv_iff γ m).1 $$ Hinv with ⟨%ks3, %nl3, %al3, %pl3, %ldsl3, %alsl3, %latsl3, %ld3, %alv3, %lat3, %fi3, %Hks3, Hlists3, #Hldf3, Hld3, #Half3, Halv3, #Hlatf3, Hlat3, Hfi3⟩
      icombine Hldf' Hldf3 gives %Hldeq
      subst Hldeq
      obtain ⟨hnd3, hsub3, hnlc3, halc3, hplc3, hld3, halv3, hlat3⟩ := Hks3
      ihave %Hldl := ownSlice_len _ _ _ $$ Hld3
      rw [ite_eq_left (show 0 ≤ sint.Z jw ∧ sint.Z jw < sint.Z ldsl'.len by rw [hld3] at Hldl; word)]
      wp_apply wp_store_slice_index ldsl' (sint.Z jw) ld3 true $$ [$Hld3] as Hld3
      · ipureintro; rw [hld3]; word
      rw [show W64 (sint.Z (W32 (-1))) = W64 (-1) from rfl]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists3 Hld3 Halv3 Hlat3 Hfi3]
      · iapply (masterLockInv_iff γ m).2
        iexists ks3, nl3, al3, pl3, ldsl', alsl3, latsl3, _, alv3, lat3, fi3
        iframe
        iframe Hldf' Half3 Hlatf3
        ipureintro; exact ⟨hnd3, hsub3, hnlc3, halc3, hplc3, by simp [hld3], halv3, hlat3⟩
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
          (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #jw]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %sl7 ⟨-, -⟩
      wp_auto
      wp_apply (wp_Master_Printf hP) $$ [$Hlogf $Hlog]
      wp_for_post
      wp_for_post
      iframe
      iexists alv, true
      iframe
      ipureintro; exact halv5
    wp_for_post
    iframe
    iexists alv, true
    iframe
    ipureintro; exact halv5

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
