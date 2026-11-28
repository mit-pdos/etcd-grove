/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__verifyLeader_.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).verifyLeader` (stage 2; stage 4: over the leader's latest configuration,
fixes `6c3454c`, `4bb3955`, `0c7aa12`): the registration of a fresh verify future, or (a single voter,
the leader) its hand-off to the FSM goroutine.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__verifyLeader_
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__quorumSize
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh
public import Dsverify.Spec.github_com.hashicorp.raft.hasVote
public import Dsverify.Proof.github_com.hashicorp.raft.leader.VerifyCase
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Perennial.Proof.sync.Results
public import Dsverify.Proof.github_com.hashicorp.raft.leader.DurView

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hG sem package_sem hRB in
theorem nodup_getElem_not_mem_take' {α} {l : List α} {n : Nat} {x : α} (hnd : l.Nodup)
    (h : l[n]? = some x) : x ∉ l.take n := by
  intro hm
  have h1 : x ∈ l.drop n := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using h⟩
  rw [← List.take_append_drop n l, List.nodup_append] at hnd
  exact hnd.2.2 x hm x h1 rfl

/-- A select case receiving from a channel that is never sent on (`shutdownCh` in the main goroutine;
as `leaderLoop`'s). -/
theorem vl_dead_recv_clause {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (ch : Loc) (γc : ChanNames) (h : Expr) (Ψ : val → IProp GF) :
    £ 1 ∗ £ 1 ∗ isChanBag (V := V) γc ch (fun _ => iprop(False)) ⊢
      chan.blockingClausePre (.CommClause (.RecvCase t (Val #ch)) h) Ψ := by
  iintro ⟨Hl1, Hl2, #Hb⟩
  simp only [chan.blockingClausePre]
  iexists V, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr; · ipureintro; rfl
  isplitr; · iapply is_bag_is_chan γc ch _ $$ Hb
  iapply bag_recv_au γc ch _ (fun v ok => iprop(WP (App h (Val (PairV #v #ok))) {{ Ψ }}))
    $$ [Hl1 Hl2] Hb
  · iframe
  inext; iintro %v Hf; iexfalso; iexact Hf

set_option maxHeartbeats 2000000 in
theorem github_com.hashicorp.raft.Raft.verifyLeader.wp_proof
    (wp_quorumSize : github_com.hashicorp.raft.Raft.quorumSize.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_hasVote : github_com.hashicorp.raft.hasVote.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.verifyLeader.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s v => by
  wp_start as ⟨#Hr, Hm, Hl, Hv, ⟨%n0v, #Hn0v, %Hn0vl⟩⟩
  ihave ⟨#HInv, #Hisrv⟩ := isRaft_proto r γ rc i $$ Hr
  ihave %Hcv := isRaft_cv (r := r) (rc := rc) (i := i) (γ := γ) $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
  ihave #Hchans := isRaft_chans r γ rc i $$ Hr
  unfold raftChans deadField deadChan
  icases Hchans with ⟨-, -, -, ⟨%fsmCh, #HfsmF, #HfsmSpsc⟩, -, -, -, -, -,
    ⟨%shCh, #HshF, %γsh, #HshBag⟩, -, -, -, -⟩
  iunfold mainOwnAt at Hm
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hsrv, Hdur, HownS, %Hvm,
    HlastLog, Hstv, Hldr0, HlogPend, Hreg, Happ, %Ha, Hprod, Hpdn, Hcomp, %Hc, Hconf, #Hcfg, #Hccfg,
    %Hli, #Hcmt, #Hlch, #Hlchan, Hlown, %Hlcap⟩
  iunfold leaderOwnC at Hl
  iunfold leaderOwnM at Hl
  icases Hl with ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #Hldr', #Hlen0, Hccf, #Hccn, Hcm,
    #Hcmi, Hinfl, Hinfls, Hinflc, %Hfs, Hfs, Hrs, Hrsm, Hrmap, Hnt,
    ⟨%NM, %vch, Hntm, HNMa, #Hvch, HNMs⟩, Hsd, #Hsdn, %Hcov, %pb, #Hpb, %Hpbc⟩
  ihave ⟨#Hshared, Hstops⟩ := (replMain_split r γ i s.term rmap).1 $$ Hrmap
  unfold verifyNew
  icases Hv with ⟨%sc, #Hsc, HnotifyCh, Hqs, Hvotes, HvoteLock, Hresp⟩
  -- the registration snapshot (after the client's) and the leader's log then
  have hfact : iprop(Inv (GF := GF) γ ∗ leaderIs γ s.term i ∗ histLb γ sc) ∗ srvOwn γ i s ⊢
      |={⊤ \ ↑durN}=> srvOwn γ i s ∗ ((∃ s', histLb γ s' ∗
        ⌜snapLe sc s' ∧ s'.term i = s.term ∧ s'.dur i = s.dur.1 ∧ s'.llen s.term = s.log.length⌝) ∗
        llogPre γ s.term s.log) := by
    iintro ⟨⟨#HI, #Hl, #Hs⟩, Hsrv⟩
    imod srvOwn_now_leader γ (⊤ \ ↑durN) gprotN_diff_durN i s sc $$ [$HI $Hsrv $Hl $Hs]
      with ⟨Hsrv, %sv, #Hsv, %Hsv⟩
    imod llogPre_leader γ (⊤ \ ↑durN) gprotN_diff_durN i s $$ [$HI $Hsrv $Hl] with ⟨Hsrv, #Hpre⟩
    imodintro
    iframe Hsrv
    isplitr
    · iexists sv; iframe #; ipureintro; exact Hsv
    iexact Hpre
  ihave #HdurI := isRaft_durInv r γ rc i $$ Hr
  iapply wp_ncmod _ _ rfl (durFact γ rc i (E := ⊤) (by solve_ndisj) s _ _ hfact)
  isplitl [Hsrv]; · iframe; iframe #
  iintro ⟨Hsrv, ⟨%sv, #Hsv, %Hsv⟩, #Hpre⟩
  obtain ⟨Hscsv, Hsvt, -, Hsvl⟩ := Hsv
  ihave %Hn0eq := len0Is_agree γ s.term n0 n0v $$ [Hlen0 Hn0v]
  · iframe #
  have hn0 : n0 < s.log.length := by rw [Hn0eq]; exact Hn0vl
  -- the latest configuration's voters
  ihave ⟨%ss, #Hss, %Hssv⟩ := cfgAtIs_voters γ s.log (uint.nat li) cfg Hcv $$ Hcfg
  obtain ⟨Hssv, Hss0, Hss1⟩ := Hssv
  have hvL : cfgOfC γ.cv s.log = srvVoters ss := by
    unfold cfgOfC; rw [← Hli.1]; exact Hssv
  have hssok : (srvIds ss).Nodup ∧ ss.length < 2 ^ 63 := by
    by_cases h0 : uint.nat li = 0
    · rw [Hss0 h0]; simp [srvIds]
    · obtain ⟨h1, -, -, -, h2⟩ := Hss1 (by omega); exact ⟨h1, by omega⟩
  wp_auto_lc 3
  ipersist v
  wp_apply (wp_hasVote cfg ss DFrac.discard i) $$ [$Hss] as Hss'
  · ipureintro; exact hssok.1
  wp_join iprop(v.[verifyFuture, go!"votes"] ↦ (if i ∈ srvVoters ss then W64 1 else W64 0))
    with [Hvotes] as Hvotes
  · rw [if_pos (by simpa using Hif)]; iframe
  · rw [if_neg (by simpa using Hif)]; iexact Hvotes
  wp_apply (wp_quorumSize r ccfg cfg cidx li ss (DFrac.own 1) DFrac.discard) $$ [$Hconf $Hss']
    as ⟨Hconf, -⟩
  · ipureintro; exact hssok.2
  have hVle : (srvVoters ss).length ≤ ss.length := by
    unfold srvVoters; rw [List.length_map]; exact List.length_filter_le _ _
  have hqn : uint.nat (W64 (((srvVoters ss).length / 2 + 1 : Nat) : Int)) =
      (srvVoters ss).length / 2 + 1 := by
    have := hssok.2; word
  generalize W64 (((srvVoters ss).length / 2 + 1 : Nat) : Int) = q at hqn ⊢
  wp_if_destruct
  · -- a single voter, the leader: hand the future to the FSM goroutine (fix `0c7aa12`)
    have hiv : i ∈ srvVoters ss := by
      by_cases h : i ∈ srvVoters ss
      · exact h
      · exfalso; rw [if_neg h] at Hif; have := hssok.2; word
    rw [if_pos hiv] at Hif
    have hV1 : (srvVoters ss).length ≤ 1 := by
      have : uint.nat q ≤ 1 := by have := hssok.2; word
      omega
    ihave Hm : mainOwnAt r γ rc i s stLeader $$ [Hsrv Hdur HownS HlastLog Hstv Hldr0 HlogPend Hreg
        Happ Hprod Hpdn Hcomp Hconf Hlown]
    · unfold mainOwnAt
      iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
      iframe; iframe #
      ipureintro; exact ⟨Hvm, Ha, Hc, Hli, Hlcap⟩
    iapply wp_ncmod _ _ rfl (leader_verify_send r γ rc i s v)
    isplitl [Hm Hresp]
    · isplitr; · iexact HInv
      isplitr; · iexact HdurI
      isplitl [Hm]; · iexact Hm
      ileft
      iexists sc, sv, s.log, [i], n0
      iframe Hresp
      iframe #
      isplitr
      · ipureintro
        refine ⟨Hscsv, Hsvl.symm, hn0, by simp, ?_, ?_⟩
        · intro j hj; rw [List.mem_singleton.mp hj, hvL]; exact hiv
        · rw [hvL]; simp; omega
      ihave #Hiw : respWit γ i s.term sv $$ []
      · unfold respWit; iexists sv; iframe #; ipureintro; exact ⟨snapLe_refl sv, Hsvt⟩
      iframe #
      iapply BigSepL.bigSepL_nil.2; iempintro
    iintro ⟨%sent, Hp, HP, Hk⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, fsmCh,
        rc.names.fsmCh.chanName, (interface.mkOk (go.GoType.PointerType verifyFuture.ty) #v)
      isplitr
      · ipureintro
        exact ⟨rfl, rfl⟩
      ihave #Hch : isChan fsmCh rc.names.fsmCh.chanName GoInterface $$ [HfsmSpsc]
      · unfold isSpsc; icases HfsmSpsc with ⟨$, -⟩
      iframe Hch
      iapply spsc_send_au $$ HfsmSpsc [$Hlc1 $Hlc2 $Hlc3] [$Hp $HP]
      inext
      iintro Hp
      ihave Hm := Hk $$ Hp
      wp_auto
      iapply HΦ
      iframe Hm
      ihave Hrmap := (replMain_split r γ i s.term rmap).2 $$ [Hstops]
      · iframe; iframe #
      ihave HNMp : (∃ (NM' : GMap Loc Unit) (vch' : Loc), nt ↦$ NM' ∗
          ghostMapAuth rc.names.vnm (1 : Qp).half NM' ∗ r.[Raft, go!"verifyCh"] ↦□ vch' ∗
          [∗map] w ↦ _u ∈ NM', leaderNotifyEntry γ rc i s.term vch' w : IProp GF) $$ [Hntm HNMa HNMs]
      · iexists NM, vch
        iframe; iframe #
      unfold leaderOwnC leaderOwnM
      iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
      iframe; iframe #
      ipureintro; exact ⟨Hfs, Hcov, Hpbc⟩
    iapply BigAndL.bigAndL_cons.2
    isplit
    · iapply vl_dead_recv_clause shCh γsh
      iframe; iframe #
    iapply BigAndL.bigAndL_nil.2
    itrivial
  -- registration (verifyLeader's ghost step): the vote tokens of the latest configuration's voters
  have hVnd : (srvVoters ss).Nodup := by
    unfold srvVoters
    exact ((List.filter_sublist (l := ss)).map (fun s : Server => (s.ID' : List w8))).nodup hssok.1
  imod vreg_register γ rc i v q (by intro h; rw [h] at hqn; simp at hqn) s.term sv sc Hscsv NM
    (srvVoters ss) hVnd $$ [Hreg HNMa Hqs Hresp] with
    ⟨Hreg, HNMa, #Hqs, #Hvreg, Hback, Hnm, Htoks, %HNMv⟩
  · iframe; iframe #
  ihave #Hiw : respWit γ i s.term sv $$ []
  · unfold respWit; iexists sv; iframe #; ipureintro; exact ⟨snapLe_refl sv, Hsvt⟩
  -- the leader's own vote, if it is a voter (fix `4bb3955`)
  ihave ⟨HQ0, Htoks⟩ : (([∗list] j ∈ (if i ∈ srvVoters ss then [i] else []),
      voteTok rc v j ∗ respWit γ j s.term sv) ∗
      [∗list] j ∈ srvVoters ss, ⌜False ∨ j = i⌝ ∨ voteTok rc v j : IProp GF) $$ [Htoks]
  · by_cases hiv : i ∈ srvVoters ss
    · rw [if_pos hiv]
      ihave ⟨Hti, Htoks⟩ := tok_take (voteTok rc v) (fun _ => False) i (srvVoters ss) hiv id $$
        [Htoks]
      · iapply (BigSepL.bigSepL_mono (fun {n y} _ => ?_)) $$ Htoks
        iintro H; iright; iexact H
      iframe Htoks
      iapply BigSepL.bigSepL_singleton.2
      iframe; iframe #
    · rw [if_neg hiv]
      isplitr; · iapply BigSepL.bigSepL_nil.2; iempintro
      iapply (BigSepL.bigSepL_mono (fun {n y} _ => ?_)) $$ Htoks
      iintro H; iright; iexact H
  -- the vote lock
  imod sync.init_Mutex (voteInv γ rc i s.term sv s.log vch v) ⊤ _ $$ HvoteLock
    [HnotifyCh Hvotes Hback HQ0] with #Hlock
  · inext
    unfold voteInv
    iexists vch
    iframe HnotifyCh
    iright
    iframe Hback
    isplitr; · ipureintro; rfl
    iexists (if i ∈ srvVoters ss then W64 1 else W64 0), (if i ∈ srvVoters ss then [i] else [])
    iframe Hvotes HQ0
    ipureintro
    by_cases hiv : i ∈ srvVoters ss
    · simp only [if_pos hiv]
      refine ⟨rfl, by simp, ?_⟩
      intro j hj; rw [List.mem_singleton.mp hj, hvL]; exact hiv
    · simp only [if_neg hiv]
      exact ⟨rfl, List.nodup_nil, fun j hj => by simp at hj⟩
  ihave #HvR : verifyReg γ rc i s.term sv s.log vch v $$ []
  · unfold verifyReg
    iexists q
    iframe #
    isplitr
    · ipureintro; exact hn0
    ipureintro
    have := hssok.2
    refine ⟨Hsvl.symm, by omega, by rw [hvL]; omega, by omega⟩
  wp_apply (wp_mapInsert (go.GoType.PointerType verifyFuture.ty) nt NM v ()) $$ [$Hntm] as Hntm
  ipersist r
  wp_func_lits
  -- the heartbeats: each voter's notify set gets the future and its vote token (fix `6c3454c`)
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_gen (fun keys (n : Nat) m' => iprop(⌜m' = rmap⌝ ∗
    (∃ rp : Loc, repl_ptr ↦ rp) ∗ (∃ idv : GoString, id_ptr ↦ idv) ∗
    r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
    [∗list] j ∈ srvVoters ss, ⌜(False ∨ j = i) ∨ j ∈ keys.take n⌝ ∨ voteTok rc v j))) $$ Hrsm
  iintro %keys %hkeys
  obtain ⟨hkm, hksz, hknd⟩ := hkeys
  isplitl [repl id Hconf Htoks]
  · isplitr; · ipureintro; rfl
    isplitl [repl]; · iexists _; iframe
    isplitl [id]; · iexists _; iframe
    iframe Hconf
    iapply (BigSepL.bigSepL_mono (fun {n y} _ => ?_)) $$ Htoks
    iintro (%h | H)
    · ileft; ipureintro; left; exact h
    · iright; iexact H
  isplitl []
  · imodintro
    iintro %n %key %val %m' ⟨%hk1, %hk2⟩ ⟨%hm', ⟨%rp, Hrp⟩, ⟨%idv, Hid⟩, Hconf, Htoks⟩ Hrsm
    subst m'
    ihave #Hsh := BigSepM.bigSepM_lookup hk2 $$ Hshared
    unfold replShared
    icases Hsh with ⟨%cm', %stopCh, %trig, %notif, %sd', %tde, %γs, -, -, #Hjv, %Hji, -, -, -, -, -, -,
      -, #Hnotif, #Hnotifn, -, -, -, -, -, -, ⟨%vch', #Hvch', #Hnl⟩⟩
    icombine Hvch Hvch' gives %Hvv
    subst Hvv
    have hnmem : key ∉ keys.take n := nodup_getElem_not_mem_take' hknd hk1
    have htake : ∀ j, j ∈ keys.take n → j ∈ keys.take (n + 1) := by
      intro j hj; rw [List.take_add_one, hk1]; exact List.mem_append_left _ hj
    wp_auto
    wp_apply (wp_hasVote cfg ss DFrac.discard key) $$ [$Hss] as Hss'
    · ipureintro; exact hssok.1
    wp_if_destruct
    · -- a voter: its notify set gets the future (fix `6c3454c`)
      have hkv : key ∈ srvVoters ss := by simpa using Hif
      ihave ⟨Htk, Htoks⟩ := tok_take (voteTok rc v)
        (fun j => (False ∨ j = i) ∨ j ∈ keys.take n) key (srvVoters ss) hkv
        (by intro h; rcases h with (h | h) | h
            · exact h
            · exact Hji h
            · exact hnmem h) $$ Htoks
      wp_apply sync.Mutex.wp_Lock $$ [$Hnl] as ⟨Hlocked, %m, %M, Hn, Hm, HM⟩
      wp_apply (wp_mapInsert (go.GoType.PointerType verifyFuture.ty) m M v ()) $$ [$Hm] as Hm
      wp_apply sync.Mutex.wp_Unlock $$ [$Hnl $Hlocked Hn Hm HM Htk]
      · iexists m, <[v := ()]> M; iframe
        iapply BigSepM.bigSepM_insert_elim $$ [Htk] HM
        unfold notifyEntry
        iexists sv, s.log; iframe; iframe #
        ipureintro; rw [hvL]; exact hkv
      unfold notifyChan
      icases Hnotifn with ⟨%γn, #Hnb⟩
      wp_apply (wp_asyncNotifyCh γn notif (fun _ => iprop(True))) $$ [$Hnb]
      unfold forMapPostcondition
      iright; ileft
      isplit; · ipureintro; rfl
      iexists rmap; iframe Hrsm
      isplitr; · ipureintro; rfl
      isplitl [Hrp]; · iexists _; iframe
      isplitl [Hid]; · iexists _; iframe
      iframe Hconf
      iapply (BigSepL.bigSepL_mono (fun {n' y} _ => ?_)) $$ Htoks
      iintro (%h | H)
      · ileft; ipureintro
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (htake y h)
        · right
          rw [List.take_add_one, hk1, h]
          simp
      · iright; iexact H
    -- not a voter: no vote to ask
    unfold forMapPostcondition
    ileft
    isplit; · ipureintro; rfl
    iexists rmap; iframe Hrsm
    isplitr; · ipureintro; rfl
    isplitl [Hrp]; · iexists _; iframe
    isplitl [Hid]; · iexists _; iframe
    iframe Hconf
    iapply (BigSepL.bigSepL_mono (fun {n' y} _ => ?_)) $$ Htoks
    iintro (%h | H)
    · ileft; ipureintro
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (htake y h)
    · iright; iexact H
  isplitl []
  · imodintro
    iintro %n %key %m' ⟨%hk1, %hk2⟩ ⟨%hm', -⟩
    subst m'
    exact absurd ((hkm key).mp (List.mem_of_getElem? hk1)) (by rw [hk2]; simp)
  iintro %m' ⟨%hm', -, -, Hconf, -⟩ Hrsm
  subst m'
  wp_auto
  iapply HΦ
  isplitl [Hsrv Hdur HownS HlastLog Hstv Hldr0 HlogPend Hreg Happ Hprod Hpdn Hcomp Hconf Hlown]
  · unfold mainOwnAt
    iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
    iframe; iframe #
    ipureintro; exact ⟨Hvm, Ha, Hc, Hli, Hlcap⟩
  ihave Hrmap := (replMain_split r γ i s.term rmap).2 $$ [Hstops]
  · iframe; iframe #
  ihave HNMs := (BigSepM.bigSepM_insert (Φ := fun w _u => leaderNotifyEntry γ rc i s.term vch w)
    (show get? NM v = none from HNMv)).2 $$ [HNMs Hnm]
  · iframe
    unfold leaderNotifyEntry
    iexists sv, s.log; iframe; iframe #
  ihave HNMp : (∃ (NM' : GMap Loc Unit) (vch' : Loc), nt ↦$ NM' ∗
      ghostMapAuth rc.names.vnm (1 : Qp).half NM' ∗ r.[Raft, go!"verifyCh"] ↦□ vch' ∗
      [∗map] w ↦ _u ∈ NM', leaderNotifyEntry γ rc i s.term vch' w : IProp GF) $$ [Hntm HNMa HNMs]
  · iexists <[v := ()]> NM, vch
    iframe; iframe #
  unfold leaderOwnC leaderOwnM
  iexists cc, cm, infl, fs, rs, rmap, nt, sd, n0
  iframe; iframe #
  ipureintro; exact ⟨Hfs, Hcov, Hpbc⟩

end proof

end Perennial
