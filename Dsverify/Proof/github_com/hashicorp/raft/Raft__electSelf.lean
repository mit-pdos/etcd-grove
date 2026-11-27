/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__electSelf.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).electSelf`: the election of term `s.term + 1`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__electSelf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__persistVote
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect

@[expose] public section

set_option linter.deprecated false

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

theorem nodup_getElem_not_mem_take {α} {l : List α} {k : Nat} {x : α} (hnd : l.Nodup)
    (h : l[k]? = some x) : x ∉ l.take k := by
  intro hm
  have h1 : x ∈ l.drop k := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using h⟩
  rw [← List.take_append_drop k l, List.nodup_append] at hnd
  exact hnd.2.2 x hm x h1 rfl

theorem mem_take_succ {α} {l : List α} {k : Nat} {x j : α} (h : l[k]? = some x) :
    j ∈ l.take (k + 1) ↔ j ∈ l.take k ∨ j = x := by
  rw [List.take_add_one, h]; simp

theorem start_bag_make {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (P : V → IProp GF) (cap : w64) (ch : Loc) (γc : ChanNames) :
    ⊢ isChan ch γc V -∗ ownChan γc V (if cap = W64 0 then ChanState.Idle else ChanState.Buffered [])
      ={⊤}=∗ isChanBag γc ch P := by
  by_cases h : cap = W64 0
  · rw [if_pos h]; exact start_bag P _ ch γc trivial
  · rw [if_neg h]; exact start_bag P _ ch γc trivial

theorem github_com.hashicorp.raft.Raft.electSelf.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_persistVote : github_com.hashicorp.raft.Raft.persistVote.spec (GF := GF) (hG := hG))
    (wp_BoolLoad : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.electSelf.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s tid => by
  wp_start as ⟨#Hr, Hmo, Htok⟩
  unfold mainOwnAt
  icases Hmo with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %cmp, Hsrv, Hdur, HownS, %Hvm, Hll, Hst,
    Hldr, Hpend, Hvreg, Happ, %Ha, Hfsm, Hpnd, Hcomp, %Hcmp, Hcfgs, #Hcfg, #Hccf, %Hcc, #Hcmt, #Hlch, #Hlchan,
    Hlown, %Hcap⟩
  ihave ⟨#HInv, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  imod srvOwn_facts γ ⊤ (by solve_ndisj) i s $$ [HInv Hsrv] with ⟨Hsrv, -, %Hsf⟩
  · iframe; iexact HInv
  imod llogPre_srv γ ⊤ (by solve_ndisj) i s $$ [HInv Hsrv] with ⟨Hsrv, #Hlpre⟩
  · iframe; iexact HInv
  ihave %hcv := isRaft_cv r γ rc i $$ Hr
  icases cfgAtIs_srvsV γ s.log _ cfg hcv Hcc.1 $$ Hcfg with ⟨%ss, #Hss, %Hok0⟩
  obtain ⟨Hok, Hvs⟩ := Hok0
  icases cfgsServers_acc' r ccfg cfg cidx li (DFrac.own 1) $$ Hcfgs with ⟨Hsv, Hcfgcl⟩
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ihave %Hsllen := ownSlice_len $$ Hss
  have hss32 : ss.length < 2 ^ 32 := Hok.2.1
  wp_auto
  wp_apply (chan.wp_make2 (V := Loc) cfg.Servers'.len) as %respCh %γc ⟨#Hrch, %Hγcap, Hrown⟩
  · ipureintro; constructor <;> word
  wp_apply +noauto (wp_getCurrentTerm.1 r γ i s) $$ [Hsrv] with Hsrv
  · iframe; iframe #
  wp_pure
  wp_bind (App (Val (GoInstruction (GoOp GoPlus go.uint64))) (Val _))
  iapply wp_go_step_receipt'
  · rfl
  inext
  iintro Hrc -
  wp_auto
  have hgt : (↑gprotN : CoPset) ⊆ ⊤ \ ↑termN := by unfold gprotN termN raftN; solve_ndisj
  have ht : uint.nat (W64 (s.term : Int) + W64 1) = s.term + 1 := by
    have := Hsf.2.2.2.2.2.1; word
  wp_apply (wp_setCurrentTerm r γ rc i sst (W64 (s.term : Int) + W64 1)
      iprop(srvOwn γ i { s with term := s.term + 1 } ∗ termLb γ i (s.term + 1) ∗
        candIs γ i (s.term + 1) s.log.length (lastTerm s.log) ∗ pubOwn γ i (s.term + 1) 0 ∗
        ccfgOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0)) $$ [HownS Hsrv Hrc]
    with ⟨HownS, Hsrv, #Hlb, #Hcand, Hpub, Hcc1, Hcc2⟩
  · iframe; iframe #
    iintro %t0 Htc0
    imod termCouple_agree γ _ hgt i s t0 $$ [HInv Hsrv Htc0] with ⟨Hsrv, Htc0, %ht0⟩
    · iframe; iframe #
    subst ht0
    rw [ht]
    imod electTerm_upd γ _ hgt i s $$ [HInv Hsrv Htc0 Hrc] with ⟨Hsrv, Htc, #Hlb, #Hcand, Hpub, Hcc1, Hcc2⟩
    · iframe; iframe #
    imodintro
    iframe; iframe #
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, #Hlid, #Hladdr, #Hpvd, -, #Hrcl⟩
  ihave ⟨%trI, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  ihave #Hcft := isRaft_cftCell r γ rc i $$ Hr
  wp_apply (wp_getLastEntry r γ rc i { s with term := s.term + 1 } a) $$ [Hll Hsrv Happ]
    as %lli %lt ⟨%Hlilt, Hll, Hsrv, Happ⟩
  · iframe; iframe #; ipureintro; exact Ha.1
  wp_apply (wp_getRPCHeader r γ rc i) as %h #Hh
  · iframe #
  unfold isTransport
  icases Htr with ⟨#Hrpc, #HConsumer, #HLocalAddr, #HEncodePeer, #HDecodePeer, #HSetHB, #HAEP, #HAE,
    #HRV, #HRPV, #HIS, #HTN⟩
  wp_apply HEncodePeer as %cs Hcs
  wp_apply (wp_cft_Load wp_BoolLoad r) $$ [Hcft] as %bcft -
  · iexact Hcft
  -- the request, shared read-only with the askPeer goroutines
  ipersist «$r0»
  irename «$r0» => Hreq
  ipersist req
  ipersist respCh
  ipersist r
  ipersist askPeer
  ipersist Hcs
  ihave #Hrv : rvReq γ (RequestVoteRequest.mk h (W64 (s.term : Int) + W64 1) cs lli lt bcft) i
      (s.term + 1) s.log.length (lastTerm s.log) $$ []
  · unfold rvReq
    iframe #
    ipureintro
    exact ⟨ht, Hlilt.1, Hlilt.2⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := SID) (V := Unit)) with ⟨%γv, Hauth⟩
  imod (start_bag_make (voteP γ i (s.term + 1) (cfgOfC γ.cv s.log) γv) cfg.Servers'.len respCh γc) $$ Hrch Hrown
    with #Hbag
  ihave %Hsllen2 := ownSlice_len $$ Hss
  ihave HI : (∃ (k : Nat) (M : GMap SID Unit) (s2 : SState) (sst2 : StableAbs) (sv0 : Server),
      "Hctr" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv0 ∗ "%Hk" ∷ ⌜k ≤ ss.length⌝ ∗
      "Hauth" ∷ ghostMapAuth γv 1 M ∗
      "%HM" ∷ ⌜∀ j, (M.lookup j).isSome ↔ j ∈ srvVoters (ss.take k)⌝ ∗
      "Hsrv" ∷ srvOwn γ i s2 ∗ "HownS" ∷ rc.ownS sst2 ∗
      "%Hself" ∷ ⌜(i ∈ srvVoters (ss.take k) ∧
          s2 = { s with term := s.term + 1, vterm := s.term + 1, vcand := i } ∧
          voteMatches sst2 { s with term := s.term + 1, vterm := s.term + 1, vcand := i }) ∨
        (i ∉ srvVoters (ss.take k) ∧ s2 = { s with term := s.term + 1 } ∧
          sst2 = StableAbs.mk (sst.ints.insert (go!"CurrentTerm" : List w8)
            (W64 (s.term : Int) + W64 1)) sst.bytes)⌝ ∗
      "Htok" ∷ rtok tid : IProp GF) $$ [i server Hauth Hsrv HownS Htok]
  · iexists 0, ∅, _, _, _
    iframe
    ipureintro
    refine ⟨by omega, ?_, Or.inr ⟨by simp [srvVoters], rfl, rfl⟩⟩
    intro j; simp [srvVoters]
  wp_for HI
  split
  · rename_i Hc
    have hk : k < ss.length := by simp only [decide_eq_true_eq] at Hc; word
    list_elem ss k as sv
    wp_auto
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] with -
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Hsv_lookup
    have hsv := Hok.1 sv (List.mem_of_getElem? Hsv_lookup)
    have hnotin : (sv.ID' : SID) ∉ srvVoters (ss.take k) := srvVoters_not_take ss k sv Hok.2.2 Hsv_lookup
    wp_if_destruct
    rotate_left
    · -- not a voter: skipped
      wp_for_post
      iframe
      iexists (k + 1), _, _, _, _
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      ipureintro
      have hns := srvVoters_take_succ_not ss k sv Hsv_lookup Hif
      refine ⟨by omega, fun j => by rw [hns j]; exact HM j, ?_⟩
      rcases Hself with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨(hns i).2 h1, h2, h3⟩
      · exact Or.inr ⟨fun h => h1 ((hns i).1 h), h2, h3⟩
    have hmemV : (sv.ID' : SID) ∈ cfgOfC γ.cv s.log := by
      rw [Hvs]; exact srvVoters_mem ss k sv Hsv_lookup Hif
    have hvk := srvVoters_take_succ ss k sv Hsv_lookup
    have Hsuf := Hif
    wp_if_destruct
    · -- the self vote
      rcases Hself with ⟨hin, -, -⟩ | ⟨-, rfl, rfl⟩
      · exact absurd hin hnotin
      ihave #Hrq2 := Hreq
      iStructNamed Hrq2
      ihave #Hh2 := Hh
      unfold hdrOk
      icases Hh2 with ⟨%Hhpv, #HhID, #HhAddr⟩
      iStructNamedSuffix RPCHeader "_h"
      wp_auto
      wp_apply (wp_persistVote r γ rc sv.ID' _ (W64 (s.term : Int) + W64 1) h.Addr' sv.ID')
        $$ [HownS] with HownS
      · iframe; iframe #
      imod grantVote_upd γ ⊤ (by solve_ndisj) sv.ID' sv.ID' { s with term := s.term + 1 }
          s.log.length (lastTerm s.log) (by simp only; omega) (upToDate_refl s.log)
          $$ [HInv Hsrv Hcand] with ⟨Hsrv, #Hvote⟩
      · iframe; iframe #
      wp_apply (wp_getRPCHeader r γ rc sv.ID') as %h2 #Hh2
      · iframe #
      iStructNamed «$v»
      have hlk : M.lookup sv.ID' = none := by
        cases h0 : M.lookup sv.ID' with
        | none => rfl
        | some _ => exact absurd ((HM sv.ID').1 (by rw [h0]; rfl)) hnotin
      imod (ghost_map_insert (GF := GF) (γ := γv) sv.ID' () hlk) $$ Hauth with ⟨Hauth, Htokj⟩
      wp_apply (wp_bag_send γc respCh «$v_ptr» (voteP γ sv.ID' (s.term + 1) (cfgOfC γ.cv s.log) γv))
        $$ [RequestVoteResponse Htokj]
      · iframe #
        unfold voteP
        iexists _, sv.ID'
        iframe
        isplitr
        · ipureintro; exact hmemV
        isplitr
        · simp only
          rw [ht]
          iapply termOk_of_candIs $$ Hcand
        iright; iexact Hvote
      wp_for_post
      iframe
      iexists (k + 1), _, _, _, _
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      ipureintro
      refine ⟨by omega, ?_, Or.inl ⟨?_, rfl, ?_⟩⟩
      · intro j
        rw [hvk]
        simp only [GMap.lookup_insert_eq_iff]
        by_cases hj : sv.ID' = j
        · subst hj; simp [Hsuf]
        · rw [if_neg hj, HM j]; constructor
          · intro h; exact Or.inl h
          · rintro (h | h); exact h; exact absurd h.2.symm hj
      · rw [hvk]; exact Or.inr ⟨Hsuf, rfl⟩
      · unfold voteMatches
        simp only [GMap.lookup_insert_eq_iff, if_true, Option.getD_some]
        exact ⟨ht, Or.inr trivial⟩
    · -- ask the peer `sv.ID'` in a goroutine
      have hlk : M.lookup sv.ID' = none := by
        cases h0 : M.lookup sv.ID' with
        | none => rfl
        | some _ => exact absurd ((HM sv.ID').1 (by rw [h0]; rfl)) hnotin
      imod (ghost_map_insert (GF := GF) (γ := γv) sv.ID' () hlk) $$ Hauth with ⟨Hauth, Htokj⟩
      have hmem : sv.ID' ∈ γ.srvs := hsv.1
      imod isSrv_of_mem γ ⊤ (by solve_ndisj) sv.ID' hmem $$ HInv with #Hvj
      wp_apply (wp_goFunc r γ rc i) $$ [Htok Htokj peer]
      · iframe; iframe #
        iintro %tid' Htok
        ihave #Hrq3 := Hreq
        iStructNamedPrefix Hrq3 "rq_"
        wp_auto
        iStructNamed «$r0»
        rw [hsv.2]
        wp_apply HRV $$ [] [] [] [RequestVoteResponse] [Htok] as %err Hargs Htok Hres
        · iexact Hvj
        · iexact Hreq
        · iexact Hrv
        · iexact RequestVoteResponse
        · iexact Htok
        icases Hres with (⟨%Herr, %rp, Hrp, Hrvr⟩ | ⟨Herr, %rp, Hrp⟩)
        · subst Herr
          wp_auto
          wp_apply (wp_bag_send γc respCh «$r0_ptr» (voteP γ i (s.term + 1) (cfgOfC γ.cv s.log) γv)) $$ [Hrp Htokj Hrvr]
          · iframe #
            unfold voteP rvResp
            icases Hrvr with ⟨#Hto, Hgr, -, -⟩
            iexists rp, sv.ID'
            iframe
            iframe #
            ipureintro; exact hmemV
          iframe
          ipureintro; rfl
        · ihave %Herr := errOk_ne_nil err $$ Herr
          cases err with
          | nil => exact absurd rfl Herr
          | ok e =>
          wp_auto
          wp_apply (wp_bag_send γc respCh «$r0_ptr» (voteP γ i (s.term + 1) (cfgOfC γ.cv s.log) γv)) $$ [Hrp Htokj]
          · iframe #
            unfold voteP
            iexists _, sv.ID'
            iframe
            isplitr
            · ipureintro; exact hmemV
            isplitr
            · rw [ht]
              iapply termOk_of_candIs $$ Hcand
            ileft; ipureintro; rfl
          iframe
          ipureintro; rfl
      iintro Htok
      wp_auto
      wp_for_post
      iframe
      iexists (k + 1), _, _, _, _
      have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hctr]
      iframe
      ipureintro
      refine ⟨by omega, ?_, ?_⟩
      · intro j
        rw [hvk]
        simp only [GMap.lookup_insert_eq_iff]
        by_cases hj : sv.ID' = j
        · subst hj; simp [Hsuf]
        · rw [if_neg hj, HM j]; constructor
          · intro h; exact Or.inl h
          · rintro (h | h); exact h; exact absurd h.2.symm hj
      · rcases Hself with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact Or.inl ⟨(hvk i).2 (Or.inl h1), h2, h3⟩
        · refine Or.inr ⟨?_, h2, h3⟩
          rw [hvk]
          rintro (h | h)
          · exact h1 h
          · exact Hif h.2.symm
  rename_i Hc
  have hkn : k = ss.length := by simp only [decide_eq_true_eq] at Hc; word
  subst hkn
  rw [List.take_length] at Hself
  rcases Hself with ⟨-, h2, hvm⟩ | ⟨hni, h2, h3⟩
  rotate_left
  · -- the candidate is no voter of its configuration: it does not vote for itself (a non-voter
    -- candidate, `timeoutNow`; FOLLOW-10)
    subst h2 h3
    wp_auto
    ihave Hcfgs := Hcfgcl $$ Hsv
    ihave #Hcmt2 := cmtIdx_mono γ s.term (s.term + 1) s.log s.log (uint.nat cidx) (by omega) rfl $$ Hcmt
    iapply HΦ
    iexists γv, γc, { s with term := s.term + 1 }
    iframe
    iframe #
    isplitl
    · isplitr
      · ipureintro
        unfold voteMatches at Hvm ⊢
        simp only [GMap.lookup_insert_eq_iff]
        rw [if_neg (by decide)]
        exact Hvm
      isplitr
      · ileft; ipureintro; decide
      ipureintro
      exact ⟨Ha, Hcmp, Hcc, Hcap⟩
    ipureintro
    exact ⟨rfl, rfl, Or.inr (by rw [Hvs]; exact hni)⟩
  subst h2
  wp_auto
  ihave Hcfgs := Hcfgcl $$ Hsv
  ihave #Hcmt2 := cmtIdx_mono γ s.term (s.term + 1) s.log s.log (uint.nat cidx) (by omega) rfl $$ Hcmt
  iapply HΦ
  iexists γv, γc, { s with term := s.term + 1, vterm := s.term + 1, vcand := i }
  iframe
  iframe #
  isplitl
  · isplitr
    · ipureintro; exact hvm
    isplitr
    · ileft; ipureintro; decide
    ipureintro
    exact ⟨Ha, Hcmp, Hcc, Hcap⟩
  ipureintro
  exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

end proof

end Perennial
