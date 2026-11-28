/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__startStopReplication.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).startStopReplication`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__startStopReplication
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__replicate
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Proof.github_com.hashicorp.raft.core.ObsHelpers
public import Dsverify.Proof.github_com.hashicorp.raft.main.MainCLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QPool
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Futures
public import Perennial.Spec.time.Now

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

theorem ml_fractional_exists_agree {PROP : Type _} [BI PROP] {X : Type _} (Φ : X → Qp → PROP)
    (hfrac : ∀ x, Fractional (Φ x)) (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

instance ml_true_fractional : Fractional (fun _ : Qp => (iprop(True) : IProp GF)) where
  fractional p q := by
    constructor
    · iintro -; isplit <;> itrivial
    · iintro -; itrivial

instance ml_lastContact_fractional (s : Loc) :
    Fractional (fun q : Qp => iprop(∃ t : time.Time,
      s.[followerReplication, go!"lastContact"] ↦{DFrac.own q} t) : Qp → IProp GF) := by
  apply ml_fractional_exists_agree (Φ := fun t q =>
    iprop(s.[followerReplication, go!"lastContact"] ↦{DFrac.own q} t))
  · intro t; exact ⟨fun q1 q2 => typedPointsto_frac_add _ t q1 q2⟩
  · intro x y q1 q2
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %h
    ipureintro; exact h

theorem take_succ_mem {α} (l : List α) (k : Nat) (x j : α) (h : l[k]? = some x) :
    j ∈ l.take (k + 1) ↔ j ∈ l.take k ∨ j = x := by
  rw [List.take_add_one, h]; simp

theorem nodup_not_mem_take {α} (l : List α) (k : Nat) (x : α) (hnd : l.Nodup) (h : l[k]? = some x) :
    x ∉ l.take k := by
  intro hm
  obtain ⟨t, hx⟩ := List.mem_iff_getElem?.mp hm
  have htk : t < k := by
    have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
  rw [List.getElem?_take, if_pos htk] at hx
  have htl : t < l.length := (List.getElem?_eq_some_iff.mp hx).1
  have := (hnd.getElem?_inj (j := k) htl).mp (by rw [hx, h])
  omega

theorem peerObs_ty_ne : PeerObservation.ty ≠ RaftState.ty := by
  unfold PeerObservation.ty RaftState.ty; simp

/-- The latest configuration's servers: their IDs are `cfgIdsOf`, each one of the protocol's
servers and its own address (unfolds `cfgAtIs`/`cfgVal`). -/
theorem ssr_cfg_servers (γ : GNames) (L : RLog) (p : Nat) (c : Configuration)
    (hp : p = lastCfgIdx L) :
    cfgAtIs (GF := GF) γ L p c ⊢
      ∃ ss : List Server, c.Servers' ↦*□ ss ∗ ⌜srvIds ss = cfgIdsOf γ.srvs L ∧
        ∀ sv ∈ ss, sv.Address' = sv.ID' ∧ sv.ID' ∈ γ.srvs⌝ := by
  subst hp
  iintro #H
  ihave ⟨%ss, #Hs, %hids⟩ := cfgAtIs_ids γ L c $$ H
  unfold cfgAtIs cfgVal
  icases H with (⟨%hp, #Hs0⟩ | ⟨%ss', %e, ⟨#Hs', %hok⟩, %h⟩)
  · ihave %heq := ownSlice_agree _ _ _ _ _ $$ Hs Hs0
    subst heq
    iexists []; iframe #; ipureintro
    exact ⟨hids, fun sv hsv => by simp at hsv⟩
  · ihave %heq := ownSlice_agree _ _ _ _ _ $$ Hs Hs'
    subst heq
    iexists ss; iframe #; ipureintro
    obtain ⟨-, hin, hsv, -⟩ := hok
    refine ⟨hids, fun sv hm => ⟨(hsv sv hm).2.1, hin _ ?_⟩⟩
    exact List.mem_map.mpr ⟨sv, hm, rfl⟩

end defs
end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable [htb : ThreadBoundLe GF (2 ^ 28)]

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.Raft.startStopReplication.wp_proof
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_replicate : github_com.hashicorp.raft.Raft.replicate.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.startStopReplication.spec (GF := GF) (hG := hG) := by
  intro r γ rc i s tid
  wp_start as ⟨#Hr, Hm, Hl, Htok⟩
  ihave ⟨#HInv, #Hvoter⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hcells with ⟨#HtermC, -, #Hdur, -, -, -, -, -⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %c, Hsrv, H2, H3, %H4, H5, H6,
    H7, H8, H9, H10, %Ha, H12, Hpd, Hcm, %Hc, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, #Hlch, #Hlchan,
    Hlown, %Hlcap⟩
  unfold leaderOwnM
  icases Hl with ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #Hldr, #Hlen0, Hcc, #Hccn, Hcm',
    #Hcmi, Hinfl, Hinfls, Hinflc, %Hfs, Hfs, Hrs, Hrsm, Hrmap, Hnt, HNMp, Hsd, #Hsdn, %Hrm0, %pb,
    #Hpb, %Hpbc⟩
  ihave #Hchans := isRaft_chans r γ rc i $$ Hr
  unfold raftChans
  icases Hchans with ⟨-, ⟨%vch, #Hvch, -⟩, -⟩
  ihave ⟨%ss, #Hss, %Hssok⟩ := ssr_cfg_servers γ s.log (uint.nat li) cfg Hli.1 $$ Hcfg
  ihave %Hsslen := ownSlice_len $$ Hss
  obtain ⟨Hssid, Hssv⟩ := Hssok
  wp_auto
  wp_apply (wp_map_make2 (K := SID) (V := Bool) cfg.Servers'.len ServerID.ty go.bool) as %icm Hicm
  wp_apply (wp_getLastIndex.2 r γ rc i) $$ [$Hr] as %lastIdx -
  ipersist r
  ihave HI : (∃ (k : Nat) (ic : GMap SID Bool) (rm : GMap SID Loc) (sv0 : Server),
      "i" ∷ i_ptr ↦ W64 k ∗ "server" ∷ server_ptr ↦ sv0 ∗ "Hicm" ∷ icm ↦$ ic ∗
      "Hrsm" ∷ rs ↦$ rm ∗ "Hrmap" ∷ ([∗map] j ↦ sr ∈ rm, replMain r γ rc i s.term j sr) ∗
      "%Hk" ∷ ⌜k ≤ ss.length ∧
        (∀ j, (rm !! j).isSome ↔ ((rmap !! j).isSome ∨ (j ∈ (ss.take k).map Server.ID' ∧ j ≠ i))) ∧
        (∀ j, ic !! j = if j ∈ (ss.take k).map Server.ID' ∧ j ≠ i then some true else none)⌝ ∗
      "Htok" ∷ rtok tid : IProp GF) $$ [i server Hicm Hrsm Hrmap Htok]
  · iexists 0, ∅, rmap, _; iframe
    ipureintro; refine ⟨Nat.zero_le _, fun j => by simp, fun j => by simp⟩
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hkle, Hrmk, Hick⟩ := Hk
    have hk : k < ss.length := by word
    have hk63 : k < 2 ^ 63 := by word
    list_elem ss k as sv
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cfg.Servers'.len from
      ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index cfg.Servers' (sint.Z (W64 k)) ss DFrac.discard sv (by word))
      $$ [$Hss] as Hss'
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hsv_lookup
    have hsvmem : sv ∈ ss := List.mem_of_getElem? Hsv_lookup
    obtain ⟨hsaddr, hssrv⟩ := Hssv sv hsvmem
    have hidk : (ss.map Server.ID')[k]? = some sv.ID' := by simp [Hsv_lookup]
    have htk : ∀ j, j ∈ (ss.take (k + 1)).map Server.ID' ↔ j ∈ (ss.take k).map Server.ID' ∨ j = sv.ID' := by
      intro j; rw [List.map_take, List.map_take]; exact take_succ_mem _ k _ j hidk
    wp_if_destruct
    · -- the server itself
      wp_for_post
      iframe
      iexists (k + 1), ic, rm, sv
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      refine ⟨by omega, fun j => ?_, fun j => ?_⟩
      · rw [Hrmk j, htk j]; constructor
        · rintro (h | ⟨h1, h2⟩); · exact Or.inl h
          · exact Or.inr ⟨Or.inl h1, h2⟩
        · rintro (h | ⟨h1 | h1, h2⟩); · exact Or.inl h
          · exact Or.inr ⟨h1, h2⟩
          · subst h1; exact absurd rfl h2
      · rw [Hick j]
        by_cases hj : j ∈ (ss.take k).map Server.ID' ∧ j ≠ sv.ID'
        · rw [if_pos hj, if_pos ⟨(htk j).mpr (Or.inl hj.1), hj.2⟩]
        · rw [if_neg hj, if_neg]; rintro ⟨h1, h2⟩
          rcases (htk j).mp h1 with h1 | h1
          · exact hj ⟨h1, h2⟩
          · exact h2 h1
    · have hick' : ∀ j, (<[sv.ID' := true]> ic) !! j =
          if j ∈ (ss.take (k + 1)).map Server.ID' ∧ j ≠ i then some true else none := by
        intro j
        by_cases hj : j = sv.ID'
        · subst hj; rw [GMap.lookup_insert, if_pos ⟨(htk _).mpr (Or.inr rfl), Hif⟩]
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj), Hick j]
          by_cases hj2 : j ∈ (ss.take k).map Server.ID' ∧ j ≠ i
          · rw [if_pos hj2, if_pos ⟨(htk j).mpr (Or.inl hj2.1), hj2.2⟩]
          · rw [if_neg hj2, if_neg]; rintro ⟨h1, h2⟩
            rcases (htk j).mp h1 with h1 | h1
            · exact hj2 ⟨h1, h2⟩
            · exact hj h1
      wp_apply (wp_mapInsert ServerID.ty icm ic sv.ID' true) $$ [$Hicm] as Hicm
      wp_apply (wp_map_lookup2 ServerID.ty (go.GoType.PointerType followerReplication.ty) rs rm sv.ID'
        (DFrac.own 1)) $$ [$Hrsm] as Hrsm
      cases hrm : rm !! sv.ID' with
      | none =>
        simp only [Option.getD_none, Option.isSome_none]
        wp_auto
        wp_apply (chan.wp_make2 (V := w64) (W64 1)) as %stopCh %γst ⟨#Hstch, %Hγst, Hstown⟩
        · ipureintro; word
        wp_apply (chan.wp_make2 (V := Unit) (W64 1)) as %trig %γtr ⟨#Htrch, %Hγtr, Htrown⟩
        · ipureintro; word
        wp_apply (chan.wp_make2 (V := Loc) (W64 1)) as %tde %γtde ⟨#Htdech, %Hγtde, Htdeown⟩
        · ipureintro; word
        wp_apply (wp_getCurrentTerm.1 r γ rc i s) $$ [$Hsrv $HInv $HtermC $Hdur] as Hsrv
        wp_apply wp_Now as %tnow -
        wp_apply (wp_map_make1 (K := Loc) (V := Unit) (go.GoType.PointerType verifyFuture.ty)
          (go.GoType.StructType [])) as %nmap Hnmap
        wp_apply (lc := 1) (chan.wp_make2 (V := Unit) (W64 1)) as %notif %γnf ⟨#Hnfch, %Hγnf, Hnfown⟩
        · ipureintro; word
        iStructNamedPrefix «$r0» "F"
        ipersist FcurrentTerm
        ipersist Fpeer
        ipersist Fcommitment
        ipersist FstopCh
        ipersist FtriggerCh
        ipersist FtriggerDeferErrorCh
        ipersist FnotifyCh
        ipersist FstepDown
        ipersist s
        have hb := htb.threadBound_le
        imod (sync.init_RWMutex_qpool (fun _ => iprop(True)) (E := ⊤) peerLockN _ hb) $$ [] FpeerLock
          with ⟨%γpl, #Hplg, #Hplp⟩
        · inext; itrivial
        imod (sync.init_RWMutex_qpool (fun q => iprop(∃ t : time.Time,
            «$r0_ptr».[followerReplication, go!"lastContact"] ↦{DFrac.own q} t)) (E := ⊤)
            replContactLockN _ hb) $$ [FlastContact] FlastContactLock
          with ⟨%γlc, #Hlcg, #Hlcp⟩
        · inext; iexists _; iexact FlastContact
        imod (sync.init_Mutex iprop(∃ (m : GoMap) (M : GMap Loc Unit),
            «$r0_ptr».[followerReplication, go!"notify"] ↦ m ∗ m ↦$ M ∗
            [∗map] v ↦ _u ∈ M, notifyEntry γ rc i s.term vch sv.ID' v) ⊤ _) $$ FnotifyLock [Fnotify Hnmap]
          with #Hnl
        · inext; iexists nmap, ∅; iframe
          iapply BigSepM.bigSepM_empty.2; iempintro
        imod (stopChan_alloc stopCh γst) $$ [Hstown] with ⟨%γs, #Hstc, Hprodc⟩
        · iframe #
          iexact Hstown
        ihave ⟨FnextIndex, FnextHalf⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ FnextIndex
        imod (inv_alloc nextIdxN ⊤ iprop(∃ v : w64,
            «$r0_ptr».[followerReplication, go!"nextIndex"] ↦{DFrac.own (1 : Qp).half} v))
          $$ [FnextIndex] with #Hni
        · inext; iexists _; iframe
        imod (start_bag (fun _ => iprop(True)) (ChanState.Buffered []) trig γtr trivial) $$ Htrch Htrown with #Htrb
        imod (start_bag (fun _ => iprop(True)) (ChanState.Buffered []) notif γnf trivial) $$ Hnfch Hnfown with #Hnfb
        imod (start_bag (fun d => deferResp d (fun _ => iprop(True))) (ChanState.Buffered []) tde γtde
          trivial) $$ Htdech Htdeown with #Htdeb
        imod (isSrv_of_mem γ ⊤ (by solve_ndisj) sv.ID' hssrv) $$ HInv with #Hjv
        iapply wp_ncmod _ _ rfl (srvV_termLb γ rc i (E := ⊤) (by solve_ndisj) s)
        isplitl [Hsrv]; · iframe; iframe #
        iintro ⟨Hsrv, #Htlb⟩
        have hpeer : sv = Server.mk sv.Suffrage' sv.ID' sv.ID' := by
          cases sv; simp only at hsaddr ⊢; rw [hsaddr]
        ihave #Hsh : replShared r γ rc i s.term sv.ID' «$r0_ptr» $$ []
        · unfold replShared rwLock
          iexists cm, stopCh, trig, notif, sd, tde, γs
          iframe #
          isplitr; · iexists sv.Suffrage'; rw [← hpeer]; iexact Fpeer
          isplitr; · ipureintro; exact Hif
          isplitr; · unfold notifyChan; iexists γtr; iexact Htrb
          unfold notifyChan; iexists γnf; iexact Hnfb
        wp_apply (wp_mapInsert ServerID.ty rs rm sv.ID' «$r0_ptr») $$ [$Hrsm] as Hrsm
        wp_apply (wp_goFunc r γ rc i _ tid) $$ [$Hr $Htok Ffailures FallowPipeline FnextHalf]
          as Htok
        · iintro %tid' Htok'
          wp_auto
          wp_apply (wp_replicate r γ rc i s.term «$r0_ptr» tid') $$ [$Hr $Htok' Ffailures
            FallowPipeline FnextHalf] as Htok'
          · unfold replOwn
            iexists sv.ID'
            iframe; iframe #
            iexists γs; unfold replStopCh; iexists stopCh; iframe #
          iframe; ipureintro; rfl
        wp_apply (wp_asyncNotifyCh γtr trig (fun _ => iprop(True))) $$ [$Htrb]
        wp_apply (wp_observe r γ rc i s _ tid) $$ [$Hr $Htok] as ⟨-, Htok⟩
        · iapply obsArg_other γ i s _ (mkOk_ne_leaderObs _ _ peerObs_ty_ne)
            (mkOk_not_raftState _ _ peerObs_ty_ne)
        wp_for_post
        iframe
        iexists (k + 1), <[sv.ID' := true]> ic, <[sv.ID' := «$r0_ptr»]> rm, sv
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        isplitl [Hrmap Hprodc]
        · iapply (BigSepM.bigSepM_insert hrm).2
          iframe
          unfold replMain
          iframe #
          iexists γs; iframe; unfold replStopCh; iexists stopCh; iframe #
        ipureintro
        refine ⟨by omega, fun j => ?_, hick'⟩
        by_cases hj : j = sv.ID'
        · subst hj; rw [GMap.lookup_insert]; simp only [Option.isSome_some, true_iff]
          exact Or.inr ⟨(htk _).mpr (Or.inr rfl), Hif⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj), Hrmk j, htk j]
          constructor
          · rintro (h | ⟨h1, h2⟩); · exact Or.inl h
            · exact Or.inr ⟨Or.inl h1, h2⟩
          · rintro (h | ⟨h1 | h1, h2⟩); · exact Or.inl h
            · exact Or.inr ⟨h1, h2⟩
            · exact absurd h1 hj
      | some sr =>
        simp only [Option.getD_some, Option.isSome_some]
        icases (BigSepM.bigSepM_lookup_acc hrm).1 $$ Hrmap with ⟨Hrm1, Hrmap⟩
        unfold replMain
        icases Hrm1 with ⟨#Hsh, Hst⟩
        ihave Hrmap := Hrmap $$ [Hst]
        · iframe; iframe #
        ihave ⟨#HcurT, ⟨%psf, #Hpeer⟩, #Hvj, #Hpl, -⟩ := replShared_core r γ i s.term sv.ID' sr $$ Hsh
        unfold rwLock
        icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
        wp_auto_lc 1
        imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
        wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
        wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP] as Hown
        imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
        simp only [hsaddr, decide_true]
        wp_auto
        wp_for_post
        iframe
        iexists (k + 1), <[sv.ID' := true]> ic, rm, sv
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        ipureintro
        refine ⟨by omega, fun j => ?_, hick'⟩
        rw [Hrmk j, htk j]
        by_cases hj : j = sv.ID'
        · subst hj
          have h1 := (Hrmk sv.ID').mp (by rw [hrm]; rfl)
          constructor
          · rintro (h | ⟨h1, h2⟩); · exact Or.inl h
            · exact Or.inr ⟨Or.inl h1, h2⟩
          · intro _; exact h1
        · constructor
          · rintro (h | ⟨h1, h2⟩); · exact Or.inl h
            · exact Or.inr ⟨Or.inl h1, h2⟩
          · rintro (h | ⟨h1 | h1, h2⟩); · exact Or.inl h
            · exact Or.inr ⟨h1, h2⟩
            · exact absurd h1 hj
  · obtain ⟨Hkle, Hrmk, Hick⟩ := Hk
    have hkn : k = ss.length := by word
    subst hkn
    rw [List.take_length] at Hrmk Hick
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range_mut_keys (fun keys n m' => iprop(∃ (v1 : Loc) (v2 : SID),
      repl_ptr ↦ v1 ∗ serverID_ptr ↦ v2 ∗ icm ↦$ ic ∗ inConfig_ptr ↦ icm ∗ lastIdx_ptr ↦ lastIdx ∗
      r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗
      ([∗map] j ↦ sr ∈ m', replMain r γ rc i s.term j sr) ∗ rtok tid ∗
      ⌜∀ j, m' !! j = if j ∈ keys.take n ∧ ic !! j = none then none else rm !! j⌝))) $$ Hrsm
    iintro %keys %hkeys
    obtain ⟨hkmem, -, hknd⟩ := hkeys
    isplitl [repl serverID Hicm inConfig lastIdx Hrs Hrmap Htok]
    · iexists _, _; iframe; ipureintro; intro j; simp
    isplitr
    · imodintro
      iintro %n %key %v %m' %Hh ⟨%v1, %v2, Hrepl, HsID, Hicm, HinC, HlI, Hrs, Hrmap, Htok, %Hm'⟩ Hrsm
      obtain ⟨hk1, hk2, hag⟩ := Hh
      have hm'k : m' !! key = some v := (hag n key (Nat.le_refl _) hk1).trans hk2
      have hknot : key ∉ keys.take n := nodup_not_mem_take _ n _ hknd hk1
      have htk : ∀ j, j ∈ keys.take (n + 1) ↔ j ∈ keys.take n ∨ j = key :=
        fun j => take_succ_mem _ n _ j hk1
      wp_auto
      wp_apply (wp_map_lookup1 ServerID.ty go.bool icm ic key (DFrac.own 1)) $$ [$Hicm] as Hicm
      by_cases hin : key ∈ ss.map Server.ID' ∧ key ≠ i
      · rw [Hick key, if_pos hin, Option.getD_some]
        wp_auto
        unfold forMapPostcondition
        ileft
        isplit
        · ipureintro; rfl
        iexists m'; iframe
        isplitl
        · ipureintro
          intro j
          rw [Hm' j]
          by_cases hj : j = key
          · subst hj
            rw [if_neg (fun h => hknot h.1), if_neg]
            rintro ⟨-, h⟩; rw [Hick, if_pos hin] at h; cases h
          · simp only [htk j, hj, or_false]
        ipureintro; intro j _; rfl
      · rw [Hick key, if_neg hin]
        icases (BigSepM.bigSepM_delete hm'k).1 $$ Hrmap with ⟨Hrk, Hrmap⟩
        unfold replMain
        icases Hrk with ⟨#Hsh, %γs, Hsc, Hcl⟩
        unfold replStopCh
        icases Hsc with ⟨%ch, #Hchf, #Hstc⟩
        ihave ⟨-, ⟨%psf, #Hpeer⟩, -⟩ := replShared_core r γ i s.term key v $$ Hsh
        rw [Option.getD_none, show Perennial.zero_val Bool = false from rfl]
        wp_auto
        wp_apply (wp_stop_send γs ch lastIdx) $$ [$Hstc $Hcl] as Hcr
        wp_apply (wp_stop_close γs ch) $$ [$Hstc $Hcr]
        wp_apply (wp_mapDelete rs m' key ServerID.ty (go.GoType.PointerType followerReplication.ty))
          $$ [$Hrsm] as Hrsm
        wp_apply (wp_observe r γ rc i s _ tid) $$ [$Hr $Htok] as ⟨-, Htok⟩
        · iapply obsArg_other γ i s _ (mkOk_ne_leaderObs _ _ peerObs_ty_ne)
            (mkOk_not_raftState _ _ peerObs_ty_ne)
        unfold forMapPostcondition
        iright; ileft
        isplit
        · ipureintro; rfl
        iexists (GMap.delete key m'); iframe
        isplitl
        · ipureintro
          intro j
          by_cases hj : j = key
          · subst hj
            rw [GMap.lookup_delete, if_pos ⟨(htk _).mpr (Or.inr rfl), by rw [Hick, if_neg hin]⟩]
          · rw [GMap.lookup_delete_ne _ (Ne.symm hj), Hm' j]
            simp only [htk j, hj, or_false]
        ipureintro; intro j hj; exact GMap.lookup_delete_ne _ (Ne.symm hj)
    iintro %m' ⟨%v1, %v2, Hrepl, HsID, Hicm, HinC, HlI, Hrs, Hrmap, Htok, %Hm'⟩ Hrsm
    wp_auto
    have hids : ∀ j, j ∈ cfgIdsOf γ.srvs s.log ↔ j ∈ ss.map Server.ID' := by
      intro j; rw [← Hssid]; rfl
    have hcov : replCover γ.srvs i s.log m' := by
      intro j
      rw [Hm' j, List.take_length, hids j]
      by_cases h : j ∈ ss.map Server.ID' ∧ j ≠ i
      · have hic : ic !! j = some true := by rw [Hick, if_pos h]
        rw [if_neg (by rintro ⟨-, h'⟩; rw [hic] at h'; cases h')]
        simp only [(Hrmk j).mpr (Or.inr h)]; exact iff_of_true trivial h
      · have hic : ic !! j = none := by rw [Hick, if_neg h]
        by_cases hk : j ∈ keys
        · rw [if_pos ⟨hk, hic⟩]; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          exact h
        · rw [if_neg (fun h' => hk h'.1)]
          have hn : rm !! j = none := by
            cases hh : rm !! j with
            | none => rfl
            | some x => exact absurd ((hkmem j).mpr (by rw [hh]; rfl)) hk
          rw [hn]; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          exact h
    iapply HΦ
    isplitl [Hsrv H2 H3 H5 H6 H7 H8 H9 H10 H12 Hpd Hcm Hconf Hlown]
    · iexists a, sst, cfg, ccfg, cidx, li, lch, γl, bs, c
      iframe; iframe #
      ipureintro; exact ⟨H4, Ha, Hc, Hli, Hlcap⟩
    iframe
    unfold leaderOwnC leaderOwnM
    iexists cc, cm, infl, fs, rs, m', nt, sd, n0
    iframe; iframe #
    ipureintro
    exact ⟨Hfs, hcov, Hpbc⟩

end proof

end Perennial
