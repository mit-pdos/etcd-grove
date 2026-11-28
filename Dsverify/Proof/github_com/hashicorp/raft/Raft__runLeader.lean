/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runLeader.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).runLeader`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.overrideNotifyBool
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupLeaderState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__startStopReplication
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__dispatchLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__leaderLoop
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Verify
public import Dsverify.Proof.github_com.hashicorp.raft.leader.Futures
public import Dsverify.Proof.github_com.hashicorp.raft.leader.MainCfg
public import Perennial.Proof.sync.Results

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

/-- A dispatched future can be answered `ErrLeadershipLost`. -/
theorem futResp_lost (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) (k : Nat) (e : Entry)
    (eLL : GoInterface) (hne : eLL ≠ interface.nil) :
    ((⌜e.kind = kNoop⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) (fun _ => iprop(True))) ∨
     (∃ (d : List w8) (n : Nat), ⌜e.kind = kCommand ∧ e.data = d⌝ ∗
        deferResp (f.[logFuture, go!"deferError"]) (futQ γ rc f d n)) ∨
     (∃ sc : Snap, ⌜e.kind = kBarrier⌝ ∗ barrierDisp γ i sc k e ∗
        deferResp (f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)) ∨
     (⌜e.kind = kConfig⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) cfgChangeQ)) ∗
      isRaftErr .leadershipLost eLL ⊢
    ∃ Q : GoInterface → IProp GF, deferResp (f.[logFuture, go!"deferError"]) Q ∗ Q eLL := by
  iintro ⟨(⟨-, H⟩ | ⟨%d, %n, -, H⟩ | ⟨%sc, -, -, H⟩ | ⟨-, H⟩), #He⟩
  · iexists _; iframe
  · iexists _; iframe; unfold futQ; iright; iright; iexact He
  · iexists _; iframe; unfold barrierQ; ileft; ipureintro; exact hne
  · iexists _; iframe; unfold cfgChangeQ; iright; ileft; iexists _; iexact He

/-- A big separating conjunction over a map, by its keys in some order (any key type). -/
theorem bigSepM_to_keys' {K V : Type} [DecidableEq K] (Ψ : K → V → IProp GF) :
    ∀ (keys : List K) (m : GMap K V), keys.Nodup → (∀ k, k ∈ keys ↔ (m !! k).isSome) →
    ([∗map] k ↦ v ∈ m, Ψ k v) ⊢ [∗list] k ∈ keys, ∃ v, ⌜m !! k = some v⌝ ∗ Ψ k v := by
  intro keys
  induction keys with
  | nil => intro m _ _; iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons k rest ih =>
    intro m hnd hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hk k).mp List.mem_cons_self)
    iintro Hm
    ihave ⟨Hk, Hm⟩ := (BigSepM.bigSepM_delete (Φ := Ψ) (m := m) hv).1 $$ Hm
    have hdel : ∀ k', k' ≠ k → (Iris.Std.delete m k) !! k' = m !! k' :=
      fun k' hne => Iris.Std.get?_delete_ne (m := m) (Ne.symm hne)
    have hdelk : (Iris.Std.delete m k) !! k = none := Iris.Std.get?_delete_eq (m := m) rfl
    ihave Hrest := ih (Iris.Std.delete m k) (List.nodup_cons.mp hnd).2 (fun k' => by
      by_cases hk' : k' = k
      · subst hk'; rw [hdelk]; simp; exact (List.nodup_cons.mp hnd).1
      · rw [hdel k' hk', ← hk k']; simp [hk']) $$ Hm
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hk]; · iexists v; iframe; ipureintro; exact hv
    iapply (BigSepL.bigSepL_mono (fun {j x} hx => ?_)) $$ Hrest
    have hxk : x ≠ k := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_of_getElem? hx)
    iintro ⟨%w, %hw, H⟩; iexists w; iframe; ipureintro; rw [← hdel x hxk]; exact hw

/-- A big separating conjunction over a map, by its keys in some order. -/
theorem bigSepM_to_keys (Ψ : SID → Loc → IProp GF) :
    ∀ (keys : List SID) (m : GMap SID Loc), keys.Nodup → (∀ k, k ∈ keys ↔ (m !! k).isSome) →
    ([∗map] k ↦ v ∈ m, Ψ k v) ⊢ [∗list] k ∈ keys, ∃ v, ⌜m !! k = some v⌝ ∗ Ψ k v := by
  intro keys
  induction keys with
  | nil => intro m _ _; iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons k rest ih =>
    intro m hnd hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hk k).mp List.mem_cons_self)
    iintro Hm
    ihave ⟨Hk, Hm⟩ := (BigSepM.bigSepM_delete (Φ := Ψ) (m := m) hv).1 $$ Hm
    have hdel : ∀ k', k' ≠ k → (Iris.Std.delete m k) !! k' = m !! k' :=
      fun k' hne => Iris.Std.get?_delete_ne (m := m) (Ne.symm hne)
    have hdelk : (Iris.Std.delete m k) !! k = none := Iris.Std.get?_delete_eq (m := m) rfl
    ihave Hrest := ih (Iris.Std.delete m k) (List.nodup_cons.mp hnd).2 (fun k' => by
      by_cases hk' : k' = k
      · subst hk'; rw [hdelk]; simp; exact (List.nodup_cons.mp hnd).1
      · rw [hdel k' hk', ← hk k']; simp [hk']) $$ Hm
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hk]; · iexists v; iframe; ipureintro; exact hv
    iapply (BigSepL.bigSepL_mono (fun {j x} hx => ?_)) $$ Hrest
    have hxk : x ≠ k := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_of_getElem? hx)
    iintro ⟨%w, %hw, H⟩; iexists w; iframe; ipureintro; rw [← hdel x hxk]; exact hw

end defs
end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.Raft.runLeader.wp_proof
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_overrideNotifyBool : github_com.hashicorp.raft.overrideNotifyBool.spec (GF := GF) (hG := hG))
    (wp_setupLeaderState : github_com.hashicorp.raft.Raft.setupLeaderState.spec (GF := GF) (hG := hG))
    (wp_startStopReplication :
      github_com.hashicorp.raft.Raft.startStopReplication.spec (GF := GF) (hG := hG))
    (wp_dispatchLogs : github_com.hashicorp.raft.Raft.dispatchLogs.spec (GF := GF) (hG := hG))
    (wp_leaderLoop : github_com.hashicorp.raft.Raft.leaderLoop.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.runLeader.spec (GF := GF) (hG := hG) :=
  fun r γ rc i s tid => by
  wp_start as ⟨#Hr, Hm, #Hlen0, Hcc2, Hany, Htok⟩
  ihave ⟨%eLL, #HeLL⟩ := isRaftErr_of_init (GF := GF) RaftErr.leadershipLost $$ Hpkg
  ihave %HeLLne := isRaftErr_nonnil RaftErr.leadershipLost eLL $$ HeLL
  wp_apply wp_with_defer as %defer Hdefer
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %cp, Hsrv, Hdur, HownS, %Hvm, HlastLog,
    Hstv, Hldr0, HlogPend, Hreg, Happ, %Ha, Hprod, Hpdn, Hcomp, %Hcp, Hconf, #Hcfg, #Hccfg, %Hli, #Hcmt, #Hlch,
    #Hlchan, Hlown, %Hlcap⟩
  wp_auto
  wp_apply (wp_overrideNotifyBool γl lch bs true) $$ [$Hlchan $Hlown] as Hlown
  · ipureintro; exact Hlcap
  wp_apply (wp_config r γ rc i) $$ [$Hr] as %c %Hc
  rw [decide_eq_true Hc.2.2.2.1]
  wp_auto
  wp_apply (wp_setupLeaderState r γ rc i s)
    $$ [$Hr $Hlen0 $Hany $Hcc2 Hsrv Hdur HownS HlastLog Hstv Hldr0 HlogPend Hreg Happ Hprod Hpdn Hcomp Hconf Hlown]
    as ⟨Hm, Hl⟩
  · unfold mainOwnAt
    iexists a, sst, cfg, ccfg, cidx, li, lch, γl, [true], cp
    iframe; iframe #
    ipureintro; exact ⟨Hvm, Ha, Hcp, Hli, Hlcap.1, by simp⟩
  ihave Hl := leaderOwnM_mono r γ rc i s.term _ (fun _ => True) _ (fun _ _ => trivial) $$ Hl
  wp_apply (wp_startStopReplication r γ rc i s tid) $$ [$Hr $Hm $Hl $Htok] as ⟨Hm, Hl, Htok⟩
  iStructNamedPrefix «$r0» "N"
  iStructNamedPrefix NdeferError "D"
  ipersist DerrCh
  ihave Hnoop : (dispP γ rc i «$r0_ptr») $$ [Nlog Nresponse Ndispatch]
  · unfold dispP noopP; iright
    iexists _, _, _
    iframe
    isplitr; · ipureintro; rfl
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSlice_nil
    unfold deferResp; iexists _; iframe #; ileft; ipureintro; rfl
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType (go.GoType.PointerType logFuture.ty))))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType logFuture.ty) [«$r0_ptr»]
  wp_auto
  isplitl []; · ipureintro; rfl
  iintro %nsl ⟨Hnsl, -⟩
  wp_auto
  wp_apply (wp_dispatchLogs r γ rc i s _ (DFrac.own 1) [«$r0_ptr»]) $$ [$Hr $Hm $Hl $Hnsl Hnoop]
    as ⟨%s2, Hm, %Hs2, Hl, -⟩
  · isplitr; · ipureintro; simp
    iapply BigSepL.bigSepL_singleton.2; iexact Hnoop
  wp_apply (wp_leaderLoop r γ rc i s2 tid) $$ [$Hr $Hm Hl $Htok] as ⟨Hm, ⟨%L, Hl⟩, Htok⟩
  · rw [Hs2.1]; iframe
    iexists s.log.length; iframe #; ipureintro; exact Hs2.2
  wp_apply (wp_setLastContact r γ rc i) $$ [$Hr]
  unfold leaderOwnC leaderOwnM
  icases Hl with ⟨%cc, %cm, %infl, %fs, %rs, %rmap, %nt, %sd, %n0, #Hldr', #Hlen0', Hcc, #Hccn, Hcm,
    #Hcmi, Hinfl, Hinfls, Hinflc, %Hfs, Hfs, Hrs, Hrsm, Hrmap, Hnt,
    ⟨%NM, %vch, Hntm, HNMa, #Hvch, HNMs⟩, Hsd, #Hsdn, %Hcov, -⟩
  ihave ⟨#Hshared, Hstops⟩ := (replMain_split r γ i s2.term rmap).1 $$ Hrmap
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range_gen (fun keys (j : Nat) m' => iprop(⌜m' = rmap⌝ ∗ ∃ v : Loc, p_ptr ↦ v ∗
    [∗list] k ∈ keys.drop j, ∃ sv, ⌜rmap !! k = some sv⌝ ∗
      ∃ γs : StopNames, replStopCh sv γs ∗ stopCloser γs))) $$ Hrsm
  iintro %keys %hkeys
  obtain ⟨hkm, hksz, hknd⟩ := hkeys
  isplitl [p Hstops]
  · isplitr; · ipureintro; rfl
    iexists _; iframe
    simp only [List.drop_zero]
    iapply bigSepM_to_keys _ keys rmap hknd (fun k => hkm k) $$ Hstops
  isplitl []
  · imodintro
    iintro %j %key %u %m' ⟨%hk1, %hk2⟩ ⟨%hm', %v, Hp, Hl⟩ Hrsm
    subst hm'
    have hjl : j < keys.length := (List.getElem?_eq_some_iff.mp hk1).1
    rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hk1).2]
    icases Hl with ⟨⟨%sv, %hsv, %γs, Hsc, Hprod⟩, Hl⟩
    rw [hk2] at hsv; cases hsv
    unfold replStopCh
    icases Hsc with ⟨%stc, #Hstf, #Hstch⟩
    wp_auto
    ihave Hprod := stopCloser_close γs $$ Hprod
    wp_apply (wp_stop_close γs stc) $$ [$Hstch $Hprod]
    unfold forMapPostcondition
    iright; ileft
    isplit; · ipureintro; rfl
    iexists _; iframe
    ipureintro; rfl
  isplitl []
  · imodintro
    iintro %j %key %m' ⟨%hk1, %hk2⟩ ⟨%hm', -⟩
    subst hm'
    exact absurd ((hkm key).mp (List.mem_of_getElem? hk1)) (by rw [hk2]; simp)
  iintro %m' ⟨%hm', %v, Hp, -⟩ Hrsm
  subst hm'
  wp_auto
  ihave #HgLL0 := isRaftErr_global RaftErr.leadershipLost eLL $$ HeLL
  ihave #HgLL : (globalAddr ErrLeadershipLost ↦□ eLL : IProp GF) $$ []
  · have e : RaftErr.leadershipLost.var = ErrLeadershipLost := rfl
    rw [← e]; iexact HgLL0
  ihave %Hil := ownSlice_len $$ Hinfls
  simp only [List.length_map] at Hil
  ihave HI : (∃ (k : Nat) (fv : Loc), "i" ∷ i_ptr ↦ W64 k ∗ "f" ∷ f_ptr ↦ fv ∗
      "%Hk" ∷ ⌜k ≤ fs.length⌝ ∗
      "Hfs" ∷ ([∗list] x ∈ fs.drop k, futResp γ rc i x.f x.k x.e ∗ llogIdx γ s2.term x.k x.e) : IProp GF)
    $$ [i f Hfs]
  · iexists 0, _; iframe; ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hk : k < fs.length := by word
    have hk63 : k < 2 ^ 63 := by have : sint.nat infl.len < 2 ^ 63 := by word
                                 omega
    list_elem fs k as x
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z infl.len from
      ⟨by word, Hif⟩)]
    wp_apply (wp_load_slice_index infl (sint.Z (W64 k)) (fs.map InflightItem.f) (DFrac.own 1)
      x.f (by word)) $$ [$Hinfls] as Hinfls
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; simp [Hx_lookup]
    have hdrop : fs.drop k = x :: fs.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hk]; congr; exact (List.getElem?_eq_some_iff.mp Hx_lookup).2
    rw [hdrop]
    icases Hfs with ⟨⟨Hxr, -⟩, Hfs⟩
    unfold futResp
    icases Hxr with ⟨-, -, Hde⟩
    ihave ⟨%Q, HdQ⟩ := futResp_lost γ rc i x.f x.k x.e eLL HeLLne $$ [Hde]
    · iframe; iframe #
    wp_apply (deferError.respond_logFuture wp_respond x.f Q eLL) $$ [HdQ] as -
    · ileft; iexact HdQ
    wp_for_post
    iframe
    iexists (k + 1), x.f
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
    iframe; ipureintro; omega
  · -- answer every verify future of the notify set (`ErrLeadershipLost`)
    unfold mainOwn mainOwnAt
    icases Hm with ⟨%s3, %st3, ⟨%a3, %sst3, %cfg3, %ccfg3, %cidx3, %li3, %lch3, %γl3, %bs3, %cp3, Hsrv3, Hdur3,
      HownS3, %Hvm3, HlastLog3, Hstv3, Hldr3, HlogPend3, Hreg3, Happ3, %Ha3, Hprod3, Hpdn3, Hcomp3, %Hcp3, Hconf3,
      #Hcfg3, #Hccfg3, %Hli3, #Hcmt3, #Hlch3, #Hlchan3, Hlown3, %Hlcap3⟩, Hl03⟩
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range_gen (fun keys (n : Nat) m' => iprop(⌜m' = NM⌝ ∗
      (∃ v : Loc, future_ptr ↦ v) ∗ ∃ NMr : GMap Loc Unit, verifyRegistry γ rc i ∗
        ghostMapAuth rc.names.vnm (1 : Qp).half NMr ∗
        ⌜∀ w, (NMr !! w).isSome ↔ w ∈ keys.drop n⌝ ∗ [∗list] w ∈ keys.drop n, nmTok rc w))) $$ Hntm
    iintro %keys %hkeys
    obtain ⟨hkm, hksz, hknd⟩ := hkeys
    isplitl [future Hreg3 HNMa HNMs]
    · isplitr; · ipureintro; rfl
      isplitl [future]; · iexists _; iframe
      iexists NM; iframe
      simp only [List.drop_zero]
      isplitr; · ipureintro; intro w; rw [hkm w]
      ihave HNMs := bigSepM_to_keys' (fun w _u => leaderNotifyEntry γ rc i s2.term vch w) keys NM hknd
        (fun k => hkm k) $$ HNMs
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ HNMs
      unfold leaderNotifyEntry
      iintro ⟨%u, -, %sv, %L, -, -, Hnm⟩; iexact Hnm
    isplitl []
    · imodintro
      iintro %n %w %u %m' ⟨%hk1, %hk2⟩ ⟨%hm', ⟨%fv, Hfut⟩, %NMr, Hreg, HNMa, %HNMr, Htoks⟩ Hntm
      subst m'
      have hjl : n < keys.length := (List.getElem?_eq_some_iff.mp hk1).1
      rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hk1).2]
      icases Htoks with ⟨Htok, Htoks⟩
      imod vreg_unnotify γ rc i w NMr $$ [Hreg HNMa Htok] with ⟨Hst, Hback⟩
      · iframe
      ihave ⟨%Q, HQ⟩ : (∃ Q : GoInterface → IProp GF,
          (deferResp (w.[verifyFuture, go!"deferError"]) Q ∗ Q eLL) ∨
            deferDone (w.[verifyFuture, go!"deferError"])) $$ [Hst]
      · icases Hst with (⟨%sc, Hresp⟩ | Hd)
        · iexists (verifyQ γ rc i sc); ileft; iframe; unfold verifyQ; ileft; ipureintro; exact HeLLne
        · iexists (fun _ => iprop(True)); iright; iexact Hd
      wp_auto
      wp_apply (wp_verifyFuture_respond w Q eLL) $$ [$HQ] as Hdone
      ihave ⟨Hreg, HNMa⟩ := Hback $$ Hdone
      unfold forMapPostcondition
      iright; ileft
      isplit; · ipureintro; rfl
      iexists NM; iframe
      isplitr; · ipureintro; rfl
      ipureintro
      intro x
      have hnd' := hknd
      rw [← List.take_append_drop n keys, List.nodup_append] at hnd'
      have hdrop : keys.drop n = w :: keys.drop (n + 1) := by
        rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hk1).2]
      rw [hdrop, List.nodup_cons] at hnd'
      by_cases hxw : w = x
      · subst hxw; simp only [GMap.lookup_delete_iff, if_true, Option.isSome_none]
        constructor
        · intro h; cases h
        · intro h; exact absurd h hnd'.2.1.1
      · rw [show (GMap.delete w NMr) !! x = NMr !! x from GMap.lookup_delete_ne _ hxw, HNMr x, hdrop]
        simp only [List.mem_cons]
        constructor
        · rintro (h | h); · exact absurd h.symm hxw
          exact h
        · intro h; right; exact h
    isplitl []
    · imodintro
      iintro %n %key %m' ⟨%hk1, %hk2⟩ ⟨%hm', -⟩
      subst m'
      exact absurd ((hkm key).mp (List.mem_of_getElem? hk1)) (by rw [hk2]; simp)
    iintro %m' ⟨%hm', ⟨%v, Hfut⟩, %NMr, Hreg, HNMa, %HNMr, -⟩ Hntm
    have hNMr : NMr = ∅ := by
      apply GMap.ext; intro w
      have := HNMr w
      simp only [List.drop_length, List.not_mem_nil, iff_false] at this
      cases h : NMr.lookup w with
      | none => rfl
      | some _ => exfalso; apply this; show (NMr !! w).isSome = true; rw [show NMr !! w = NMr.lookup w from rfl, h]; rfl
    subst hNMr
    ihave #Hlocks := isRaft_locks r γ rc i $$ Hr
    unfold raftLocks rwLock
    icases Hlocks with ⟨-, ⟨%γp, #Hguard, -⟩, -⟩
    ihave #Himm := isRaft_imm r γ rc i $$ Hr
    unfold raftImm
    icases Himm with ⟨-, #HlocalID, #HlocalAddr, -⟩
    wp_auto
    wp_apply (sync.RWMutex.wp_Lock_guard _ (leaderLockP r)) $$ [] as ⟨Hlk, HP⟩
    · iframe #
    iunfold leaderLockP at HP
    icases HP with ⟨%la, %lid, Hla, Hlid⟩
    wp_auto
    wp_join iprop(∃ (a' : ServerAddress) (id' : ServerID),
        r.[Raft, go!"leaderAddr"] ↦ a' ∗ r.[Raft, go!"leaderID"] ↦ id' ∗ r_ptr ↦ r) with [Hla Hlid r]
      as ⟨%a', %id', Hla, Hlid, r⟩
    · wp_if_destruct
      · isplitr; · itrivial
        iexists _, _; iframe
      · isplitr; · itrivial
        iexists _, _; iframe
    wp_apply (sync.RWMutex.wp_Unlock_guard _ (leaderLockP r)) $$ [Hlk Hla Hlid]
    · iframe Hlk
      inext
      iunfold leaderLockP
      iexists a', id'
      iframe
    icombine Hlch Hlch3 gives %Hlcheq
    subst Hlcheq
    wp_apply (wp_overrideNotifyBool γl3 lch bs3 false) $$ [$Hlchan3 $Hlown3] as Hlown3
    · ipureintro; exact Hlcap3
    rw [decide_eq_true Hc.2.2.2.1]
    wp_auto
    iapply HΦ
    iframe
    isplitr [Hcc Hcm Hinfl Hrs Hnt Hsd HNMa]
    · iexists lch
      iframe #
      ipureintro; exact ⟨Hvm3, Ha3, Hcp3, Hli3, Hlcap3.1, by simp⟩
    unfold leaderStateAny
    iexists _, _, _, _, _, _
    iframe

end proof

end Perennial
