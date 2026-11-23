/-
Package `proxy`: `handleClientBatch` (`proxyclienthandler.go`): the batch is stored and queued;
when the pipeline is free, the next undecided slot `p` is issued (its init token, paid by the
batch's credit, goes to the pending slots) and a timer is started whose function sends
`ProposeRequestIndex{p}` (with the pending slot's ghost element) to the main loop.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunClientBatch

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

set_option hygiene false in
/-- Closing `ownQ` when no slot was issued (only `toBeProposed` grew). -/
local macro "rc_close_noissue" : tactic => `(tactic| (
  iapply HΦ
  iunfold ownQ
  iexists γs, cb, bm, ebm, rl, slots, L, c, lp, D, Bm, tb1, tbs ++ [b.id]
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hlp72
  iunfold ownProp
  iexists Pm, its, ts, tlp, bt
  iframe
  iframe #
  isplitr
  · iexists _hs2; itrivial
  ipureintro; exact ⟨HPm, Hts⟩))

theorem wp_handleClientBatch
    (wp_NTWC : NewTimerWithCancel_spec (GF := GF) (hG := hG))
    (wp_STF : SetTimeoutFuntion_spec (GF := GF) (hG := hG))
    (wp_Start : Start_spec (GF := GF) (hG := hG))
    (wp_gls : getLeaderSequence_spec (GF := GF) (hG := hG))
    (wp_glw : getLeaderWait_spec (GF := GF) (hG := hG))
    (wp_hdn : handleDecisionNotification_spec (GF := GF) (hG := hG)) :
    handleClientBatch_spec (GF := GF) (hG := hG) := by
  intro γ cf k pr γq v
  wp_start as ⟨#Hsh, Hown, Hreq⟩
  iunfold proxySharedDef at Hsh
  icases Hsh with ⟨%_hs, %_γs', %_cb', %_bm', %_ebm', #Hfacts, #Hconsts, -, #Hchans, -, -⟩
  iunfold sharedFacts at Hfacts
  icases Hfacts with ⟨%Hk, #Hcons, #Hsmri, -, #Hnil, #Hsp0, #Hconf⟩
  have Hok := Hk.1
  unfold QConf.ok at Hok
  ihave #Hconsts0 := Hconsts
  iunfold sharedConsts at Hconsts
  icases Hconsts with ⟨#Hname, #Hcode, #Hbsz, #Hpipe, #Hlm, #Hlt, #Hes, #Hnr⟩
  iunfold sharedChans at Hchans
  icases Hchans with ⟨-, -, -, -, #Hdecch⟩
  iunfold ownQ at Hown
  icases Hown with ⟨%γs, %cb, %bm, %ebm, %rl, %slots, %L, %c, %lp, %D, %Bm, %tb, %tbs,
    #Hcb, #Hst, #Hnilst, #Hbm, #Hebm, Hrl, Hsl, Hslcap, Hlog, Hsmr, Hlp, Hfront, %Hlp72,
    Htb, Htbs, Htbcap, Hids, Hdec, Hepo, Hprop⟩
  iunfold ownProp at Hprop
  icases Hprop with ⟨%Pm, %its, %ts, %tlp, %bt, Hpch, Hauth, Htoks, %HPm, Hits, Hts, %Hts,
    Htlp, #Hbt⟩
  iunfold cbReqP at Hreq
  icases Hreq with ⟨%b, %t, #Hrep, #Hreg, %Hbok, Hcred⟩
  icases Hpch with ⟨%_hs2, #Hpch⟩
  ihave #Hrep' := Hrep
  iunfold repCBVal at Hrep'
  icases Hrep' with ⟨%_ps, %Hvb, -⟩
  wp_auto
  wp_apply (store_add_proof γ γs cb v b) $$ [] as #Hhas
  · unfold isStore; iframe #; ipureintro; exact Hbok
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) [v.Id']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply wp_slice_append (V := GoString) _ _ _ _ (DFrac.own 1) $$ [$Htbs $Htbcap $Hlit]
    as %tb1 ⟨Htbs, Htbcap, -⟩
  ihave Hids := (BigSepL.bigSepL_snoc).2 $$ [$Hids]
  · iunfold idP; unfold storeHas; iframe Hhas; iexists b; iframe Hreg; ipureintro; exact ⟨Hbok, rfl⟩
  rw [Hvb.2]
  wp_apply time.wp_Now as %tn -
  wp_apply time.Time.wp_Sub as %d -
  wp_apply (time.Duration.wp_Microseconds d)
  wp_if_destruct
  · icases rc_smrP_c_acc $$ Hsmr with ⟨Hc, %Hsp, Hsmrc⟩
    wp_auto
    wp_if_destruct
    · ihave %HlenL := rc_log_len $$ Hlog
      ihave %Hrllen := ownSlice_len $$ Hsl
      wp_join iprop(∃ (p : w64), proposeIndex_ptr ↦ p ∗ rl ↦* slots ∗ logP γ γs cf slots L ∗
          pr_ptr ↦ pr ∗ pr.[Proxy, go!"replicatedLog"] ↦ rl ∗
          ⌜sint.Z lp + 1 ≤ sint.Z p ∧ (sint.Z p = sint.Z lp + 1 ∨ sint.Z p ≤ slots.length) ∧
            sint.Z p ≤ 601 ∧ sint.Z c < sint.Z p⌝ ∗
          (⌜sint.Z p = sint.Z lp + 1⌝ ∨ ∃ ids, decided γ (sint.Z p - 1) ids))
        at next with [proposeIndex Hsl Hlog pr Hrl] as ⟨%p, proposeIndex, Hsl, Hlog, pr, Hrl, %Hpx, Hpd⟩
      · ihave HI : (∃ (p : w64), "proposeIndex" ∷ proposeIndex_ptr ↦ p ∗
            "%Hp" ∷ ⌜sint.Z lp + 1 ≤ sint.Z p ∧ (sint.Z p = sint.Z lp + 1 ∨ sint.Z p ≤ slots.length) ∧
              sint.Z p ≤ 601⌝ ∗
            "Hpd" ∷ (⌜sint.Z p = sint.Z lp + 1⌝ ∨ ∃ ids, decided γ (sint.Z p - 1) ids) : IProp GF)
            $$ [proposeIndex]
        · iexists (lp + W64 1)
          iframe
          isplitr
          · ipureintro; word
          ileft; ipureintro; word
        wp_for HI
        wp_if_destruct
        · have Hplt : sint.nat p < slots.length := by word
          list_elem slots (sint.nat p) as s
          icases rc_log_slot γ γs cf slots L (sint.nat p) s Hs_lookup $$ Hlog with ⟨%o, %Ho, #Hod, Hlog⟩
          have Hb : 0 ≤ sint.Z p ∧ sint.Z p < sint.Z rl.len := ⟨by word, by word⟩
          icases ownSlice_elem_acc (sint.Z p) s rl _ slots (by word)
            (by rw [show (sint.Z p).toNat = sint.nat p by word]; exact Hs_lookup) $$ Hsl with ⟨Hel, Hsl⟩
          repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
          ihave Hsl := Hsl $$ Hel
          rw [list_set_lookup_self _ _ _ (by rw [show (sint.Z p).toNat = sint.nat p by word]; exact Hs_lookup)]
          rcases o with _ | ids
          · simp only [Ho.2, Option.isSome_none]
            cleanup_bool_decide
            wp_join_done
            iexists p
            iframe
            ipureintro
            refine ⟨Hp.1, Hp.2.1, Hp.2.2, ?_⟩
            by_cases hcp : sint.Z c < sint.Z p
            · exact hcp
            exfalso
            have h1 := Hsp.2.2.2 (sint.nat p - 1) (by have := Hsp.1; word)
            rw [show sint.nat p - 1 + 1 = sint.nat p by word, Ho.1] at h1
            cases h1
          · simp only [Ho.2, Option.isSome_some]
            simp only [_root_.decide_true, ↓reduceIte]
            wp_auto
            wp_for_post
            iframe
            iexists (p + W64 1)
            iframe
            isplitr
            · ipureintro; have := Hsp.2.2.1; word
            iright
            iexists ids
            rw [show sint.Z (p + W64 1) - 1 = ((sint.nat p : Nat) : Int) by word]
            iapply Hod
            ipureintro; exact ⟨rfl, by word⟩
        · wp_join_done
          iexists p
          iframe
          ipureintro
          refine ⟨Hp.1, Hp.2.1, Hp.2.2, ?_⟩
          have := Hsp.1; have := Hsp.2.1; word
      -- issue slot `p`
      ihave ⟨%ids0, Hpd⟩ : (∃ ids0 : List GoString, ⌜sint.Z p = sint.Z lp + 1⌝ ∨
          decided γ (sint.Z p - 1) ids0 : IProp GF) $$ [Hpd]
      · icases Hpd with (%Hpe | ⟨%ids0, #Hd0⟩)
        · iexists []; ileft; ipureintro; exact Hpe
        · iexists ids0; iright; iexact Hd0
      imod (rc_issue γ (k : Int) (sint.Z lp + 1) (sint.Z p) t ids0 Hpx.1)
        $$ Hcons Hsp0 Hfront Hcred Hpd with ⟨Hfront, Htok, %Hp72⟩
      have Hfresh : Pm !! (sint.Z p) = none := by
        cases h : Pm !! sint.Z p with
        | none => rfl
        | some u => have := HPm.1 _ (by rw [h]; rfl); omega
      imod (ghost_map_insert (sint.Z p) () Hfresh) $$ Hauth with ⟨Hauth, Hq⟩
      ihave Htoks := (BigSepM.bigSepM_insert (Φ := fun j (_ : Unit) => initTok (GF := GF) γ k j)
        (show PartialMap.get? Pm (sint.Z p) = none from Hfresh)).2 $$ [$Htok $Htoks]
      -- the leader's wait
      wp_apply (wp_gls γ γs cf k pr p rl slots L) $$ [Hrl Hsl Hlog]
        as %sl %q ⟨Hseq, %Hq, -, Hlogrd⟩
      · iframe #; iunfold logRd; iframe; ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2, by word, by word⟩
      iunfold logRd at Hlogrd
      icases Hlogrd with ⟨Hrl, Hsl, Hlog⟩
      wp_apply (wp_glw cf k pr sl q) $$ [$Hseq]
      · iframe #; ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2, Hq⟩
      iintro ⟨%Hqi, -⟩
      wp_auto
      wp_if_destruct
      · exfalso
        have h0 := rc_msWait_nonneg p c cf.tmo (q.idxOf k) (by omega) (by omega)
          (by have := Hsp.1; omega) Hpx.2.2.1 Hpx.2.2.2
        word
      ihave %Htslen := ownSlice_len $$ Hts
      have Hpts : sint.nat p < ts.length := by word
      list_elem ts (sint.nat p) as tp
      have Htp : tp = null := by
        by_cases h : tp = null
        · exact h
        · have := Hts.2 _ _ Htp_lookup h; word
      subst Htp
      have Hbt : 0 ≤ sint.Z p ∧ sint.Z p < sint.Z its.len := ⟨by word, by word⟩
      icases ownSlice_elem_acc (sint.Z p) null its _ ts (by word)
        (by rw [show (sint.Z p).toNat = sint.nat p by word]; exact Htp_lookup) $$ Hts with ⟨Htel, Hts⟩
      repeat' (first | wp_auto | simp only [Hbt, _root_.and_self, ↓reduceIte])
      wp_apply (wp_NTWC _) as %tm Htm
      repeat' (first | wp_auto | simp only [Hbt, _root_.and_self, ↓reduceIte])
      ipersist pr
      ipersist proposeIndex
      wp_apply (wp_STF tm _ _ _) $$ [$Htm] as Htm
      simp only [Hbt, _root_.and_self, ↓reduceIte]
      wp_auto
      iunfold chanField at Hpch
      icases Hpch with ⟨%qch, %γqc, #Hqf, #Hqbag⟩
      wp_apply (wp_Start tm _ _) $$ [$Htm Hq]
      · iintro %Φ' HΦ'
        wp_auto
        wp_apply wp_bag_send $$ [Hqbag Hq]
        · iframe Hqbag; iunfold reqIdxP; iexact Hq
        iexact HΦ'
      iintro -
      wp_auto
      wp_join with [Hdec]
      · wp_apply (wp_hdn γ pr) $$ [$Hdec] as Hdec
        · iframe Hdecch
        wp_join_done
      wp_apply time.wp_Now as %tn2 -
      ihave Hsmr := Hsmrc $$ Hc
      ihave Hts := Hts $$ Htel
      iapply HΦ
      iunfold ownQ
      iexists γs, cb, bm, ebm, rl, slots, L, c, p, D, Bm, tb1, tbs ++ [b.id]
      iframe
      iframe #
      isplitr
      · ipureintro; exact ⟨by omega, Hp72.2⟩
      iunfold ownProp
      iexists Pm.insert (sint.Z p) (), its, ts.set (sint.Z p).toNat tm, tn2, bt
      iframe
      iframe #
      isplitr
      · iexists _hs2; iunfold chanField; iexists qch, γqc; iframe #
      have Hpure := rc_issue_pure Pm ts tm (sint.Z lp) (sint.Z p) slots.length HPm Hts Hlp72.1 Hpx.1 Hpx.2.1
      isplitr
      · ipureintro; exact Hpure.1
      ipureintro; exact Hpure.2
    · ihave Hsmr := Hsmrc $$ Hc
      rc_close_noissue
  · rc_close_noissue

end proofs

end Perennial.raxos
