/-
Package `proxy`: `proposeToIndex` (`proxyclienthandler.go`): a timer's request to propose a
pending slot `i` (its ghost element `reqIdxP`): the slot's init token is taken from the pending
map; if the slot is decided already, nothing; else a batch of `toBeProposed` (or `"nil"`) is
proposed with `cons_init`, the log is extended to the slot, which records the proposed ids.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunSummary

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
variable [ha : hyp.AtoiSpec GF]

attribute [local instance] HeapGS.goose_globalGS

theorem wp_proposeToIndex
    (wp_sum : proposeSummary_spec (GF := GF) (hG := hG)) :
    proposeToIndex_spec (GF := GF) (hG := hG) := fun γ cf k pr γq i => by
  wp_start as ⟨#Hsh, Hown, Hel⟩
  iunfold proxySharedDef at Hsh
  icases Hsh with ⟨%_hs, %_γs', %_cb', %_bm', %_ebm', #Hfacts, #Hconsts, -, #Hchans, -, -⟩
  iunfold sharedFacts at Hfacts
  icases Hfacts with ⟨%Hk, #Hcons, #Hsmri, -, #Hnilreg, #Hsp0, #Hconf⟩
  have Hok := Hk.1
  unfold QConf.ok at Hok
  ihave #Hc2 := Hconsts
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨-, -, #Hbsz, -, #Hlm, -, -, -⟩
  iunfold sharedChans at Hchans
  icases Hchans with ⟨-, -, #Hpch0, -, -⟩
  ihave #Hpch := Hpch0
  iunfold chanField at Hpch
  icases Hpch with ⟨%pch, %γp, #Hpchf, #Hpbag⟩
  iunfold ownQ at Hown
  icases Hown with ⟨%γs, %cb, %bm, %ebm, %rl, %slots, %L, %c, %lp, %D, %Bm, %tb, %tbs, #Hcb, #Hst,
    #Hnilst, #Hbm, #Hebm, Hrl, Hsl, Hslcap, Hlog, Hsmr, Hlp, Hfr, %Hlpb, Htb, Htbs, Htbcap, #Hids,
    Hdec, Hepo, Hprop⟩
  iunfold ownProp at Hprop
  icases Hprop with ⟨%Pm, %its, %ts, %tlp, %bt, #Hrqch, Hauth, Htoks, %HPm, Hits, Hts, %Hts,
    Htlp, #Hbt⟩
  iunfold reqIdxP at Hel
  ihave %HiPm := ghost_map_lookup $$ Hauth Hel
  have Hib := HPm.1 (sint.Z i) (by simp [HiPm])
  icases (BigSepM.bigSepM_delete (Φ := fun j (_ : Unit) => initTok (GF := GF) γ k j)
    (show PartialMap.get? Pm (sint.Z i) = some () from HiPm)).1 $$ Htoks with ⟨Htok, Htoks⟩
  imod ghost_map_delete $$ Hauth Hel with Hauth
  wp_auto
  ihave %Hrllen := ownSlice_len $$ Hsl
  iunfold logP at Hlog
  icases Hlog with ⟨%HlenL, Hlog⟩
  -- whether the slot is decided already
  wp_join (Q := fun v => iprop("Hsl" ∷ rl ↦* slots ∗ "Hrl" ∷ pr.[Proxy, go!"replicatedLog"] ↦ rl ∗
      "pr" ∷ pr_ptr ↦ pr ∗ "proposeIndex" ∷ proposeIndex_ptr ↦ i ∗
      (⌜v = executeVal ∧ ¬ (sint.Z i < sint.Z rl.len ∧ ∃ s, slots[sint.nat i]? = some s ∧ s.decided' = true)⌝ ∨
       ⌜v = returnVal #() ∧ sint.Z i < sint.Z rl.len ∧ ∃ s, slots[sint.nat i]? = some s ∧ s.decided' = true⌝)))
    with [Hsl Hrl pr proposeIndex]
  · have Hilt : sint.nat i < slots.length := by word
    list_elem slots (sint.nat i) as s
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rl.len := ⟨by word, Hif⟩
    icases ownSlice_elem_acc (sint.Z i) s rl _ slots Hb.1 (by simpa using Hs_lookup) $$ Hsl
      with ⟨Hel, Hsl⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave Hsl := Hsl $$ Hel
    rw [list_set_lookup_self _ _ _ (by simpa using Hs_lookup)]
    wp_if_destruct
    · iframe
      iright
      ipureintro
      exact ⟨trivial, trivial, s, Hs_lookup, Hif⟩
    · iframe
      ileft
      ipureintro
      refine ⟨trivial, ?_⟩
      rintro ⟨-, s', Hs', Hd⟩
      rw [Hs_lookup] at Hs'; cases Hs'; exact Hif Hd
  · iframe
    ileft
    ipureintro
    refine ⟨trivial, ?_⟩
    rintro ⟨h, -⟩; exact Hif h
  rename_i v
  iintro ⟨Hsl, Hrl, pr, proposeIndex, (%Hc | %Hc)⟩
  rotate_left
  · -- decided already: return
    obtain ⟨rfl, Hlt, -⟩ := Hc
    wp_auto
    iapply HΦ
    iunfold ownQ
    iexists γs, cb, bm, ebm, rl, slots, L, c, lp, D, Bm, tb, tbs
    iframe #
    iframe
    isplitl [Hlog]
    · iunfold logP; iframe Hlog; ipureintro; exact HlenL
    isplitr
    · ipureintro; exact Hlpb
    iunfold ownProp
    iexists GMap.delete (sint.Z i) Pm, its, ts, tlp, bt
    iframe #
    iframe
    ipureintro
    exact ⟨rp_pm_delete Pm (sint.Z lp) slots.length slots.length (sint.Z i) HPm (Nat.le_refl _) (by rw [Hrllen.1]; word), Hts⟩
  obtain ⟨rfl, Hnd⟩ := Hc
  wp_auto
  ihave %Hitslen := ownSlice_len $$ Hts
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z its.len := ⟨by word, by have := Hts.1; word⟩
  simp only [Hbi, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index $$ [Hts] as Hts
  · iframe Hts; ipureintro; exact ⟨Hbi.1, by have := Hts.1; word⟩
  -- leader mode 2: an epoch's first slot from epoch `2n` on proposes the summary
  wp_apply (wp_isBeginningOfEpoch cf k pr i) $$ []
  · iframe #; ipureintro; exact ⟨Hk.1, by word, by word⟩
  wp_if_destruct
  · have Hss : sumSlot cf.n cf.ep (sint.Z i) := Hif
    have wp_sum' := wp_sum
    unfold proposeSummary_spec at wp_sum'
    wp_apply (wp_sum' γ γs cf k pr i rl slots L)
      $$ [Htok Hrl Hsl Hlog Hslcap Hepo Hdec]
      as ⟨%rl', %slots', %m, Hlogrd, Hslcap, %Hm, Hepo, Hdec⟩
    · iframe #
      iframe
      isplitr
      · ipureintro
        refine ⟨Hk.1, Hk.2.1, Hk.2.2, Hss, Hib.1, by omega, fun h => Hnd ⟨by word, h.2⟩⟩
      iunfold logRd; iframe; iunfold logP; iframe; ipureintro; exact HlenL
    clear wp_sum'
    iunfold logRd at Hlogrd
    icases Hlogrd with ⟨Hrl, Hsl, Hlog⟩
    ihave %HlenL' := rp_log_len γ γs cf slots' (L ++ List.replicate m none) $$ Hlog
    iapply HΦ
    iunfold ownQ
    iexists γs, cb, bm, ebm, rl', slots', L ++ List.replicate m none, c, lp, D, Bm, tb, tbs
    iframe #
    iframe
    isplitl [Hsmr]
    · iapply rp_smrP_ext (m := m) (h := Hm.1.imp id (fun h => by rw [← HlenL]; word)) $$ Hsmr
    isplitr
    · ipureintro; exact Hlpb
    iunfold ownProp
    iexists GMap.delete (sint.Z i) Pm, its, ts.set (sint.Z i).toNat null, tlp, bt
    iframe #
    iframe
    ipureintro
    refine ⟨rp_pm_delete Pm (sint.Z lp) slots.length _ (sint.Z i) HPm
      (by rw [HlenL', HlenL]; simp) (by have := Hm.2; word), rp_ts_set ts _ _ Hts⟩
  have Hns : decide (sumSlot cf.n cf.ep (sint.Z i)) = false := decide_eq_false Hif
  clear Hif
  ihave %Htblen := ownSlice_len $$ Htbs
  wp_join iprop(∃ bsz : w64, "batchSize" ∷ batchSize_ptr ↦ bsz ∗ "pr" ∷ pr_ptr ↦ pr ∗
      "Htb" ∷ pr.[Proxy, go!"toBeProposed"] ↦ tb ∗
      "%Hbsz" ∷ ⌜sint.Z bsz = min (sint.Z tb.len) 50⌝) with [batchSize pr Htb]
    as ⟨%bsz, batchSize, pr, Htb, %Hbsz⟩
  · iexists _; iframe; ipureintro; word
  · iexists _; iframe; ipureintro; word
  wp_apply (wp_slice_make2 (V := GoString)) as %sp0 ⟨Hsp0, -⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := raxos.proto.client.ClientBatch)) as %bp0 ⟨Hbp0, Hbp0cap⟩
  · ipureintro; word
  wp_join iprop(∃ (sp bp tb' : GoSlice) (ids tbs' : List GoString)
      (vs : List raxos.proto.client.ClientBatch) (bs : List Batch),
      "strProposals" ∷ strProposals_ptr ↦ sp ∗ "#Hsp" ∷ sp ↦*□ ids ∗
      "btchProposals" ∷ btchProposals_ptr ↦ bp ∗ "Hbp" ∷ bp ↦* vs ∗
      "#Hbatches" ∷ batchesP γ vs bs ∗ "%Hbs" ∷ ⌜bs.map Batch.id = ids ∧ ids ≠ []⌝ ∗
      "#Hidsp" ∷ ([∗list] x ∈ ids, idP γ γs x) ∗
      "Htb" ∷ pr.[Proxy, go!"toBeProposed"] ↦ tb' ∗ "Htbs" ∷ tb' ↦* tbs' ∗
      "Htbcap" ∷ ownSliceCap GoString tb' (DFrac.own 1) ∗
      "#Hids" ∷ ([∗list] x ∈ tbs', idP γ γs x) ∗ "pr" ∷ pr_ptr ↦ pr)
    with [strProposals btchProposals Hbp0 Hbp0cap Htb Htbs Htbcap pr batchSize]
    as ⟨%sp, %bp, %tb', %ids, %tbs', %vs, %bs, strProposals, #Hsp, btchProposals, Hbp, #Hbatches,
      %Hbs, #Hidsp, Htb, Htbs, Htbcap, #Hids', pr⟩
  · -- nothing to propose: the "nil" batch
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoString) (t := go.string) [go!"nil"]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %spn ⟨Hspn, -⟩
    ipersist Hspn
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType raxos.proto.client.ClientBatch.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := raxos.proto.client.ClientBatch) (t := raxos.proto.client.ClientBatch.ty) [_]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := raxos.proto.client.ClientBatch) _ _ _ _ _ $$ [$Hbp0 $Hbp0cap $Hlit]
      as %bpn ⟨Hbpn, -, -⟩
    isplitr
    · ipureintro; rfl
    iexists _, bpn, tb, [go!"nil"], tbs, _, [nilBatch]
    iframe
    isplitr
    · iexact Hspn
    isplitr
    · iunfold batchesP
      isplitr
      · ipureintro; exact ⟨rfl, by simp [rp_nilBatch_ok]⟩
      simp only [List.replicate_zero, List.nil_append]
      iapply BigSepL.bigSepL_singleton.2
      iexists nilBatch
      isplitr
      · ipureintro; rfl
      isplitr
      · iunfold repCBVal
        iexists []
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        isplitr
        · iapply ownSlice_nil
        iunfold repList
        isplitr
        · ipureintro; rfl
        iapply BigSepL.bigSepL_nil.2; iempintro
      rw [show nilBatch.id = go!"nil" from rfl]
      iexact Hnilreg
    isplitr
    · ipureintro; exact ⟨rfl, by simp⟩
    isplitr
    · iapply BigSepL.bigSepL_singleton.2
      iunfold idP
      iframe Hnilst
      iexists nilBatch
      iframe Hnilreg
      ipureintro; exact ⟨rp_nilBatch_ok, rfl⟩
    iexact Hids
  · -- a batch of `toBeProposed`
    ihave %Htbwf := ownSliceCap_wf $$ Htbcap
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z bsz ∧ sint.Z bsz ≤ sint.Z tb.cap := by
      refine ⟨by word, by word, by word⟩
    simp only [Hb0, _root_.and_self, ↓reduceIte]
    wp_auto
    have Hb1 : 0 ≤ sint.Z bsz ∧ sint.Z bsz ≤ sint.Z tb.len ∧ sint.Z tb.len ≤ sint.Z tb.cap :=
      ⟨by word, by word, Htbwf.2⟩
    simp only [Hb1, _root_.and_self, ↓reduceIte]
    wp_auto
    icases (ownSlice_split_all bsz tb _ tbs ⟨Hb1.1, Hb1.2.1⟩).1 $$ Htbs with ⟨Hsp, Htbs⟩
    ihave Htbcap := (ownSliceCap_slice tb bsz _ Hb1).1 $$ Htbcap
    icases rp_bigSepL_take_drop (sint.nat bsz) tbs (fun x => idP (GF := GF) γ γs x) $$ Hids
      with ⟨#Hidsp, #Hidsr⟩
    ipersist Hsp
    wp_apply (wp_slice_make2 (V := raxos.proto.client.ClientBatch)) as %bp1 ⟨Hbp1, Hbp1cap⟩
    · ipureintro; word
    ihave %Hspl := ownSlice_len $$ Hsp
    ihave HI : (∃ (j : w64) (bp : GoSlice) (vs : List raxos.proto.client.ClientBatch) (bs : List Batch),
        "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z bsz⌝ ∗
        "btchProposals" ∷ btchProposals_ptr ↦ bp ∗ "Hbp" ∷ bp ↦* vs ∗
        "Hbpcap" ∷ ownSliceCap raxos.proto.client.ClientBatch bp (DFrac.own 1) ∗
        "#Hbatches" ∷ batchesP γ vs bs ∗ "%Hbs" ∷ ⌜bs.map Batch.id = (tbs.take (sint.nat bsz)).take (sint.nat j)⌝ : IProp GF)
        $$ [i btchProposals Hbp1 Hbp1cap]
    · iexists W64 0, bp1, [], []
      iframe
      isplitr
      · ipureintro; word
      isplitr
      · iunfold batchesP
        isplitr
        · ipureintro; simp
        iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; simp
    wp_for HI
    by_cases Hif : sint.Z j < sint.Z (bsz - W64 0)
    · simp only [decide_eq_true Hif, eq_self_iff_true, _root_.decide_true, ↓reduceIte]
      wp_auto
      have Hjl : sint.nat j < (tbs.take (sint.nat bsz)).length := by
        simp only [List.length_take]; word
      list_elem (tbs.take (sint.nat bsz)) (sint.nat j) as x
      ihave #Hx := BigSepL.bigSepL_lookup (Φ := fun _ y => idP (GF := GF) γ γs y) Hx_lookup $$ Hidsp
      iunfold idP at Hx
      icases Hx with ⟨#Hxs, %bx, #Hxreg, %Hxok⟩
      have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (bsz - W64 0) := ⟨Hj.1, Hif⟩
      simp only [Hbj, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ x Hj.1 $$ [Hsp] as -
      · iframe Hsp; ipureintro; simpa using Hx_lookup
      wp_apply (store_get_proof γ γs cb x true) $$ [Hst Hxs] as %v %ok ⟨%Hok, Hv⟩
      · unfold isStore storeHas; iframe Hst; simp only [↓reduceIte]; iexact Hxs
      obtain rfl : ok = true := Hok rfl
      simp only [↓reduceIte]
      icases Hv with ⟨%b, %Hb', #Hrepv, #Hregx, -⟩
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType raxos.proto.client.ClientBatch.ty))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := raxos.proto.client.ClientBatch) (t := raxos.proto.client.ClientBatch.ty) [v]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := raxos.proto.client.ClientBatch) _ _ _ _ _ $$ [$Hbp $Hbpcap $Hlit]
        as %bp' ⟨Hbp, Hbpcap, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, bp', vs ++ [v], bs ++ [b]
      iframe
      have Hjn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      isplitr
      · ipureintro; word
      isplitr
      · iapply rp_batchesP_snoc γ vs bs v b Hb'.2
        iframe Hbatches Hrepv
        rw [Hb'.1]; iexact Hregx
      ipureintro
      rw [Hjn, take_succ_of_getElem? _ _ _ Hx_lookup, List.map_append, Hbs]; simp [Hb'.1]
    · have hft : ((#false : val) = #true) = False :=
        propext ⟨fun h => Bool.false_ne_true (go.intoVal_inj h), False.elim⟩
      simp only [decide_eq_false Hif, hft, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
      try (simp only [eq_self_iff_true, _root_.decide_true, ↓reduceIte])
      have Hjb : sint.nat j = sint.nat bsz := by word
      have Hlt : sint.nat bsz ≤ tbs.length := by word
      have Hpos : 0 < sint.nat bsz := by word
      isplitr
      · ipureintro; trivial
      iexists _, bp, _, tbs.take (sint.nat bsz), tbs.drop (sint.nat bsz), vs, bs
      iframe
      isplitr
      · iexact Hsp
      isplitr
      · iexact Hbatches
      isplitr
      · ipureintro
        rw [Hjb, List.take_take, Nat.min_self] at Hbs
        refine ⟨Hbs, ?_⟩
        intro h
        have := congrArg List.length h
        simp only [List.length_take, List.length_nil] at this
        omega
      isplitr
      · iexact Hidsp
      iexact Hidsr
  -- the leader flag
  wp_apply (wp_getLeaderSequence γ γs cf k pr i rl slots L) $$ [Hrl Hsl Hlog]
    as %lsl %q ⟨Hlsl, %Hq, #Hld, Hlogrd⟩
  · iframe #; iunfold logRd; iframe Hrl Hsl; iunfold logP; iframe Hlog
    ipureintro; exact ⟨⟨Hk.1, Hk.2.1, Hk.2.2, by word, by word⟩, HlenL⟩
  iunfold logRd at Hlogrd
  icases Hlogrd with ⟨Hrl, Hsl, Hlog⟩
  iunfold logP at Hlog
  icases Hlog with ⟨-, Hlog⟩
  wp_apply (wp_getLeaderWait cf k pr lsl q) $$ [$Hlsl]
  · iframe #; ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2, Hq⟩
  iintro ⟨%Hqi, -⟩
  have Hfl := rp_flag cf k q Hk.1 ⟨Hk.2.1, Hk.2.2⟩ Hq
  wp_auto
  wp_join iprop(∃ bl : Bool, "isLeader" ∷ isLeader_ptr ↦ bl ∗ "pr" ∷ pr_ptr ↦ pr ∗
      "%Hbl" ∷ ⌜bl = decide (q.head? = some k)⌝) with [isLeader pr]
    as ⟨%bl, isLeader, pr, %Hbl⟩
  · iexists true; iframe; ipureintro; simp [Hfl.1 Hif]
  · iexists false; iframe; ipureintro; simp only [Bool.false_eq, decide_eq_false_iff_not]
    exact fun h => Hif (Hfl.2 h)
  -- the proposal: its init event, from the slot's token
  iunfold decState at Hdec
  icases Hdec with ⟨%ls, %ps, %ds, Hls, Hps, Hds, #Hdsp, Hlscap, Hpscap, Hdscap⟩
  subst Hbl
  imod (rs_cons_init γ cf (k : Int) (sint.Z i) ids (decide (q.head? = some k)) Hk.1 Hbs.2
    (fun h => absurd (decide_eq_true h) (by rw [Hns]; simp))) $$ Hcons Hconf Htok Hld [] with #Hinit
  · iapply BigSepL.bigSepL_impl $$ Hidsp
    imodintro
    iintro %n %x %_ Hx
    iunfold idP at Hx
    icases Hx with ⟨-, %b, Hb, -⟩
    iexists b; iexact Hb
  ipersist Hbp
  wp_load
  wp_auto
  wp_apply wp_bag_send $$ [Hpbag]
  · iframe Hpbag
    iunfold proposeReqP
    iexists ids, vs, bs
    dsimp only
    iframe #
    ipureintro; exact Hbs.1
  -- extend the log to the slot
  ihave HI : (∃ (rl' : GoSlice) (m : Nat),
      "Hrl" ∷ pr.[Proxy, go!"replicatedLog"] ↦ rl' ∗ "Hsl" ∷ rl' ↦* (slots ++ List.replicate m rp_s0) ∗
      "Hslcap" ∷ ownSliceCap Slot rl' (DFrac.own 1) ∗
      "Hlog" ∷ ([∗list] j ↦ s ∈ slots ++ List.replicate m rp_s0,
        ∃ o, ⌜(L ++ List.replicate m none)[j]? = some o⌝ ∗ slotP γ γs cf j s o) ∗
      "%Hm" ∷ ⌜m = 0 ∨ slots.length + m ≤ sint.nat i + 1⌝ : IProp GF) $$ [Hrl Hsl Hslcap Hlog]
  · iexists rl, 0
    simp only [List.replicate_zero, List.append_nil]
    iframe
    ipureintro; simp
  wp_for HI
  ihave %Hsl'len := ownSlice_len $$ Hsl
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Slot.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Slot) (t := Slot.ty) [rp_s0]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := Slot) _ _ _ _ _ $$ [$Hsl $Hslcap $Hlit] as %rl'' ⟨Hsl, Hslcap, -⟩
    wp_for_post
    iframe
    iexists rl'', m + 1
    rw [List.replicate_succ', ← List.append_assoc, List.replicate_succ', ← List.append_assoc]
    iframe
    isplitl [Hlog]
    · iapply BigSepL.bigSepL_append.2
      isplitl [Hlog]
      · iapply BigSepL.bigSepL_impl $$ Hlog
        imodintro
        iintro %j %s0 %hj ⟨%o, %Ho, Hs⟩
        iexists o
        iframe Hs
        ipureintro
        have := (List.getElem?_eq_some_iff.1 hj).1
        simp only [List.length_append, List.length_replicate] at this
        rw [List.getElem?_append_left (by simp [← HlenL]; omega)]
        exact Ho
      iapply BigSepL.bigSepL_singleton.2
      iexists none
      isplitr
      · ipureintro
        simp only [Nat.zero_add, List.length_append, List.length_replicate]
        rw [List.getElem?_append_right (by simp [HlenL])]
        simp [HlenL]
      iapply rp_slotP_s0
    ipureintro
    right
    simp only [List.length_append, List.length_replicate] at Hsl'len
    word
  -- the slot records the proposed ids
  simp only [List.length_append, List.length_replicate] at Hsl'len
  have Hil : sint.nat i < (slots ++ List.replicate m rp_s0).length := by
    simp only [List.length_append, List.length_replicate]; word
  list_elem (slots ++ List.replicate m rp_s0) (sint.nat i) as sx
  have Hsxd := rp_slot_undecided slots m (sint.nat i) sx Hsx_lookup
    (fun h => Hnd ⟨by have := h.1; rw [Hrllen.1] at this; word, h.2⟩)
  icases BigSepL.bigSepL_insert_acc Hsx_lookup $$ Hlog with ⟨⟨%o, %Ho, Hslot⟩, Hlog⟩
  iunfold slotP at Hslot
  icases Hslot with ⟨%Hod, -⟩
  have Hon : o = none := by
    cases o with
    | none => rfl
    | some _ => rw [Hsxd] at Hod; simp at Hod
  subst Hon
  have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rl'.len := ⟨by word, by word⟩
  icases ownSlice_elem_acc (sint.Z i) sx rl' _ _ Hb.1 (by simpa using Hsx_lookup) $$ Hsl
    with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  wp_apply (wp_slice_make2 (V := w64)) as %ls' ⟨Hls', Hls'cap⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w32)) as %ps' ⟨Hps', Hps'cap⟩
  · ipureintro; word
  wp_apply +noauto (wp_slice_make2 (V := GoSlice)) as %ds' ⟨Hds', Hds'cap⟩
  · ipureintro; word
  ipersist Hls'
  ipersist Hps'
  ipersist Hds'
  wp_auto
  ihave Hsl := Hsl $$ Hel
  ihave Hlog := Hlog $$ %(Slot.mk sp sx.decidedBatch' sx.decided' sx.committed' 0 0) [Hsp]
  · iexists none
    isplitr
    · ipureintro; exact Ho
    iunfold slotP
    isplitr
    · ipureintro; simpa using Hsxd
    iexists ids
    iframe Hsp
    rw [show ((sint.nat i : Nat) : Int) = sint.Z i by word, Hns]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hidsp
  iapply HΦ
  iunfold ownQ
  iexists γs, cb, bm, ebm, rl', _, L ++ List.replicate m none, c, lp, D, Bm, tb', tbs'
  iframe #
  iframe
  isplitl [Hlog]
  · iunfold logP
    isplitr
    · ipureintro; simp [HlenL]
    iexact Hlog
  isplitl [Hsmr]
  · iapply rp_smrP_ext (m := m) (h := Hm.imp id (fun h => by rw [← HlenL]; word)) $$ Hsmr
  isplitr
  · ipureintro; exact Hlpb
  isplitl [Hls Hps Hds Hls'cap Hps'cap Hds'cap]
  · iunfold decState
    iexists ls', ps', ds'
    iframe
    iunfold decidedSlotsP
    iexists List.replicate 0 (zero_val w64), List.replicate 0 (zero_val w32),
      List.replicate 0 (zero_val GoSlice), []
    isplitr
    · iexact Hls'
    isplitr
    · iexact Hps'
    isplitr
    · iexact Hds'
    isplitr
    · ipureintro; simp
    iapply BigSepL.bigSepL_nil.2; iempintro
  iunfold ownProp
  iexists GMap.delete (sint.Z i) Pm, its, ts.set (sint.Z i).toNat null, tlp, bt
  iframe #
  iframe
  ipureintro
  refine ⟨rp_pm_delete Pm (sint.Z lp) slots.length _ (sint.Z i) HPm (by simp) (by simp; word),
    rp_ts_set ts _ _ Hts⟩

end proofs

end Perennial.raxos
