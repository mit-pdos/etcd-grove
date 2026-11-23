/-
Package `proxy`: `updateStateMachine` (`proxysmrhandler.go`), the riskiest step: it executes the
decided slots after the committed index, in order, each once every id of the slot is in the
store (else it asks for the missing batches and stops); each slot's execution is
`smr_exec_slot`'s, and its answers are sent.
-/
module

public import Dsverify.Proof.raxos.Proxy.SmrGhost

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

/-- What `updateStateMachine` reads of the proxy, for good (persistent). -/
def usmShared (γ : QNames) (γs : GName) (pr cb bm ebm : Loc) : IProp GF :=
  iprop(∃ (fch och : Loc) (γf γo : ChanNames),
    inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ batchReg γ go!"nil" nilBatch ∗
    pr.[Proxy, go!"clientBatchStore"] ↦□ cb ∗ isStore γ γs cb ∗
    pr.[Proxy, go!"benchmark"] ↦□ bm ∗ pr.[Proxy, go!"executedBatches"] ↦□ ebm ∗
    pr.[Proxy, go!"proxyToProposerFetchChan"] ↦□ fch ∗ isChanBag γf fch fetchReqP ∗
    pr.[Proxy, go!"outgoingMessageChan"] ↦□ och ∗ isChanBag γo och (outP γ) ∗
    pr.[Proxy, go!"clientBatchRpc"] ↦□ W8 1)

instance usmShared_persistent (γ : QNames) (γs : GName) (pr cb bm ebm : Loc) :
    Persistent (usmShared (GF := GF) γ γs pr cb bm ebm) := by
  unfold usmShared; infer_instance

theorem wp_updateStateMachine (γ : QNames) (γs : GName) (cf : QConf) (pr cb bm ebm : Loc) (sendResponse : Bool)
    (rl : GoSlice) (slots : List Slot) (L : List (Option (List GoString))) (c : w64)
    (D : List (List GoString)) (Bm : GMap GoString Batch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ usmShared γ γs pr cb bm ebm ∗
        pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots ∗ logP γ γs cf slots L ∗
        smrP γ pr bm ebm L c D Bm }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"updateStateMachine")) (Val #sendResponse))
    {{ RET #(); ∃ (slots' : List Slot) (c' : w64) (D' : List (List GoString)) (Bm' : GMap GoString Batch),
        pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots' ∗ logP γ γs cf slots' L ∗
        smrP γ pr bm ebm L c' D' Bm' }} := by
  wp_start as ⟨#Hsh, Hrl, Hsl, Hlog, Hsmr⟩
  iunfold usmShared at Hsh
  icases Hsh with ⟨%fch, %och, %γf, %γo, #Hcons, #Hsmri, #Hnil, #Hcb, #Hst, #Hbm, #Hebm, #Hfch, #Hfbag,
    #Hoch, #Hobag, #Hcode⟩
  iunfold smrP at Hsmr
  icases Hsmr with ⟨%E, %t, Hc, Ht, %Hpure, #Hlb, Hkv, Hm, %HE, #Hknown, %Hpure2⟩
  wp_auto
  ihave HI : (∃ (c' : w64) (slots' : List Slot) (D' : List (List GoString)) (Bm' : GMap GoString Batch),
      "i" ∷ i_ptr ↦ (c' + W64 1) ∗ "Hsl" ∷ rl ↦* slots' ∗ "Hlog" ∷ logP γ γs cf slots' L ∗
      "Hsmr" ∷ smrP γ pr bm ebm L c' D' Bm' : IProp GF) $$ [i Hsl Hlog Hc Ht Hkv Hm]
  · iexists c, slots, D, Bm
    iframe i Hsl Hlog
    iunfold smrP
    iexists E, t
    iframe Hc Ht Hkv Hm Hlb Hknown
    ipureintro; exact ⟨Hpure, HE, Hpure2⟩
  wp_for HI
  iunfold smrP at Hsmr
  icases Hsmr with ⟨%E, %t, Hc, Ht, %Hp, #Hlb, Hkv, Hm, %HE, #Hknown, %Hp2⟩
  iunfold logP at Hlog
  icases Hlog with ⟨%Hlen, Hlog⟩
  ihave %Hrllen := ownSlice_len $$ Hsl
  have Hn : sint.Z (c' + W64 1) = D'.length + 1 := by have := Hp.2.2.1; word
  wp_if_destruct
  · have Hnlt : D'.length + 1 < slots'.length := by word
    list_elem slots' (D'.length + 1) as s
    icases BigSepL.bigSepL_insert_acc Hs_lookup $$ Hlog with ⟨⟨%o, %Ho, Hslot⟩, Hlog⟩
    have Hb : 0 ≤ sint.Z (c' + W64 1) ∧ sint.Z (c' + W64 1) < sint.Z rl.len := ⟨by word, Hif⟩
    icases ownSlice_elem_acc (sint.Z (c' + W64 1)) s rl _ slots' (by word) (by rw [Hn]; simpa using Hs_lookup)
      $$ Hsl with ⟨Hel, Hsl⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    iunfold slotP at Hslot
    icases Hslot with ⟨%Hdec, Hslot⟩
    rcases o with _ | ids
    · -- not decided: stop
      simp only [Option.isSome_none] at Hdec
      rw [Hdec]
      wp_auto
      wp_for_post
      ihave Hsl := Hsl $$ Hel
      rw [list_set_lookup_self _ _ _ (by rw [Hn]; simpa using Hs_lookup)]
      ihave Hlog := Hlog $$ [Hslot]
      · iexists none
        isplitr
        · ipureintro; exact Ho
        iunfold slotP
        isplitr
        · ipureintro; simpa using Hdec
        iexact Hslot
      rw [list_set_lookup_self _ _ _ Hs_lookup]
      iapply HΦ
      iexists slots', c', D', Bm'
      iframe Hrl Hsl
      isplitl [Hlog]
      · iunfold logP; iframe Hlog; ipureintro; exact Hlen
      iunfold smrP
      iexists E, t
      iframe Hc Ht Hkv Hm Hlb Hknown
      ipureintro; exact ⟨Hp, HE, Hp2⟩
    · simp only [Option.isSome_some] at Hdec
      rw [Hdec]
      wp_auto
      icases Hslot with ⟨#Hids, %Hidsok, #Hdecided⟩
      have Hn0 : D'.length + 1 ≠ 0 := by omega
      simp only [Hn0, ↓reduceIte]
      ihave %Hidslen := ownSlice_len $$ Hids
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      have Hne : ¬ (s.decidedBatch'.len = W64 0) := by
        intro h; apply Hidsok.1; apply List.eq_nil_of_length_eq_zero; rw [Hidslen.1, h]; rfl
      simp only [Hne, decide_false, ↓reduceIte]
      wp_auto
      ihave HJ : (∃ (j : w64) (Bn : GMap GoString Batch),
          "j" ∷ j_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.decidedBatch'.len⌝ ∗
          "#HknownN" ∷ knownP γ Bn ∗
          "%HBn" ∷ ⌜(∀ y c, Bm' !! y = some c → Bn !! y = some c) ∧
            (∀ y c, Bn !! y = some c → ∀ m ∈ c.cmds, cmdOk m) ∧ (∀ y c, Bn !! y = some c → c.id = y) ∧
            ∀ x ∈ ids.take (sint.nat j), (Bn !! x).isSome⌝ ∗
          "#Hhas" ∷ [∗list] x ∈ ids.take (sint.nat j), storeHas γs x : IProp GF) $$ [j]
      · iexists W64 0, Bm'
        iframe j Hknown
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp only [List.take_zero]
        isplitr
        · ipureintro; exact ⟨by word, by word⟩
        isplitr
        · ipureintro; exact ⟨fun _ _ h => h, Hp2.1, Hp2.2.1, by simp⟩
        iapply BigSepL.bigSepL_nil.2; iempintro
      wp_for HJ
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      cleanup_bool_decide
      wp_if_destruct
      · have Hjlt : sint.nat j < ids.length := by word
        list_elem ids (sint.nat j) as x
        have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.decidedBatch'.len := ⟨Hj.1, Hif⟩
        repeat' (first | wp_auto | simp only [Hb, Hbj, _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index _ (sint.Z j) ids _ x Hj.1 $$ [Hids] as -
        · iframe Hids; ipureintro; simpa using Hx_lookup
        wp_apply (store_get_proof γ γs cb x false) $$ [Hst] as %v %ok ⟨-, Hv⟩
        · iframe Hst; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        cases ok
        · -- missing: fetch it, stop
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          repeat' (first | wp_auto | simp only [Hb, Hbj, _root_.and_self, ↓reduceIte])
          wp_apply wp_bag_send $$ [Hfbag]
          · iframe Hfbag
            iunfold fetchReqP
            iexists ids
            dsimp only
            iframe Hids
            ipureintro; exact Hidsok.2
          wp_for_post
          wp_for_post
          ihave Hsl := Hsl $$ Hel
          rw [list_set_lookup_self _ _ _ (by rw [Hn]; simpa using Hs_lookup)]
          ihave Hlog := Hlog $$ [Hids]
          · iexists some ids
            isplitr
            · ipureintro; exact Ho
            iunfold slotP
            isplitr
            · ipureintro; simpa using Hdec
            dsimp only
            iframe Hids
            isplitr
            · ipureintro; exact Hidsok
            simp only [Hn0, ↓reduceIte]
            iexact Hdecided
          rw [list_set_lookup_self _ _ _ Hs_lookup]
          iapply HΦ
          iexists slots', c', D', Bm'
          iframe Hrl Hsl
          isplitl [Hlog]
          · iunfold logP; iframe Hlog; ipureintro; exact Hlen
          iunfold smrP
          iexists E, t
          iframe Hc Ht Hkv Hm Hlb Hknown
          ipureintro; exact ⟨Hp, HE, Hp2⟩
        · -- in the store
          simp only [↓reduceIte, Bool.not_true]
          icases Hv with ⟨%b, %Hbx, -, #Hregx, #Hhasx⟩
          icases (known_extend γ Bn x b HBn.2.1 HBn.2.2.1 ⟨Hbx.2, Hbx.1⟩) $$ HknownN Hregx
            with ⟨%Bn', #HknownN', %HBn'⟩
          repeat' (first | wp_auto | simp only [Hb, Hbj, _root_.and_self, ↓reduceIte])
          wp_for_post
          iframe
          have Hjn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          iexists j + W64 1, Bn'
          rw [Hjn, take_succ_of_getElem? _ _ _ Hx_lookup]
          iframe HknownN' j
          isplitr
          · ipureintro; exact ⟨by word, by word⟩
          isplitr
          · ipureintro
            refine ⟨fun y c h => HBn'.1 y c (HBn.1 y c h), HBn'.2.2.1, HBn'.2.2.2, ?_⟩
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 (HBn.2.2.2 y hy)
              rw [HBn'.1 y c0 hc0]; rfl
            · simp at hy; subst hy; rw [HBn'.2.1]; rfl
          iapply BigSepL.bigSepL_append.2
          iframe Hhas
          iapply BigSepL.bigSepL_singleton.2
          iexact Hhasx
      · -- every id of the slot is in the store: execute it
        have Hjl : sint.nat j = ids.length := by word
        rw [Hjl, List.take_length] at HBn
        rw [Hjl, List.take_length]
        have Hcongr : execLog (fun x => Bm' !! x) D' = execLog (fun x => Bn !! x) D' := by
          apply px_execLog_congr
          intro x hx
          obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 (Hp2.2.2 x hx)
          rw [hc0, HBn.1 x c0 hc0]
        rw [Hcongr] at HE
        rw [Hcongr]
        repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
        wp_apply wp_executeClientBatches γ γs pr cb bm ebm s.decidedBatch' ids Bn _ E HE HBn.2.2.2
          HBn.2.1 HBn.2.2.1 $$ [Hm Hkv] as %rs %outs ⟨%E', Hm, %HE', Hkv, Hrs, Houts⟩
        · iframe Hcb Hst Hbm Hebm Hm Hkv Hids Hhas HknownN
        wp_apply (lc := 2) wp_time_Now as %tn _
        -- the ghost commit of the slot
        ipersist Hrs
        imod (bigSepL_bupd_mono outs _ (fun k o => iprop(∃ x b r,
            ⌜(freshIds (execLog (fun y => Bn !! y) D').done ids)[k]? = some x ∧ Bn !! x = some b ∧
              (execIds (fun y => Bn !! y) (execLog (fun y => Bn !! y) D') ids).results x = some r⌝ ∗
            repCBVal (GF := GF) o .discard ⟨x, b.sender, r⟩))
          (fun k o => by
            iintro ⟨%x, %b, %r, %H, Hr⟩
            imod repCBVal_persist $$ Hr with Hr
            imodintro
            iexists x, b, r
            iframe Hr
            ipureintro; exact H)) $$ Houts with Houts
        have Hdl : ((D'.length + 1 : Nat) : Int) = (D'.length : Int) + 1 := by push_cast; rfl
        rw [Hdl] at *
        imod (commit_ghost γ D' ids Bn outs (fun x hx => by
            rcases List.mem_flatten.1 hx with ⟨l, hl, hxl⟩
            rcases List.mem_append.1 hl with hl | hl
            · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 (Hp2.2.2 x (List.mem_flatten.2 ⟨l, hl, hxl⟩))
              rw [HBn.1 x c0 hc0]; rfl
            · simp at hl; subst hl; exact HBn.2.2.2 x hxl) HBn.2.2.1)
          $$ Hcons Hsmri [Hlc1 Hlc2] Hlb Hdecided HknownN Hnil Houts with ⟨#Hlb', #Hans⟩
        · iapply (lc_split (n := 1) (m := 1)).2; iframe Hlc1 Hlc2
        repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
        wp_apply (wp_slice_make2 (V := GoString)) as %ns ⟨Hns, -⟩
        · ipureintro; word
        repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
        ipersist Hns
        wp_if_destruct
        · wp_for_post
          have Hidx : (sint.Z (c' + W64 1)).toNat = D'.length + 1 := by rw [Hn]; omega
          ihave Hsl := Hsl $$ Hel
          ihave Hlog := Hlog $$ %(⟨ns, s.decidedBatch', s.decided', true, s.proposer', s.s'⟩ : Slot) [Hids Hdecided]
          · iexists some ids
            isplitr
            · ipureintro; exact Ho
            iunfold slotP
            isplitr
            · ipureintro; simpa using Hdec
            dsimp only
            iframe Hids
            isplitr
            · ipureintro; exact Hidsok
            simp only [Hn0, ↓reduceIte]
            rw [show ((D'.length + 1 : Nat) : Int) = (D'.length : Int) + 1 by push_cast; rfl]
            iexact Hdecided
          rw [Hidx]
          iframe
          iexists c' + W64 1, _, D' ++ [ids], Bn
          iframe i Hsl
          isplitl [Hlog]
          · iunfold logP
            simp only [named]
            isplitr
            · ipureintro; simp [Hlen]
            iexact Hlog
          iunfold smrP
          iexists E', tn
          rw [px_execLog_snoc]
          iframe Hc Ht Hkv Hm Hlb' HknownN
          ipureintro
          refine ⟨⟨by rw [Hn]; simp, by simp; omega, Hp.2.2.1, ?_⟩, HE', HBn.2.1, HBn.2.2.1, ?_⟩
          · intro k hk
            simp only [List.length_append, List.length_singleton] at hk
            by_cases hkD : k < D'.length
            · rw [Hp.2.2.2 k hkD, List.getElem_append_left hkD]
            · have : k = D'.length := by omega
              subst this
              rw [Ho]; simp
          · intro x hx
            rcases List.mem_flatten.1 hx with ⟨l, hl, hxl⟩
            rcases List.mem_append.1 hl with hl | hl
            · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 (Hp2.2.2 x (List.mem_flatten.2 ⟨l, hl, hxl⟩))
              rw [HBn.1 x c0 hc0]; rfl
            · simp at hl; subst hl; exact HBn.2.2.2 x hxl
        · wp_apply wp_sendClientResponse γ pr och γo rs outs $$ [Hans]
          · iframe Hoch Hobag Hcode Hrs Hans
          wp_for_post
          have Hidx : (sint.Z (c' + W64 1)).toNat = D'.length + 1 := by rw [Hn]; omega
          ihave Hsl := Hsl $$ Hel
          ihave Hlog := Hlog $$ %(⟨ns, s.decidedBatch', s.decided', true, s.proposer', s.s'⟩ : Slot) [Hids Hdecided]
          · iexists some ids
            isplitr
            · ipureintro; exact Ho
            iunfold slotP
            isplitr
            · ipureintro; simpa using Hdec
            dsimp only
            iframe Hids
            isplitr
            · ipureintro; exact Hidsok
            simp only [Hn0, ↓reduceIte]
            rw [show ((D'.length + 1 : Nat) : Int) = (D'.length : Int) + 1 by push_cast; rfl]
            iexact Hdecided
          rw [Hidx]
          iframe
          iexists c' + W64 1, _, D' ++ [ids], Bn
          iframe i Hsl
          isplitl [Hlog]
          · iunfold logP
            simp only [named]
            isplitr
            · ipureintro; simp [Hlen]
            iexact Hlog
          iunfold smrP
          iexists E', tn
          rw [px_execLog_snoc]
          iframe Hc Ht Hkv Hm Hlb' HknownN
          ipureintro
          refine ⟨⟨by rw [Hn]; simp, by simp; omega, Hp.2.2.1, ?_⟩, HE', HBn.2.1, HBn.2.2.1, ?_⟩
          · intro k hk
            simp only [List.length_append, List.length_singleton] at hk
            by_cases hkD : k < D'.length
            · rw [Hp.2.2.2 k hkD, List.getElem_append_left hkD]
            · have : k = D'.length := by omega
              subst this
              rw [Ho]; simp
          · intro x hx
            rcases List.mem_flatten.1 hx with ⟨l, hl, hxl⟩
            rcases List.mem_append.1 hl with hl | hl
            · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 (Hp2.2.2 x (List.mem_flatten.2 ⟨l, hl, hxl⟩))
              rw [HBn.1 x c0 hc0]; rfl
            · simp at hl; subst hl; exact HBn.2.2.2 x hxl
  · iapply HΦ
    iexists slots', c', D', Bm'
    iframe Hrl Hsl
    isplitl [Hlog]
    · iunfold logP; iframe Hlog; ipureintro; exact Hlen
    iunfold smrP
    iexists E, t
    iframe Hc Ht Hkv Hm Hlb Hknown
    ipureintro; exact ⟨Hp, HE, Hp2⟩

end proofs
end Perennial.raxos
