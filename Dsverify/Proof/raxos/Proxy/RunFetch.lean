/-
Package `proxy`: `handleFetchResponse` (`proxysmrhandler.go`): the fetched batches go to the
store, then the state machine is updated (answers sent).
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDefs

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

instance rf_batchesP_persistent (γ : QNames) (vs : List raxos.proto.client.ClientBatch)
    (bs : List Batch) : Persistent (batchesP (GF := GF) γ vs bs) := by
  unfold batchesP; infer_instance

theorem wp_handleFetchResponse : handleFetchResponse_spec (GF := GF) (hG := hG) := by
  intro γ cf k pr γq m
  wp_start as ⟨#Hsh, Hown, Hm⟩
  iunfold fetchRespP at Hm
  icases Hm with ⟨%vs, %bs, #Hvs, #Hbs⟩
  iunfold batchesP at Hbs
  icases Hbs with ⟨%Hbs, #Hbs⟩
  iunfold ownQ at Hown
  icases Hown with ⟨%γs, %cb, %bm, %ebm, %rl, %slots, %L, %c, %lp, %D, %Bm, %tb, %tbs,
    #Hcb, #Hst, #Hnil, #Hbm, #Hebm, Hrl, Hsl, Hrlcap, Hlog, Hsmr, Hlp, Hfront, %Hlpb, Htb, Htbs,
    Htbcap, Hidps, Hdec, Hepo, Hprop⟩
  ihave %Hvslen := ownSlice_len $$ Hvs
  iunfold logP at Hlog
  icases Hlog with ⟨%Hlen0, Hlog⟩
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z m.batches'.len⌝ : IProp GF) $$ [i]
  · iexists W64 0; iframe; ipureintro; exact ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have Hilt : sint.nat i < vs.length := by word
    list_elem vs (sint.nat i) as v
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m.batches'.len := ⟨Hi.1, Hif⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index m.batches' (sint.Z i) vs _ v Hi.1 $$ [Hvs] as -
    · iframe Hvs; ipureintro; simpa using Hv_lookup
    ihave Hel := BigSepL.bigSepL_lookup Hv_lookup $$ Hbs
    icases Hel with ⟨%b, %Hb', #Hrep, #Hreg⟩
    have Hbok : batchFit b := Hbs.2 b (List.mem_of_getElem? Hb')
    wp_apply (store_add_proof γ γs cb v b) $$ [Hst Hrep Hreg] as -
    · unfold isStore; iframe Hst Hrep Hreg; ipureintro; exact Hbok
    wp_for_post
    iframe
    iexists i + W64 1
    iframe
    ipureintro; exact ⟨by word, by word⟩
  · ihave #Hus := usmShared_of γ cf k pr γs cb bm ebm $$ Hsh Hcb Hst Hbm Hebm
    wp_apply (wp_updateStateMachine γ γs cf pr cb bm ebm true rl slots L c D Bm) $$ [Hus Hrl Hsl Hlog Hsmr]
      as ⟨%slots', %c', %D', %Bm', Hrl, Hsl, Hlog, Hsmr⟩
    · iframe Hus Hrl Hsl Hsmr
      iunfold logP; iframe Hlog; ipureintro; exact Hlen0
    iunfold logP at Hlog
    icases Hlog with ⟨%Hlen', Hlog⟩
    have Hl : slots'.length = slots.length := by rw [Hlen', Hlen0]
    iapply HΦ
    iunfold ownQ
    iexists γs, cb, bm, ebm, rl, slots', L, c', lp, D', Bm', tb, tbs
    rw [Hl]
    iframe Hcb Hst Hnil Hbm Hebm Hrl Hsl Hrlcap Hsmr Hlp Hfront Htb Htbs Htbcap Hidps Hdec Hepo Hprop
    isplitl [Hlog]
    · iunfold logP; iframe Hlog; ipureintro; exact Hlen'
    ipureintro; exact Hlpb
end proofs

end Perennial.raxos
