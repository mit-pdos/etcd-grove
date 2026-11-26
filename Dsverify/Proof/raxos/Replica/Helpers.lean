/-
Package `replica`: the recorder's small helpers (`findAllBatches`,
`convertToClientBatchMessages`, `convertToDecideResponseClientBatchMessages`).
-/
module

public import Dsverify.Proof.raxos.Replica.ReqPersist
public import Dsverify.Proof.raxos.Proxy.Store

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]


set_option goose.wp.extras true

theorem wp_findAllBatches (γ : QNames) (k : Nat) (re : Loc) (ids : GoSlice) (xs : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isRecorder γ k re ∗ ids ↦*□ xs }}
      (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"findAllBatches")) (Val #ids))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as ⟨#Hre, #Hids⟩
  iunfold isRecorder at Hre
  icases Hre with ⟨%cb, %γs, %ch, %γc, %mu, #Hcb, #Hst, -⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hids
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · list_elem xs (sint.nat i) as x
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ids.len from ⟨Hi, by simpa using Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index ids (sint.Z i) xs _ x Hi $$ [] as -
    · iframe #; ipureintro; exact Hx_lookup
    wp_apply store_get_proof γ γs cb x false $$ [$Hst] as %v %ok ⟨-, -⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    cases ok <;> wp_auto
    · wp_for_post
      iapply HΦ; itrivial
    · wp_for_post
      iframe
      iexists _; iframe; ipureintro; word
  · iapply HΦ; itrivial

theorem wp_convertToClientBatchMessages (re : Loc) (msl : GoSlice) (ps : List Loc)
    (cmds : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ msl ↦*□ ps ∗
        repList repPMSingle ps .discard cmds }}
      (App (Val (re @!! go.GoType.PointerType Recorder.ty @!! go!"convertToClientBatchMessages"))
        (Val #msl))
    {{ (ra : GoSlice), RET #ra; ∃ qs, ra ↦* qs ∗ repList repCSingle qs .discard cmds }} := by
  wp_start as ⟨#Hms, #Hrep⟩
  ihave %Hlen := ownSlice_len $$ Hms
  ihave %Hlc : ⌜ps.length = cmds.length⌝ $$ []
  · iunfold repList at Hrep; icases Hrep with ⟨%H, -⟩; ipureintro; exact H
  wp_auto
  wp_apply (wp_slice_make2 (V := Loc) _) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; word
  ihave HI : (∃ (i : w64) (zs : List Loc), "i" ∷ i_ptr ↦ i ∗ "Hsl" ∷ sl ↦* zs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z msl.len ∧ zs.length = ps.length⌝ ∗
      "#Hpre" ∷ repList repCSingle (zs.take (sint.nat i)) .discard (cmds.take (sint.nat i)) :
      IProp GF) $$ [i Hsl]
  · iexists _, _
    iframe
    isplitr
    · ipureintro; simp only [List.length_replicate]; refine ⟨by word, by word, by word⟩
    · simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; iapply repList_nil
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z msl.len := ⟨Hi.1, by simpa [goose_wp_simp_extra] using Hif⟩
    list_elem ps (sint.nat i) as q
    list_elem cmds (sint.nat i) as c
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z i) ps _ q Hi.1 $$ [] as -
    · iframe #; ipureintro; exact Hq_lookup
    ihave #Hq : repPMSingle q .discard c $$ []
    · iunfold repList at Hrep
      icases Hrep with ⟨-, Hs⟩
      ihave Hx := BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ y, ⌜cmds[i]? = some y⌝ ∗
        repPMSingle p DFrac.discard y)) Hq_lookup $$ Hs
      icases Hx with ⟨%y, %Hy, Hx⟩
      rw [Hc_lookup] at Hy; cases Hy; iexact Hx
    iunfold repPMSingle at Hq
    icases Hq with ⟨%xq, #Hxq, %Hxm⟩
    wp_auto
    irename «$r0» => Hnq
    generalize «$r0_ptr» = nq at *
    imod ptCSingle_share ⊤ _ _ ?st $$ Hnq with #Hnq
    case st => exact stateOk_zero _
    ihave %Hlen2 := ownSlice_len $$ Hsl
    have Hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, by have := Hi.2.2; word⟩
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index sl (sint.Z i) zs nq $$ [Hsl] as Hsl
    · iframe; ipureintro; refine ⟨Hi.1, by word⟩
    wp_for_post
    iframe
    iexists _, _
    iframe
    isplitr
    · ipureintro; simp only [List.length_set]; refine ⟨by word, by word, Hi.2.2⟩
    · rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, List.take_add_one,
        List.getElem?_set_self (by word), Hc_lookup]
      simp only [Option.toList_some]
      rw [show (List.take (sint.nat i) (zs.set (sint.Z i).toNat nq)) = List.take (sint.nat i) zs by
        rw [List.take_set]; exact List.set_eq_of_length_le (by simp; word)]
      iapply repList_snoc $$ [$Hpre]
      unfold repCSingle
      iexists _; iframe #; ipureintro; exact ⟨rfl, Hxm.2⟩
  · iapply HΦ
    iexists zs; iframe
    have e1 : zs.take (sint.nat i) = zs := List.take_of_length_le (by word)
    have e2 : cmds.take (sint.nat i) = cmds := List.take_of_length_le (by word)
    have e3 : repList (GF := GF) repCSingle zs .discard cmds =
        repList repCSingle (zs.take (sint.nat i)) .discard (cmds.take (sint.nat i)) := by
      rw [e1, e2]
    rw [e3]
    iexact Hpre

end proof

end Perennial.raxos
