/-
Package `proxy`: the specs of the small methods the decision handlers call: `hasSameBatches`,
`decidedTheProposedValue` (some answer: either is safe), `getHighestIndex` (the maximum of a
nonempty slice), `updateEpochTime` (leader mode 1: returns at once).
-/
module

public import Dsverify.Proof.raxos.Proxy.RunSmrHelpers
public import Dsverify.Proof.raxos.Proxy.RunRemove
public import Dsverify.Proof.raxos.Proxy.MabLeader

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
variable [ha : hyp.AtoiHyp GF]

attribute [local instance] HeapGS.goose_globalGS

theorem rd_wp_hasSameBatches (pr : Loc) (a1 a2 : GoSlice) (l1 l2 : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ a1 ↦*□ l1 ∗ a2 ↦*□ l2 }}
      (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"hasSameBatches")) (Val #a1))
        (Val #a2))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as ⟨#H1, #H2⟩
  wp_auto
  ihave %Hl1 := ownSlice_len $$ H1
  ihave %Hl2 := ownSlice_len $$ H2
  wp_if_destruct
  rotate_left
  · wp_end
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a1.len⌝ : IProp GF)
    $$ [i]
  · iexists W64 0; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hlt1 : sint.nat i < l1.length := by word
    have Hlt2 : sint.nat i < l2.length := by word
    list_elem l1 (sint.nat i) as x1
    list_elem l2 (sint.nat i) as x2
    have Hb1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a1.len := ⟨Hi.1, Hif⟩
    have Hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a2.len := ⟨Hi.1, by word⟩
    repeat' (first | wp_auto | simp only [Hb1, Hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index a1 (sint.Z i) l1 _ x1 Hi.1 $$ [H1] as -
    · iframe H1; ipureintro; simpa using Hx1_lookup
    repeat' (first | wp_auto | simp only [Hb1, Hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index a2 (sint.Z i) l2 _ x2 Hi.1 $$ [H2] as -
    · iframe H2; ipureintro; simpa using Hx2_lookup
    wp_if_destruct <;>
    first
    | (wp_for_post; wp_end; done)
    | (wp_for_post; iframe; iexists i + W64 1; iframe; ipureintro; word)
  · wp_end

theorem rd_wp_decidedTheProposedValue (pr : Loc) (rl : GoSlice) (slots : List Slot) (i : w64)
    (s : Slot) (pids : List GoString) (dsl : GoSlice) (ids : List GoString)
    (hi : 0 ≤ sint.Z i) (hs : slots[sint.nat i]? = some s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ pr.[Proxy, go!"replicatedLog"] ↦ rl ∗
        rl ↦* slots ∗ s.proposedBatch' ↦*□ pids ∗ dsl ↦*□ ids }}
      (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"decidedTheProposedValue"))
        (Val #i)) (Val #dsl))
    {{ (b : Bool), RET #b; pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots }} := by
  wp_start as ⟨Hrl, Hsl, #Hp, #Hd⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rl.len := ⟨hi, by
    have := (List.getElem?_eq_some_iff.1 hs).1; word⟩
  have hs' : slots[(sint.Z i).toNat]? = some s := by simpa using hs
  icases ownSlice_elem_acc (sint.Z i) s rl _ slots hi hs' $$ Hsl with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  wp_if_destruct
  · ihave Hsl := Hsl $$ Hel
    rw [list_set_lookup_self _ _ _ hs']
    wp_end
  · repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave Hsl := Hsl $$ Hel
    rw [list_set_lookup_self _ _ _ hs']
    wp_apply rd_wp_hasSameBatches pr s.proposedBatch' dsl pids ids $$ [] as %b -
    · iframe Hp Hd
    wp_if_destruct <;> wp_end

theorem rd_wp_getHighestIndex (pr : Loc) (sl : GoSlice) (is : List w64) (hne : is ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sl ↦*□ is }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"getHighestIndex")) (Val #sl))
    {{ (h : w64), RET #h; ⌜h ∈ is ∧ ∀ x ∈ is, sint.Z x ≤ sint.Z h⌝ }} := by
  wp_start as #Hs
  wp_auto
  ihave %Hl := ownSlice_len $$ Hs
  obtain ⟨x0, Hx0⟩ : ∃ x0, is[0]? = some x0 := by
    cases is with
    | nil => exact absurd rfl hne
    | cons a _ => exact ⟨a, rfl⟩
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have : 0 < is.length := List.length_pos_iff.2 hne
    constructor <;> word
  repeat' (first | wp_auto | simp only [Hb0, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) is _ x0 (by decide) $$ [Hs] as -
  · iframe Hs; ipureintro; simpa using Hx0
  ihave HI : (∃ (i h : w64), "i" ∷ i_ptr ↦ i ∗ "highest" ∷ highest_ptr ↦ h ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧ h ∈ is ∧
        ∀ x ∈ is.take (sint.nat i), sint.Z x ≤ sint.Z h⌝ : IProp GF) $$ [i highest]
  · iexists W64 0, x0; iframe
    ipureintro
    refine ⟨by word, by word, List.mem_of_getElem? Hx0, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_if_destruct
  · try simp at Hif
    have Hlt : sint.nat i < is.length := by word
    list_elem is (sint.nat i) as x
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, Hif⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z i) is _ x Hi.1 $$ [Hs] as -
    · iframe Hs; ipureintro; simpa using Hx_lookup
    have Htake : is.take (sint.nat (i + W64 1)) = is.take (sint.nat i) ++ [x] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      exact take_succ_of_getElem? _ _ _ Hx_lookup
    wp_if_destruct
    · repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index sl (sint.Z i) is _ x Hi.1 $$ [Hs] as -
      · iframe Hs; ipureintro; simpa using Hx_lookup
      wp_for_post
      iframe
      iexists i + W64 1, x
      iframe
      ipureintro
      refine ⟨by word, by word, List.mem_of_getElem? Hx_lookup, ?_⟩
      rw [Htake]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · have := Hi.2.2.2 y hy; omega
      · simp at hy; subst hy; omega
    · wp_for_post
      iframe
      iexists i + W64 1, h
      iframe
      ipureintro
      refine ⟨by word, by word, Hi.2.2.1, ?_⟩
      rw [Htake]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact Hi.2.2.2 y hy
      · simp at hy; subst hy; omega
  · have Hin : sint.nat i = is.length := by word
    rw [Hin, List.take_length] at Hi
    wp_end
    ipureintro; exact ⟨Hi.2.2.1, Hi.2.2.2⟩

/-- `pr.putBackProposedBatches(i)` (Q7): slot `i`'s proposed ids back to `toBeProposed`, but at
a summary slot (its proposal is an epoch summary, not a client batch). -/
theorem rd_wp_putBack (γ : QNames) (γs : GName) (cf : QConf) (k : Nat)
    (pr : Loc) (rl : GoSlice) (slots : List Slot) (i : w64) (s : Slot) (pids : List GoString)
    (hc : cf.ok) (hi : 0 ≤ sint.Z i ∧ sint.Z i ≤ 100000) (hs : slots[sint.nat i]? = some s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts cf k pr ∗
        pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots ∗ rd_tbP γ γs pr ∗
        s.proposedBatch' ↦*□ pids ∗
        (if decide (sumSlot cf.n cf.ep (sint.Z i)) then iprop(True) else [∗list] x ∈ pids, idP γ γs x) }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"putBackProposedBatches")) (Val #i))
    {{ RET #(); pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots ∗ rd_tbP γ γs pr }} := by
  wp_start as ⟨#Hc, Hrl, Hsl, Htbp, #Hp, Hids⟩
  ihave #Hc2 := Hc
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨-, -, -, -, #Hlm, -, -, -⟩
  wp_auto
  wp_apply (wp_isBeginningOfEpoch cf k pr i) $$ []
  · iframe #; ipureintro; exact ⟨hc, hi⟩
  wp_if_destruct
  · iapply HΦ; iframe
  iunfold rd_tbP at Htbp
  icases Htbp with ⟨%tb1, %tbs1, Htbf, Htb, Htbcap, #Hids1⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rl.len := ⟨hi.1, by
    have := (List.getElem?_eq_some_iff.1 hs).1; word⟩
  icases ownSlice_elem_acc (sint.Z i) s rl _ slots hi.1 (by simpa using hs) $$ Hsl with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  wp_apply (wp_slice_append (V := GoString) tb1 tbs1 s.proposedBatch' pids DFrac.discard)
    $$ [$Htb $Htbcap $Hp] as %tb' ⟨Htb, Htbcap, -⟩
  ihave Hsl := Hsl $$ Hel
  rw [list_set_lookup_self _ _ _ (by simpa using hs)]
  iapply HΦ
  iframe Hrl Hsl
  iunfold rd_tbP
  iexists tb', tbs1 ++ pids
  iframe Htbf Htb Htbcap
  iapply BigSepL.bigSepL_append.2
  iframe Hids1 Hids

end proofs

end Perennial.raxos
