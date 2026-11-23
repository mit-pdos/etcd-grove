/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Base.lean`, run `rabia-r1wake-1`.)

Shared definitions and lemmas of the ledger's proofs: the packages a proof calls into, the
sorting of the tallies (`SortRecvProposals`), the lock's critical sections.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Tallies
public import Dsverify.Proof.rabia.internal.ledger.Pure
public import Perennial.Proof.sync
public import Perennial.Proof.sort

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

set_option linter.unusedSectionVars false

/-! ### The configuration's bounds (stage 2) -/

/-- A configuration `choose` can pick has phase arrays of 2..10 entries. -/
theorem blockLen_ok {cf : RCfg} (hc : cf.Ok) : 1 ≤ cf.blockLen ∧ cf.blockLen ≤ 10 := by
  obtain ⟨-, -, -, hb⟩ := hc
  unfold RCfg.blockLen
  rcases cf with ⟨n, f, ba, bm, bl⟩
  simp only at hb ⊢
  obtain _ | _ | _ | _ | bl := bl <;> first | decide | omega

/-- A configuration `choose` can pick has a quorum of at most 4. -/
theorem q_ok {cf : RCfg} (hc : cf.Ok) : cf.q ≤ 4 := by
  obtain ⟨h, -⟩ := hc
  unfold RCfg.q
  omega

/-! ### The executor's `MyBCMsgs` -/

theorem getD_append_replicate {α : Type} (l : List α) (k i : Nat) (d : α) :
    (l ++ List.replicate k d).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rfl
  · rw [List.getElem?_eq_none (by omega : l.length ≤ i)]
    simp only [List.getElem?_replicate]
    split <;> rfl

theorem myRel_setMy (pv : PrivSt) (vs' : List (GoArray w32 2)) (phase round : Nat) (x : w32)
    (hr : round = 1 ∨ round = 2)
    (h1 : ∀ i (h : i < vs'.length), vs'[i] = encMy (pv.myBC.getD i (0, 0)))
    (h2 : pv.myBC.length ≤ vs'.length) (hp : phase < vs'.length) (hlt : vs'.length < 2 ^ 32) :
    myRel (pv.setMy phase round x).myBC
      (vs'.set phase (array.mk 2 ((encMy (pv.myBC.getD phase (0, 0))).arr.set (round - 1) x))) := by
  unfold PrivSt.setMy myRel
  simp only [List.length_set, List.length_modify, List.length_append, List.length_replicate]
  refine ⟨by omega, hlt, ?_⟩
  intro i h
  have hL : ∀ j : Nat, (pv.myBC ++ List.replicate (phase + 1 - pv.myBC.length)
      ((0 : w32), (0 : w32)))[j]?.getD ((0 : w32), (0 : w32)) =
      pv.myBC[j]?.getD ((0 : w32), (0 : w32)) := by
    intro j; rw [← List.getD_eq_getElem?_getD, getD_append_replicate, List.getD_eq_getElem?_getD]
  simp only [List.getD_eq_getElem?_getD] at h1 ⊢
  rw [List.getElem_set, List.getElem?_modify]
  by_cases hi : phase = i
  · subst hi
    simp only [↓reduceIte]
    have hlt' : phase < (pv.myBC ++ List.replicate (phase + 1 - pv.myBC.length) (0, 0)).length := by
      simp; omega
    have hp' := hL phase
    rw [List.getElem?_eq_getElem hlt'] at hp' ⊢
    simp only [Option.getD_some] at hp'
    simp only [Option.map_eq_map, Option.map_some, Option.getD_some, hp']
    unfold encMy
    rcases hr with rfl | rfl <;> rfl
  · simp only [hi, ↓reduceIte, Option.map_eq_map, Option.map_id_fun', id]
    rw [hL, h1 i h]

theorem W64_succ (n : Nat) : W64 (n + 1 : Nat) = W64 n + W64 1 := by
  word

theorem encT_incr0 (bcT : List (Nat × Nat)) (t0 : Nat × Nat) (h : bcT[0]? = some t0) :
    (bcT.map encT).set 0 (array.mk 2 ((encT t0).arr.set 0 (W64 t0.1 + W64 1))) =
      (bcT.modify 0 (fun p => (p.1 + 1, p.2))).map encT := by
  apply List.ext_getElem?; intro k
  rw [List.getElem?_set, List.getElem?_map, List.getElem?_map, List.getElem?_modify]
  by_cases hk : 0 = k
  · subst hk
    have hl : 0 < (bcT.map encT).length := by
      simp; exact (List.getElem?_eq_some_iff.1 h).1
    simp only [↓reduceIte, hl, h]
    simp [encT]
    word
  · simp [hk, List.getElem?_map]

/-- Count `x` of `c`. -/
def Counts.get (x : Nat) (c : Counts) : Nat := if x = 0 then c.1 else if x = 1 then c.2.1 else c.2.2

theorem encT_incr (T : List (Nat × Nat)) (p r : Nat) (t : Nat × Nat) (hr : r = 1 ∨ r = 2)
    (h : T[p]? = some t) :
    (T.map encT).set p (array.mk 2 ((encT t).arr.set (r - 1)
        (W64 ((if r = 1 then t.1 else t.2 : Nat) : Int) + W64 1))) =
      (T.modify p (incT r)).map encT := by
  apply List.ext_getElem?; intro k
  rw [List.getElem?_set, List.getElem?_map, List.getElem?_map, List.getElem?_modify]
  by_cases hk : p = k
  · subst hk
    have hl : p < (T.map encT).length := by simp; exact (List.getElem?_eq_some_iff.1 h).1
    simp only [↓reduceIte, hl, h, Option.map_eq_map, Option.map_some]
    rcases hr with rfl | rfl <;> simp [encT, incT] <;> word
  · simp [hk]

theorem encBC_incr (B : List (Counts × Counts)) (p r x : Nat) (c : Counts × Counts)
    (hr : r = 1 ∨ r = 2) (hx : x ≤ 2) (h : B[p]? = some c) :
    (B.map encBC).set p (array.mk 2 ((encBC c).arr.set (r - 1)
        (array.mk 3 ((encC (if r = 1 then c.1 else c.2)).arr.set x
          (W64 ((Counts.get x (if r = 1 then c.1 else c.2) : Nat) : Int) + W64 1))))) =
      (B.modify p (incBC r x)).map encBC := by
  apply List.ext_getElem?; intro k
  rw [List.getElem?_set, List.getElem?_map, List.getElem?_map, List.getElem?_modify]
  by_cases hk : p = k
  · subst hk
    have hl : p < (B.map encBC).length := by simp; exact (List.getElem?_eq_some_iff.1 h).1
    simp only [↓reduceIte, hl, h, Option.map_eq_map, Option.map_some]
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases hr with rfl | rfl <;> rcases hx' with rfl | rfl | rfl <;>
      simp [encBC, encC, incBC, incC, Counts.get] <;> word
  · simp [hk]

/-! ### The well-formedness of the shared state -/

theorem SlotSt.total01_ok (st : SlotSt) (h : st.wf) : cntOk (st.total 0 1) := by
  obtain ⟨-, -, -, -, h5, h6, h7, -⟩ := h
  unfold SlotSt.total
  rcases hb : st.bcT[0]? with _ | ⟨t1, t2⟩
  · simp
  · simp only [↓reduceIte]
    exact (h5 _ (List.mem_of_getElem? hb)).1

theorem SlotSt.wf_distinct (st : SlotSt) (h : st.wf) : distinctIds st.props := h.1

theorem SlotSt.wf_props_cnt (st : SlotSt) (h : st.wf) : ∀ x ∈ st.props, cntOk x.2 := by
  intro x hx
  have := st.total01_ok h
  have := h.2.1 x hx
  unfold cntOk at *; omega

theorem SlotSt.wf_props_len (st : SlotSt) (h : st.wf) : st.props.length ≤ 2 ^ 62 := by
  have := st.total01_ok h
  have := h.2.2.1
  unfold cntOk at *; omega

theorem SlotSt.wf_sort (st : SlotSt) (h : st.wf) :
    ({ st with props := sortProps st.props } : SlotSt).wf := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp := List.mergeSort_perm st.props tallyLt
  refine ⟨distinctIds_perm h1 hp.symm, ?_, ?_, h4⟩
  · intro t ht
    exact h2 t (hp.subset ht)
  · simp only [sortProps, List.length_mergeSort]; exact h3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

/-- The ledger's initialization includes that of the packages it calls into (`sync`, `sort`,
`message`): the run's instance's dependency part. -/
abbrev LedgerDeps : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ⊢
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message

theorem decRep_of_objRep (dec : ConsensusObj) (o : ObjV) :
    objRep (GF := GF) dec o ⊢ decRep dec true o := by
  unfold decRep; exact .rfl

theorem decRep_elim (dec : ConsensusObj) (b : Bool) (o : ObjV) :
    decRep (GF := GF) dec b o ⊢ if b = true then objRep dec o else iprop(True) := by
  unfold decRep; exact .rfl

/-- An element of an array element of a slice. -/
theorem slice_array_acc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {n : Int}
    (s : GoSlice) (dq : DFrac) (vs : List (GoArray V n)) (i j : Int) (a : GoArray V n) (v : V)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (ha : vs[i.toNat]? = some a) (hv : a.arr[j.toNat]? = some v) :
    (s ↦*{dq} vs : IProp GF) ⊢ typedPointsto (arrayIndexRef V j (sliceIndexRef (GoArray V n) i s)) v dq ∗
      (∀ v', typedPointsto (arrayIndexRef V j (sliceIndexRef (GoArray V n) i s)) v' dq -∗
        s ↦*{dq} vs.set i.toNat (array.mk n (a.arr.set j.toNat v'))) := by
  iintro Hs
  icases ownSlice_elem_acc i a s dq vs hi ha $$ Hs with ⟨Ha, Hs⟩
  icases array_acc (sliceIndexRef _ i s) j dq n a v hj hv $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro %v' Hv'
  iapply Hs
  iapply Ha $$ Hv'

/-- An element of an array element of an array element of a slice. -/
theorem slice_array2_acc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {n m : Int}
    (s : GoSlice) (dq : DFrac) (vs : List (GoArray (GoArray V m) n)) (i j k : Int)
    (a : GoArray (GoArray V m) n) (b : GoArray V m) (v : V)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hk : 0 ≤ k) (ha : vs[i.toNat]? = some a)
    (hb : a.arr[j.toNat]? = some b) (hv : b.arr[k.toNat]? = some v) :
    (s ↦*{dq} vs : IProp GF) ⊢
      typedPointsto (arrayIndexRef V k (arrayIndexRef (GoArray V m) j
        (sliceIndexRef (GoArray (GoArray V m) n) i s))) v dq ∗
      (∀ v', typedPointsto (arrayIndexRef V k (arrayIndexRef (GoArray V m) j
          (sliceIndexRef (GoArray (GoArray V m) n) i s))) v' dq -∗
        s ↦*{dq} vs.set i.toNat (array.mk n (a.arr.set j.toNat (array.mk m (b.arr.set k.toNat v'))))) := by
  iintro Hs
  icases slice_array_acc s dq vs i j a b hi hj ha hb $$ Hs with ⟨Hb, Hs⟩
  icases array_acc _ k dq m b v hk hv $$ Hb with ⟨Hv, Hb⟩
  iframe Hv
  iintro %v' Hv'
  iapply Hs
  iapply Hb $$ Hv'

/-- Reading an element of an array points-to. -/
theorem array_read {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {n : Int} (p : Loc)
    (i : Int) (dq : DFrac) (a : GoArray V n) (v : V) (hi : 0 ≤ i) (hv : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢ typedPointsto (arrayIndexRef V i p) v dq ∗
      (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq) := by
  iintro Ha
  icases array_acc p i dq n a v hi hv $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ Hv
  rw [list_set_lookup_self _ _ _ hv]
  iexact Ha

theorem decRep_false (dec : ConsensusObj) (o : ObjV) : ⊢ decRep (GF := GF) dec false o := by
  unfold decRep; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

theorem talliesRep_nil : ⊢ talliesRep (GF := GF) [] [] := by
  unfold talliesRep
  isplitr
  · ipureintro; rfl
  · iintro !> %i %t %x %h; simp at h

/-- The zero object holds the default object (unfolds `message.objRep`: a missing law of
`message`, the zero object's representation). -/
theorem objRep_zero : ⊢ objRep (GF := GF) (Perennial.zero_val ConsensusObj) default := by
  unfold objRep
  rw [show (Perennial.zero_val ConsensusObj).CliIds' = slice.nil from rfl,
    show (Perennial.zero_val ConsensusObj).CliSeqs' = slice.nil from rfl,
    show (Perennial.zero_val ConsensusObj).Commands' = slice.nil from rfl,
    show (default : ObjV).cliIds = [] from rfl, show (default : ObjV).cliSeqs = [] from rfl,
    show (default : ObjV).commands = [] from rfl]
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSlice_nil
  · iapply ownSlice_nil

theorem ledgerDeps : LedgerDeps (GF := GF) := by
  iintro #H
  isplitr
  · iPkgInit
  isplitr
  · iPkgInit
  · iPkgInit

theorem Slot.wp_SortRecvProposals (wp_Lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG))
    (s : Loc) (ps : GoSlice) (xs : List (ObjV × Nat)) (hd : distinctIds xs)
    (hl : xs.length ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        structFieldRef Slot go!"RecvProposals" s ↦ ps ∗ ownTallies ps xs }}
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"SortRecvProposals")) (Val #()))
    {{ RET #(); structFieldRef Slot go!"RecvProposals" s ↦ ps ∗ ownTallies ps (sortProps xs) }} := by
  wp_start as ⟨Hps, Hown⟩
  wp_auto
  ihave #Hsrt := tallies_isSorter wp_Lt ps $$ []
  · iPkgInit
  wp_apply sort.wp_Sort (interface.mk tallies.ty #ps) (ownTallies ps)
    (fun a b => tallyLt a b = true) tallyLt_swo xs $$ [$Hsrt $Hown] as %xs' ⟨Hown, %Hperm, %Hsorted⟩
  · ipureintro; exact hl
  rw [sortProps_eq xs xs' hd Hperm Hsorted]
  iapply HΦ
  iframe Hps Hown

end proof
end Perennial.rabia.internal.ledger
