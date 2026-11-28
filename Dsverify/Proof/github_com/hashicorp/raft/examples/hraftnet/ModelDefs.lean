/-
`Model()` (kit.go) against the register's porcupine model spec `regS`, and `Gen`'s spec (notes/dsv-hraft.md,
S5e), as craq's `craqnet/ModelDefs.lean`: the state's helpers `pushPend`, `findPend`, `erasePend` over
read-only slices of values, `step` (`wp_step`: `goStep` of the decoded answer, `ModelSet.lean`), `regDec`
on boxed values (`regDec_box`), `Model.spec`, `Gen.spec`; and the store's decoding facts remote's `Check`
needs (`regS_pendDec`, `regR_encOut_inj`). `KitProof.lean` proves `Model.wp_proof` and `Gen.wp_proof`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ModelSet
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.KitCodecDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## porcupine's model -/

section model
variable [GooseExts] [GoGlobalContext]

/-- An answer `Out{u, f, w}`, decoded: unknown is an error, else the output `(f, w)`. -/
def decAns (u f : Bool) (w : Str8) : Ans HOut := if u then .err else .ok ⟨(f, w.1), w.2⟩

open Classical in
/-- porcupine's operations as the store's: a boxed input and a boxed bounded `Out`; anything else
decodes to nothing. -/
def regDec (io : OpV) : Option (HIn × Ans HOut) :=
  if h : ∃ (i : HIn) (u f : Bool) (w : Str8), io = (inV i.1, outVal u f w.1) then
    let i := Classical.choose h
    let u := Classical.choose (Classical.choose_spec h)
    let f := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
    let w := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))
    some (i, decAns u f w)
  else none

/-- **The register's porcupine model**, as the pending library's invariant sees it (its sequential
model only). -/
def regS0 {GF : BundledGFunctors} : ModelSpec GF (PSet service.Reg HIn) where
  M := pM regB regDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : HIn, i = inV x.1) ∧ ∃ (u f : Bool) (w : Str8), o = outVal u f w.1⌝)
  ioOk_pers _ _ := by infer_instance

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- kit.go's `State` of the register `a` and the pending slice `sl`. -/
def stOf (a : service.Reg) (sl : GoSlice) : State := State.mk a.isSome (a.getD []) sl

/-- A model value: the boxed `State{Present, V, Pend}` of the register `a` and a read-only slice of
the values of the writes `P`; `(a, P)` brackets the set `s` (`Sim`); `P` has at most `k` entries (a
step adds at most one). -/
def regRep (k : Nat) (v : GoInterface) (s : PSet service.Reg HIn) : IProp GF :=
  iprop(∃ (sl : GoSlice) (a : service.Reg) (P : List HIn),
    ⌜v = interface.mkOk State.ty #(stOf a sl) ∧ Sim a P s ∧ RegOk a ∧
      (∀ i ∈ P, i.1.1 = true) ∧ P.length ≤ k⌝ ∗
    sl ↦*□ P.map pendV)

/-- **The register's porcupine model**: `pM regB regDec`, over `Model()`'s values. -/
def regS : ModelSpec GF (PSet service.Reg HIn) where
  M := (regS0 (GF := GF)).M
  rep k v s := regRep k v s
  ioOk := (regS0 (GF := GF)).ioOk
  ioOk_pers := (regS0 (GF := GF)).ioOk_pers

end spec

/-! ## The helpers -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet

set_option goose.wp.extras true

/-- `pushPend(p, v)`: a new slice, `p`'s values with `v` appended. -/
theorem wp_pushPend (p : GoSlice) (P : List GoString) (v : GoString) (hP : P.length < 2 ^ 60) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.pushPend)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ v $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

/-- `findPend(p, v)`: the first index of `v` in `p`, if any. -/
theorem wp_findPend (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.findPend)) (Val #p)) (Val #v))
    {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
        ⌜(∀ j < (if ok then sint.nat i else P.length), P[j]? ≠ some v) ∧
          (ok = true → 0 ≤ sint.Z i ∧ P[sint.nat i]? = some v)⌝ }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ ∀ j < sint.nat i, P[j]? ≠ some v⌝ :
        IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by decide, Hl.2, fun j hj => by rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for HI
  wp_if_destruct
  · have hi : sint.Z i < sint.Z p.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    list_elem P (sint.nat i) as e
    rw [ite_eq_left ⟨Hi.1, hi⟩]
    wp_apply wp_load_slice_index p (sint.Z i) P DFrac.discard e Hi.1 $$ [$Hp] with -
    · ipureintro; exact He_lookup
    (try wp_auto)
    by_cases hv : e = v
    · rw [decide_eq_true hv]
      wp_auto
      rw [forPostcondition_unseal]; unfold forPostconditionDef
      iright; iright; iright; ileft
      iexists #()
      isplitr
      · ipureintro; rfl
      dsimp only
      wp_auto
      iapply HΦ
      ipureintro
      subst hv
      exact ⟨fun j hj => Hi.2.2 j (by simpa using hj), fun _ => ⟨Hi.1, He_lookup⟩⟩
    · rw [decide_eq_false hv]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj => ?_⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Hi.2.2 j hj
      · rw [He_lookup]; intro h; exact hv (Option.some.inj h)
  · have hn : sint.nat i = P.length := by
      have : ¬ sint.Z i < sint.Z p.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    ipureintro
    exact ⟨fun j hj => Hi.2.2 j (by simpa [hn] using hj), fun h => by cases h⟩

theorem eraseIdx_take_succ {α : Type} (P : List α) (i j : Nat) (x : α) (hx : P[j]? = some x)
    (hij : j ≠ i) : (P.take (j + 1)).eraseIdx i = (P.take j).eraseIdx i ++ [x] := by
  rw [List.take_add_one, hx, Option.toList_some]
  have hj : j < P.length := (List.getElem?_eq_some_iff.1 hx).1
  have hl : (P.take j).length = j := by simp; omega
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rw [List.eraseIdx_of_length_le (by simp; omega), List.eraseIdx_of_length_le (by omega)]
  · rw [List.eraseIdx_append_of_lt_length (by omega)]

theorem eraseIdx_take_self {α : Type} (P : List α) (i : Nat) :
    (P.take (i + 1)).eraseIdx i = (P.take i).eraseIdx i := by
  rw [List.eraseIdx_of_length_le (l := P.take i) (by simp [Nat.min_le_left])]
  rcases Nat.lt_or_ge i P.length with h | h
  · rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
      List.eraseIdx_append_of_length_le (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt h), Nat.sub_self,
      List.eraseIdx_cons_zero, List.append_nil]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
      List.eraseIdx_of_length_le (by omega)]

/-- `erasePend(p, i)`: a fresh slice, `p` without its element `i`. -/
theorem wp_erasePend (p : GoSlice) (P : List GoString) (i : w64) (hi : 0 ≤ sint.Z i) :
    {{ (p ↦*□ P : IProp GF) }}
      (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.erasePend)) (Val #p))
        (Val #i))
    {{ (q : GoSlice), RET #q; q ↦* P.eraseIdx (sint.nat i) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make3 (V := GoString) (W64 0) p.len ⟨by decide, Hl.2⟩ as %q ⟨Hq, Hqc, -⟩
  (try wp_auto)
  ihave HI : (∃ (j : w64) (qq : GoSlice), "j" ∷ j_ptr ↦ j ∗ "q" ∷ q_ptr ↦ qq ∗
      "Hq" ∷ qq ↦* (P.take (sint.nat j)).eraseIdx (sint.nat i) ∗
      "Hqc" ∷ ownSliceCap GoString qq (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z p.len⌝ : IProp GF) $$ [j q Hq Hqc]
  · iexists W64 0, q
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.eraseIdx_nil,
      List.replicate_zero]
    iframe
    ipureintro; exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hj : sint.Z j < sint.Z p.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    by_cases hji : j = i
    · subst hji
      simp only [decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, qq
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, eraseIdx_take_self]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · rw [decide_eq_false hji]
      simp only [Bool.not_false]
      wp_auto
      list_elem P (sint.nat j) as e
      rw [ite_eq_left ⟨Hj.1, hj⟩]
      wp_apply wp_load_slice_index p (sint.Z j) P DFrac.discard e Hj.1 $$ [$Hp] with -
      · ipureintro; exact He_lookup
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoString) [e]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hq $Hqc $Hsl1] as %qq' ⟨Hq, Hqc, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, qq'
      have hne : sint.nat j ≠ sint.nat i := fun h => hji (by word)
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
        eraseIdx_take_succ P _ _ e He_lookup hne]
      iframe
      ipureintro; exact ⟨by word, by word⟩
  · have hn : sint.nat j = P.length := by
      have : ¬ sint.Z j < sint.Z p.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    rw [hn, List.take_length]
    iframe

theorem map_eraseIdx' {α β : Type} (g : α → β) (l : List α) (j : Nat) :
    (l.eraseIdx j).map g = (l.map g).eraseIdx j := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih => cases j <;> simp_all [List.eraseIdx]

theorem erase_first {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) (j : Nat)
    (hj : l[j]? = some x) (hlt : ∀ i < j, l[i]? ≠ some x) : l.erase x = l.eraseIdx j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons y l ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj; simp
    | succ j =>
      have hy : y ≠ x := fun h => hlt 0 (by omega) (by simp [h])
      rw [List.erase_cons_tail (by simpa using hy), List.eraseIdx_cons_succ,
        ih j (by simpa using hj) (fun i hi => by simpa using hlt (i + 1) (by omega))]

/-- `findPend`'s index on the values of `P`: `P`'s first write of that value, which `goStep` erases. -/
theorem find_idx (P : List HIn) (w : GoString) (idx : Nat)
    (h1 : ∀ j < idx, (P.map pendV)[j]? ≠ some w) (h2 : (P.map pendV)[idx]? = some w) :
    ∃ j, P.find? (fun j => decide (pendV j = w)) = some j ∧
      (P.erase j).map pendV = (P.map pendV).eraseIdx idx := by
  rw [List.getElem?_map] at h2
  obtain ⟨y, hy, hpy⟩ := Option.map_eq_some_iff.1 h2
  have hlt : ∀ k < idx, P[k]? ≠ some y := by
    intro k hk he
    exact h1 k hk (by rw [List.getElem?_map, he]; simp [hpy])
  refine ⟨y, ?_, ?_⟩
  · have hidx : idx < P.length := (List.getElem?_eq_some_iff.1 hy).1
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hpy, idx, hidx, (List.getElem?_eq_some_iff.1 hy).2, fun k hk => ?_⟩
    have := h1 k hk
    rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  · rw [erase_first P y idx hy hlt, map_eraseIdx']

theorem find_none' (P : List HIn) (w : GoString)
    (h1 : ∀ j < (P.map pendV).length, (P.map pendV)[j]? ≠ some w) :
    P.find? (fun j => decide (pendV j = w)) = none := by
  rw [List.find?_eq_none]
  intro x hx hv
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hx
  exact h1 j (by simpa using hj)
    (by rw [List.getElem?_map, List.getElem?_eq_getElem hj, he]; simpa using hv)

/-- kit.go's `In` of an input. -/
def inOf (i : HIn) : In := In.mk i.1.1 i.1.2.1 i.1.2.2

/-- What `step` returns: the verdict of `goStep` on the decoded answer, and when it allows the
step, a state holding `goStep`'s next state. -/
def goStepPost (a : service.Reg) (P : List HIn) (i : HIn) (u f : Bool) (w : Str8) (ok : Bool)
    (s' : State) : IProp GF :=
  iprop(⌜ok = (goStep a P i (decAns u f w)).isSome⌝ ∗
    if ok then ∃ (sl' : GoSlice) (a' : service.Reg) (P' : List HIn),
      ⌜s' = stOf a' sl' ∧ goStep a P i (decAns u f w) = some (a', P')⌝ ∗
      sl' ↦*□ P'.map pendV
    else True)

theorem wp_step (sl : GoSlice) (a : service.Reg) (P : List HIn)
    (hlen : P.length < 2 ^ 60) (i : HIn) (u f : Bool) (w : Str8) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ P.map pendV }}
      (App (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.step))
        (Val #(State.mk a.isSome (a.getD []) sl))) (Val #(inOf i))) (Val #(Out.mk u f w.1)))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); goStepPost a P i u f w ok s' }} := by
  wp_start as #Hsl
  have hpm : (P.map pendV).length < 2 ^ 60 := by simpa using hlen
  obtain ⟨⟨p, wy, v⟩, hi⟩ := i
  simp only [inOf]
  cases u <;> cases p
  · -- a read, its answer known
    cases a <;> cases f
    all_goals simp only [Option.isSome_none, Option.getD_none, Option.isSome_some,
      Option.getD_some]
    all_goals wp_auto
    · -- nothing held, nothing found
      by_cases hw : w.1 = []
      · simp only [hw, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hw]
        simp only [Bool.not_false, ↓reduceIte]
        iexists sl, none, P
        isplitr
        · ipureintro; exact ⟨rfl, by simp [goStep, decAns, hw]⟩
        iexact Hsl
      · simp only [hw, _root_.decide_false, Bool.not_false]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    · -- nothing held, a value found: a pending write's?
      wp_apply wp_findPend sl (P.map pendV) w.1 $$ [$Hsl] as %idx %ok %Hf
      cases ok
      · have hnf := find_none' P w.1 (by simpa using Hf.1)
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hnf]
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · obtain ⟨hidx0, hidx⟩ := Hf.2 rfl
        obtain ⟨j, hfd, herase⟩ := find_idx P w.1 (sint.nat idx) (by simpa using Hf.1) hidx
        wp_auto
        wp_apply +noauto wp_erasePend sl (P.map pendV) idx hidx0 $$ [$Hsl] as %q Hq
        iapply fupd_wp
        imod ownSlice_persist _ _ _ $$ Hq with #Hq
        imodintro
        wp_auto
        iapply HΦ
        unfold goStepPost
        have hg : goStep none P ⟨(false, wy, v), hi⟩ (decAns false true w) =
            some (some w.1, P.erase j) := by
          simp [goStep, decAns, hfd]
        rw [hg]
        isplitr
        · ipureintro; rfl
        simp only [Option.isSome_some, ↓reduceIte]
        iexists q, some w.1, P.erase j
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        rw [herase]
        iexact Hq
    · -- a value held, nothing found
      by_cases hw : w.1 = []
      · simp only [hw, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · simp only [hw, _root_.decide_false, Bool.not_false]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    · -- a value held, a value found: the register's, or a pending write's?
      rename_i x
      by_cases hxw : x = w.1
      · rw [decide_eq_true hxw]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hxw]
        simp only [↓reduceIte]
        iexists sl, some x, P
        isplitr
        · ipureintro; exact ⟨rfl, by simp [goStep, decAns, hxw]⟩
        iexact Hsl
      · rw [decide_eq_false hxw]
        wp_auto
        wp_apply wp_findPend sl (P.map pendV) w.1 $$ [$Hsl] as %idx %ok %Hf
        cases ok
        · have hnf := find_none' P w.1 (by simpa using Hf.1)
          wp_auto
          iapply HΦ
          unfold goStepPost
          isplitr
          · ipureintro; simp [goStep, decAns, hnf, hxw]
          simp only [Bool.false_eq_true, ↓reduceIte]
          itrivial
        · obtain ⟨hidx0, hidx⟩ := Hf.2 rfl
          obtain ⟨j, hfd, herase⟩ := find_idx P w.1 (sint.nat idx) (by simpa using Hf.1) hidx
          wp_auto
          wp_apply +noauto wp_erasePend sl (P.map pendV) idx hidx0 $$ [$Hsl] as %q Hq
          iapply fupd_wp
          imod ownSlice_persist _ _ _ $$ Hq with #Hq
          imodintro
          wp_auto
          iapply HΦ
          unfold goStepPost
          have hg : goStep (some x) P ⟨(false, wy, v), hi⟩ (decAns false true w) =
              some (some w.1, P.erase j) := by
            simp [goStep, decAns, hfd, hxw]
          rw [hg]
          isplitr
          · ipureintro; rfl
          simp only [Option.isSome_some, ↓reduceIte]
          iexists q, some w.1, P.erase j
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          rw [herase]
          iexact Hq
  · -- a write, its answer known
    cases f
    · wp_auto
      by_cases hw : w.1 = []
      · simp only [hw, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hw]
        simp only [↓reduceIte]
        iexists sl, some v, P
        isplitr
        · ipureintro; exact ⟨rfl, by simp [goStep, decAns, hw, pendV]⟩
        iexact Hsl
      · simp only [hw, _root_.decide_false, Bool.not_false]
        wp_auto
        iapply HΦ
        unfold goStepPost
        isplitr
        · ipureintro; simp [goStep, decAns, hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
    · wp_auto
      iapply HΦ
      unfold goStepPost
      isplitr
      · ipureintro; simp [goStep, decAns]
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
  · -- a read, unknown
    wp_auto
    iapply HΦ
    unfold goStepPost
    isplitr
    · ipureintro; simp [goStep, decAns]
    simp only [↓reduceIte]
    iexists sl, a, P
    isplitr
    · ipureintro; exact ⟨rfl, by simp [goStep, decAns]⟩
    iexact Hsl
  · -- a write, unknown: pending
    wp_auto
    wp_apply +noauto wp_pushPend sl (P.map pendV) v hpm $$ [$Hsl] as %q Hq
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hq with #Hq
    imodintro
    wp_auto
    iapply HΦ
    unfold goStepPost
    isplitr
    · ipureintro; simp [goStep, decAns]
    simp only [↓reduceIte]
    iexists q, a, P ++ [⟨(true, wy, v), hi⟩]
    isplitr
    · ipureintro; exact ⟨rfl, by simp [goStep, decAns]⟩
    simp only [List.map_append, List.map_cons, List.map_nil, pendV]
    iexact Hq

end proof

/-! ## `regDec` on boxed values -/

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : Assumptions]

/-- `In`'s values are injective. -/
theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hV := (In.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  have hW := (In.TypeAssumptions.get_Way x).isGoStep_det_internal.isGoStep_pure_det
  have hW' := (In.TypeAssumptions.get_Way y).isGoStep_det_internal.isGoStep_pure_det
  have hP := (In.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (In.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hV'] at hV
  rw [h, hW'] at hW
  rw [h, hP'] at hP
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  have eW : Val #x.Way' = Val #y.Way' := (congrFun hW (Val #y.Way')) ▸ rfl
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  injection eV with eV
  injection eW with eW
  injection eP with eP
  have eV' := go.intoVal_inj eV
  have eW' := go.intoVal_inj eW
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  cases x; cases y
  simp only at eV' eW' eP'
  subst eV' eW' eP'
  rfl

theorem inV_inj {x y : InF} (h : inV x = inV y) : x = y := by
  simp only [inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  have := in_intoVal_inj h
  simp only [In.mk.injEq] at this
  obtain ⟨h1, h2, h3⟩ := this
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- `regDec` on a boxed input and a boxed bounded `Out`. -/
theorem regDec_box (x : HIn) (u f : Bool) (w : Str8) :
    regDec (inV x.1, outVal u f w.1) = some (x, decAns u f w) := by
  unfold regDec
  split
  · next h =>
    have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec h)))
    obtain ⟨h1, h2⟩ := Prod.mk.inj hs
    have e1 := Subtype.ext (inV_inj h1)
    obtain ⟨e2, e3, e4⟩ := outVal_inj h2
    have e4' := Subtype.ext e4
    dsimp only
    rw [← e4', ← e3, ← e2, ← e1]
  · next hn => exact absurd ⟨x, u, f, w, rfl⟩ hn

end dec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet

theorem inV_inOf (x : HIn) : inV x.1 = interface.mkOk In.ty #(inOf x) := rfl

/-- **porcupine's model is the pending-writes model** of the far side's store `regR g` (remote's
`Check` premise). -/
theorem regS_pendDec (g : GName) :
    PendDec (regR (GF := GF) (Gg := hG.goose_globalGS) g) (regS (GF := GF)) :=
  .ofTotal (fun _ => rfl) {
  init := rfl
  ok s i o := by
    show (pM regB regDec).step s (inV i.1, outVal false o.1.1 o.1.2) = _
    rw [pM_step regB regDec s _ i _ (regDec_box i false o.1.1 ⟨o.1.2, o.2⟩)]
    rfl
  err s i := by
    show (pM regB regDec).step s (inV i.1, outVal true false []) = _
    rw [pM_step regB regDec s _ i _ (regDec_box i true false ⟨[], by simp⟩)]
    rfl
  ioOk_ok i o := BI.pure_intro ⟨⟨i, rfl⟩, false, o.1.1, ⟨o.1.2, o.2⟩, rfl⟩
  ioOk_err i := BI.pure_intro ⟨⟨i, rfl⟩, true, false, ⟨[], by simp⟩, rfl⟩
  noObs _ := rfl }

/-- **Distinct outputs have distinct bytes** (remote's `Check` premise). -/
theorem regR_encOut_inj (g : GName) (o o' : HOut)
    (h : (regR (GF := GF) (Gg := hG.goose_globalGS) g).encOut
        ((regR (GF := GF) (Gg := hG.goose_globalGS) g).ov o) =
      (regR (GF := GF) (Gg := hG.goose_globalGS) g).encOut
        ((regR (GF := GF) (Gg := hG.goose_globalGS) g).ov o')) :
    o = o' := by
  obtain ⟨⟨f, v⟩, hv⟩ := o
  obtain ⟨⟨f', v'⟩, hv'⟩ := o'
  simp only [regR, outV] at h
  rw [encOutV_outVal _ _ _ hv, encOutV_outVal _ _ _ hv'] at h
  simp only [encOutB, List.cons.injEq] at h
  obtain ⟨-, h2, -, rfl⟩ := h
  cases f <;> cases f' <;> first | rfl | exact absurd h2 (by decide)

/-- `Model()`: porcupine's model of the register with pending writes (`regS`). -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (regS (GF := GF)) m }}

/-- `Gen`: a client's next input, a boxed input of the kit (`HIn`: a way below 3, a value shorter
than 256 bytes). Under the package's initialization (`Gen` calls `strconv.Itoa`, which needs
`strconv`'s; `lintest.genSpec`'s triple has no package premise). -/
abbrev Gen.spec : Prop :=
  isPkgInit (PROP := IProp GF) kpkg ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.hashicorp.raft.examples.hraftnet.Gen [])
      (fun x => iprop(∃ i : HIn, ⌜x = inV i.1⌝))

end proof

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
