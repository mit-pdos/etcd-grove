/-
The kit's porcupine model (`model.go`, notes/dsv-quepaxa.md): its spec `qS` and the pure facts its
proof (`ModelProof.lean`) needs.

The Go state is a slice of entries, one per key touched (`State`); as a pure value, a list `E` of
keys and entries (`Pure/ModelSet`'s `Ent`), with distinct keys (`qOk`). Its lookup `lk E` is the
model's state `M` of `Pure/ModelSet`, and the state stands for `mSet (lk E)`. `stepL` is `model.go`'s
`step` on `E`; `stepL_lk`: its lookup is `upd`'s, so its set is `pSeq kvB`'s step (`step_mSet`).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Base
public import Dsverify.Proof.raxos.Pure.ModelSet
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace raxos.examples.quepaxanet

open EtcdGrove.linkv raxos.pure

/-! ## The state as a list of keys and entries -/

/-- A key and its entry. -/
abbrev KEnt := GoString × Ent

/-- Key `k`'s entry in `E` (`lookup`): the first with key `k`, or the empty entry. -/
def lk (E : List KEnt) (k : GoString) : Ent :=
  ((E.find? (fun p => decide (p.1 = k))).map Prod.snd).getD Ent.empty

/-- The state's invariant: distinct keys, every entry `Ok`. -/
def qOk (E : List KEnt) : Prop := (E.map Prod.fst).Nodup ∧ ∀ p ∈ E, p.2.Ok

/-- `E` with key `k`'s entry `e` (`set` at `lookup`'s index). -/
def setL (E : List KEnt) (k : GoString) (e : Ent) : List KEnt :=
  if E.findIdx (fun p => decide (p.1 = k)) < E.length then
    E.set (E.findIdx (fun p => decide (p.1 = k))) (k, e)
  else E ++ [(k, e)]

/-- `model.go`'s `step` on the pure state: `stepE` on the input's key. -/
def stepL (E : List KEnt) (i : KIn) (a : Ans KOut) : Bool × List KEnt :=
  if (raxos.pure.stepE (lk E i.k) i a).1 then (true, setL E i.k (raxos.pure.stepE (lk E i.k) i a).2)
  else (false, E)

theorem lk_nil (k : GoString) : lk [] k = Ent.empty := rfl

theorem lk_cons (p : KEnt) (E : List KEnt) (k : GoString) :
    lk (p :: E) k = if p.1 = k then p.2 else lk E k := by
  unfold lk
  by_cases h : p.1 = k <;> simp [List.find?_cons, h]

theorem findIdx_cons (p : KEnt) (E : List KEnt) (k : GoString) :
    (p :: E).findIdx (fun p => decide (p.1 = k)) =
      if p.1 = k then 0 else E.findIdx (fun p => decide (p.1 = k)) + 1 := by
  by_cases h : p.1 = k <;> simp [List.findIdx_cons, h]

theorem setL_cons (p : KEnt) (E : List KEnt) (k : GoString) (e : Ent) :
    setL (p :: E) k e = if p.1 = k then (k, e) :: E else p :: setL E k e := by
  unfold setL
  rw [findIdx_cons]
  by_cases h : p.1 = k
  · simp [h]
  · simp only [h, ↓reduceIte, List.length_cons, Nat.add_lt_add_iff_right, List.set_cons_succ]
    split <;> rfl

theorem lk_setL_pt (E : List KEnt) (k : GoString) (e : Ent) (k' : GoString) :
    lk (setL E k e) k' = if k' = k then e else lk E k' := by
  induction E with
  | nil => simp [setL, lk_cons, lk_nil, eq_comm]
  | cons p E ih =>
    rw [setL_cons]
    by_cases h : p.1 = k
    · rw [if_pos h]
      simp only [lk_cons]
      by_cases h' : k' = k
      · simp [h']
      · have h2 : ¬ p.1 = k' := fun e => h' (e.symm.trans h)
        simp [h', h2, Ne.symm h']
    · rw [if_neg h]
      simp only [lk_cons, ih]
      by_cases h' : k' = k
      · subst h'; simp [h]
      · simp [h']

theorem lk_setL (E : List KEnt) (k : GoString) (e : Ent) :
    lk (setL E k e) = upd (lk E) k e := by
  funext k'
  rw [lk_setL_pt]
  rfl

theorem keys_setL (E : List KEnt) (k : GoString) (e : Ent) :
    (setL E k e).map Prod.fst =
      if k ∈ E.map Prod.fst then E.map Prod.fst else E.map Prod.fst ++ [k] := by
  induction E with
  | nil => simp [setL]
  | cons p E ih =>
    rw [setL_cons]
    by_cases h : p.1 = k
    · simp [h]
    · simp only [h, ↓reduceIte, List.map_cons, ih, List.mem_cons]
      by_cases h2 : k ∈ E.map Prod.fst
      · simp [h2]
      · simp [h2, Ne.symm h]

theorem mem_setL {E : List KEnt} {k : GoString} {e : Ent} {q : KEnt} (hq : q ∈ setL E k e) :
    q = (k, e) ∨ q ∈ E := by
  induction E with
  | nil => simp [setL] at hq; exact .inl hq
  | cons p E ih =>
    rw [setL_cons] at hq
    split at hq
    · rcases List.mem_cons.1 hq with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 hq with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases ih h with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_cons_of_mem _ h')

theorem lk_mem {E : List KEnt} (k : GoString) : lk E k = Ent.empty ∨ (k, lk E k) ∈ E := by
  induction E with
  | nil => exact .inl rfl
  | cons p E ih =>
    rw [lk_cons]
    by_cases h : p.1 = k
    · rw [if_pos h]; exact .inr (h ▸ List.mem_cons_self)
    · rw [if_neg h]
      rcases ih with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')

theorem lk_ok {E : List KEnt} (h : qOk E) (k : GoString) : (lk E k).Ok := by
  rcases lk_mem (E := E) k with h' | h'
  · rw [h']; intro; rfl
  · exact h.2 _ h'

theorem qOk_setL {E : List KEnt} (h : qOk E) (k : GoString) {e : Ent} (he : e.Ok) :
    qOk (setL E k e) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [keys_setL]
    split
    · exact h.1
    · rename_i hk
      refine List.nodup_append.2 ⟨h.1, by simp, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hk ha
  · rcases mem_setL hq with rfl | hq
    · exact he
    · exact h.2 q hq

theorem length_setL (E : List KEnt) (k : GoString) (e : Ent) :
    (setL E k e).length ≤ E.length + 1 := by
  unfold setL; split <;> simp

/-! ## Bounds: a step adds at most one entry and one pending value -/

/-- Every entry's pending values are at most `n`. -/
def allLe (n : Nat) (E : List KEnt) : Prop := ∀ p ∈ E, p.2.all.length ≤ n

theorem stepE_all_len (e : Ent) (i : KIn) (a : Ans KOut) :
    (raxos.pure.stepE e i a).2.all.length ≤ e.all.length + 1 := by
  obtain ⟨put, k, v⟩ := i
  obtain ⟨f, w, old, new⟩ := e
  unfold raxos.pure.stepE
  cases a with
  | err => cases put <;> simp [Ent.all] <;> omega
  | ok o =>
    cases put
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · simp
      · split
        · simp only [Ent.all, List.append_nil]
          have := List.length_erase_le (l := old ++ new) (a := o.v)
          simp only [List.length_append] at this ⊢
          omega
        · simp
    · simp only [↓reduceIte]
      split
      · simp
      · simp [Ent.all]

theorem lk_all_le {n : Nat} {E : List KEnt} (h : allLe n E) (k : GoString) :
    (lk E k).all.length ≤ n := by
  rcases lk_mem (E := E) k with h' | h'
  · rw [h']; simp [Ent.empty, Ent.all]
  · exact h _ h'

theorem allLe_setL {n : Nat} {E : List KEnt} (h : allLe n E) (k : GoString) {e : Ent}
    (he : e.all.length ≤ n + 1) : allLe (n + 1) (setL E k e) := by
  intro q hq
  rcases mem_setL hq with rfl | hq
  · exact he
  · have := h q hq; omega

/-! ## The step on sets -/

/-- **`step` on the pure state is `pSeq kvB`'s step** on the sets the states stand for. -/
theorem stepL_pSeq {E : List KEnt} (hE : qOk E) (hne : ∃ c, mSet (lk E) c) (i : KIn)
    (a : Ans KOut) :
    (pSeq kvB).step (mSet (lk E)) (i, a) =
      if (stepL E i a).1 then some (mSet (lk (stepL E i a).2)) else none := by
  rw [step_mSet hne i (lk_ok hE i.k) a]
  unfold stepL
  split <;> simp [lk_setL, *]

theorem stepL_ok {E : List KEnt} (hE : qOk E) (i : KIn) (a : Ans KOut) : qOk (stepL E i a).2 := by
  unfold stepL
  split
  · exact qOk_setL hE _ (raxos.pure.stepE_ok (lk_ok hE i.k) i a)
  · exact hE

theorem stepL_bounds {n : Nat} {E : List KEnt} (hl : E.length ≤ n) (ha : allLe n E) (i : KIn)
    (a : Ans KOut) : (stepL E i a).2.length ≤ n + 1 ∧ allLe (n + 1) (stepL E i a).2 := by
  unfold stepL
  split
  · refine ⟨?_, allLe_setL ha _ ?_⟩
    · have := length_setL E i.k (raxos.pure.stepE (lk E i.k) i a).2
      simp only; omega
    · have := stepE_all_len (lk E i.k) i a
      have := lk_all_le ha i.k
      omega
  · exact ⟨by simp only; omega, fun q hq => by have := ha q hq; omega⟩

/-! ## porcupine's operations -/

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding an `In`). -/
abbrev inV (i : In) : GoInterface := interface.mkOk In.ty #i

/-- An output, boxed (`any` holding an `Out`). -/
abbrev outV (o : Out) : GoInterface := interface.mkOk Out.ty #o

/-- A state, boxed (`any` holding a `State`). -/
abbrev stV (s : State) : GoInterface := interface.mkOk State.ty #s

/-- The kit's `In` as the store's input. -/
def kin (i : In) : KIn := ⟨i.Put', i.K', i.V'⟩

/-- The kit's `Out` as the store's answer: unknown (`err`), or a known outcome. -/
def kans (o : Out) : Ans KOut := if o.Unknown' then .err else .ok ⟨o.Found', o.V'⟩

open Classical in
/-- porcupine's operations as the store's: a boxed `In` and a boxed `Out`; anything else decodes
to nothing. -/
def qDec (io : OpV) : Option (KIn × Ans KOut) :=
  if h : ∃ (i : In) (o : Out), io = (inV i, outV o) then
    some (kin (Classical.choose h), kans (Classical.choose (Classical.choose_spec h)))
  else none

/-- **The store's porcupine model**, as the pending library's invariant sees it: `pSeq kvB`
through `qDec`. -/
def qS0 {GF : BundledGFunctors} : ModelSpec GF (PSet raxos.pure.Store KIn) where
  M := pM kvB qDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : In, i = inV x) ∧ ∃ y : Out, o = outV y⌝)
  ioOk_pers _ _ := by infer_instance

end vals

section dec
variable [GooseExts] [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics] [bvi : go.BasicIntoValInj]
variable [package_sem : raxos.examples.quepaxanet.Assumptions]

theorem in_intoVal_inj {x y : In} (h : (#x : val) = #y) : x = y := by
  have hP := (In.TypeAssumptions.get_Put x).isGoStep_det_internal.isGoStep_pure_det
  have hP' := (In.TypeAssumptions.get_Put y).isGoStep_det_internal.isGoStep_pure_det
  have hK := (In.TypeAssumptions.get_K x).isGoStep_det_internal.isGoStep_pure_det
  have hK' := (In.TypeAssumptions.get_K y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (In.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (In.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hP'] at hP
  rw [h, hK'] at hK
  rw [h, hV'] at hV
  have eP : Val #x.Put' = Val #y.Put' := (congrFun hP (Val #y.Put')) ▸ rfl
  have eK : Val #x.K' = Val #y.K' := (congrFun hK (Val #y.K')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eP with eP
  injection eK with eK
  injection eV with eV
  have eP' := GoGlobalContext.intoVal_inj_bool eP
  have eK' := go.intoVal_inj eK
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eP' eK' eV'
  subst eP' eK' eV'
  rfl

theorem out_intoVal_inj {x y : Out} (h : (#x : val) = #y) : x = y := by
  have hU := (Out.TypeAssumptions.get_Unknown x).isGoStep_det_internal.isGoStep_pure_det
  have hU' := (Out.TypeAssumptions.get_Unknown y).isGoStep_det_internal.isGoStep_pure_det
  have hF := (Out.TypeAssumptions.get_Found x).isGoStep_det_internal.isGoStep_pure_det
  have hF' := (Out.TypeAssumptions.get_Found y).isGoStep_det_internal.isGoStep_pure_det
  have hV := (Out.TypeAssumptions.get_V x).isGoStep_det_internal.isGoStep_pure_det
  have hV' := (Out.TypeAssumptions.get_V y).isGoStep_det_internal.isGoStep_pure_det
  rw [h, hU'] at hU
  rw [h, hF'] at hF
  rw [h, hV'] at hV
  have eU : Val #x.Unknown' = Val #y.Unknown' := (congrFun hU (Val #y.Unknown')) ▸ rfl
  have eF : Val #x.Found' = Val #y.Found' := (congrFun hF (Val #y.Found')) ▸ rfl
  have eV : Val #x.V' = Val #y.V' := (congrFun hV (Val #y.V')) ▸ rfl
  injection eU with eU
  injection eF with eF
  injection eV with eV
  have eU' := GoGlobalContext.intoVal_inj_bool eU
  have eF' := GoGlobalContext.intoVal_inj_bool eF
  have eV' := go.intoVal_inj eV
  cases x; cases y
  simp only at eU' eF' eV'
  subst eU' eF' eV'
  rfl

theorem inV_inj {a b : In} (h : inV a = inV b) : a = b := by
  simp only [inV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact in_intoVal_inj h

theorem outV_inj {a b : Out} (h : outV a = outV b) : a = b := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    _root_.true_and] at h
  exact out_intoVal_inj h

/-- `qDec` on a boxed `In` and a boxed `Out`. -/
theorem qDec_box (i : In) (o : Out) : qDec (inV i, outV o) = some (kin i, kans o) := by
  have hx : ∃ (i' : In) (o' : Out), (inV i, outV o) = (inV i', outV o') := ⟨i, o, rfl⟩
  rw [qDec, dif_pos hx]
  have hs := Classical.choose_spec (Classical.choose_spec hx)
  obtain ⟨h1, h2⟩ := Prod.mk.inj hs
  generalize Classical.choose (Classical.choose_spec hx) = o' at h2 ⊢
  generalize Classical.choose hx = i' at h1 ⊢
  rw [← inV_inj h1, ← outV_inj h2]

end dec

/-! ## The model's spec -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]

/-- A Go entry holding key `p.1`'s entry `p.2`, its pending lists read-only. -/
def entRep (e : Entry) (p : KEnt) : IProp GF :=
  iprop(⌜e.K' = p.1 ∧ e.Found' = p.2.f ∧ e.V' = p.2.v⌝ ∗ e.Old' ↦*□ p.2.old ∗ e.New' ↦*□ p.2.new)

instance entRep_persistent (e : Entry) (p : KEnt) : Persistent (entRep (GF := GF) e p) := by
  unfold entRep; infer_instance

/-- A model value: the boxed `State` `sl`, read-only, whose entries hold `E` (distinct keys,
entries `Ok`); its set is `mSet (lk E)`, which is not empty; at most `k` entries and `k` pending
values per entry (a step adds at most one of each). -/
def qRep (k : Nat) (v : GoInterface) (S : PSet raxos.pure.Store KIn) : IProp GF :=
  iprop(∃ (sl : State) (es : List Entry) (E : List KEnt),
    ⌜v = stV sl ∧ S = mSet (lk E) ∧ qOk E ∧ (∃ c, mSet (lk E) c) ∧ E.length ≤ k ∧ allLe k E⌝ ∗
    sl ↦*□ es ∗ [∗list] e;p ∈ es;E, entRep e p)

/-- **The store's porcupine model** (pending puts): `pSeq kvB` through `qDec`. -/
def qS : ModelSpec GF (PSet raxos.pure.Store KIn) where
  M := (qS0 (GF := GF)).M
  rep k v s := qRep k v s
  ioOk := (qS0 (GF := GF)).ioOk
  ioOk_pers := (qS0 (GF := GF)).ioOk_pers

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

/-- `Model()`: the store's porcupine model. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! raxos.examples.quepaxanet.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (qS (GF := GF)) m }}

end spec

end raxos.examples.quepaxanet
end Perennial
