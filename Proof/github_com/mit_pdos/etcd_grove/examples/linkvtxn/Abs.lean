/-
Lean-first (no Rocq counterpart).

# linkvtxn: the Go model's store against the robustness model (linkv-txn stage E)

The abstraction of `ModelLemmas.lean`'s pure Go store to `linkv/TxnModel.lean`'s (`absSt`), the
decoders of the Go `Input` and `Output` (`decIn`, `decOut`), and **`mstepL_abs`**: on a good store
(`GoodSt`: entries sorted strictly by key, every key the workload's), `mstep` of a decodable input
is the model's `mStep` (the state, and the output decoded), and keeps the store good.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.ModelLemmas
public import Perennial.Std.Word.Automation

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open github_com.mit_pdos.etcd_grove.examples.linkvtxn
open Classical

section go
variable [ext : FfiSyntax]

/-! ## The abstraction -/

/-- The workload's keys (`workloadKeys()`). -/
abbrev wks : List GoString := [go!"k0", go!"k1", go!"k2"]

/-- A Go value's model value. -/
def absVR (r : VR) : linkv.VR GoString := ⟨r.Val', r.Mod', r.Ver'⟩

/-- The model store of a list of entries: every key's first entry's value. -/
def absStore (es : List entry) : linkv.MStore GoString GoString :=
  fun k => (es.find? (fun e => decide (e.key' = k))).map (fun e => absVR e.r')

/-- **The model state of a Go store.** -/
def absSt (st : GSt) : linkv.MSt GoString GoString := ⟨absStore st.kvs, uint.nat st.rev⟩

/-- A good store: its entries sorted strictly by key, every key the workload's. -/
def GoodSt (st : GSt) : Prop :=
  (st.kvs.map entry.key').Pairwise go.GoStringLt ∧ ∀ e ∈ st.kvs, e.key' ∈ wks

/-! ## The decoders -/

/-- A comparison's model comparison. -/
def decCmp (c : Cmp) : Option (linkv.MCmp GoString GoString) :=
  if c.Kind' = W64 0 then some (.val c.Key' c.Val')
  else if c.Kind' = W64 1 then some (.ver c.Key' c.Num')
  else if c.Kind' = W64 2 then some (.mod c.Key' c.Num')
  else none

/-- A transaction operation's model operation. -/
def decTOp (o : TOp) : Option (linkv.MOp GoString GoString) :=
  if o.Kind' = W64 0 then some (.get o.Key')
  else if o.Kind' = W64 1 then some (.put o.Key' o.Val')
  else if o.Kind' = W64 2 then some (.del o.Key')
  else none

/-- Decoding every element. -/
def decAll {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: l => (f a).bind fun b => (decAll f l).map (b :: ·)

/-- **An input's model input**: by its kind; a transaction with at most one comparison, three
then- and one else-operation. -/
def decIn (x : Input) : Option (linkv.MIn GoString GoString) :=
  if x.Kind' = W64 0 then some (.get x.Key')
  else if x.Kind' = W64 1 then some .list
  else if x.Kind' = W64 2 then some (.put x.Key' x.Val')
  else if x.Kind' = W64 3 then some (.del x.Key')
  else if x.Kind' = W64 4 ∧ 0 ≤ sint.Z x.NCmps' ∧ sint.Z x.NCmps' ≤ 1 ∧ 0 ≤ sint.Z x.NThen' ∧
      sint.Z x.NThen' ≤ 3 ∧ 0 ≤ sint.Z x.NElse' ∧ sint.Z x.NElse' ≤ 1 then
    (decAll decCmp (cmpsOfL x)).bind fun cs => (decAll decTOp (thenOfL x)).bind fun t =>
      (decAll decTOp (elseOfL x)).map fun e => .txn cs t e
  else none

/-- A transaction operation's key. -/
def mopKey : linkv.MOp GoString GoString → GoString
  | .get k => k
  | .put k _ => k
  | .del k => k

/-- A model input's keys are the workload's. -/
def inKeys : linkv.MIn GoString GoString → Prop
  | .get k => k ∈ wks
  | .list => True
  | .put k _ => k ∈ wks
  | .del k => k ∈ wks
  | .txn _ t e => ∀ op ∈ t ++ e, mopKey op ∈ wks

/-- **An input `Gen` may return**: decodable, its keys the workload's. -/
def ValidIn (x : Input) : Prop := ∃ i, decIn x = some i ∧ inKeys i

/-- A get's value. -/
def decVR (found : Bool) (r : VR) : Option (linkv.VR GoString) :=
  if found then some (absVR r) else none

/-- A transaction operation's result (a kind the model never answers: a count it never gives). -/
def decRes (t : TRes) : linkv.MRes GoString :=
  if t.Kind' = W64 0 then .get (decVR t.Found' t.R')
  else if t.Kind' = W64 1 then .put
  else if t.Kind' = W64 2 then .del (uint.nat t.N')
  else .del (uint.nat t.N' + 2)

/-- A result count the model never gives (four). -/
def badCount (n : w64) : Prop := sint.Z n < 0 ∨ 3 < sint.Z n

/-- **An output's model answer**, by its input's kind (counts outside `[0, 3]` decode to four
results or key-values, which the model never answers). -/
def decOut (kind : w64) (y : Output) : linkv.Ans (linkv.MOut GoString GoString) :=
  if y.Err' then .err
  else .ok (
    if kind = W64 0 then .get (uint.nat y.Rev') (decVR y.Found' y.R')
    else if kind = W64 1 then
      .list (uint.nat y.Rev')
        (if badCount y.NKVs' then List.replicate 4 (go!"", ⟨[], W64 0, W64 0⟩)
         else (kvsOfL y).map fun kv => (kv.Key', absVR kv.R'))
    else if kind = W64 2 then .put (uint.nat y.Rev')
    else if kind = W64 3 then .del (uint.nat y.Rev') (uint.nat y.N')
    else .txn (uint.nat y.Rev') y.Ok'
        (if badCount y.NRes' then List.replicate 4 (.del 2) else (resOfL y).map decRes))

/-! ## The store's helpers, abstracted -/

theorem absStore_cons (e : entry) (es : List entry) (k : GoString) :
    absStore (e :: es) k = if e.key' = k then some (absVR e.r') else absStore es k := by
  unfold absStore
  by_cases h : e.key' = k <;> simp [List.find?_cons, h]

theorem absStore_nil : absStore ([] : List entry) = fun _ => none := rfl

/-- **A lookup's value is the model store's.** -/
theorem lookupL_dec (es : List entry) (k : GoString) :
    decVR (lookupL es k).2 (lookupL es k).1 = absStore es k := by
  unfold lookupL absStore decVR
  cases es.find? (fun e => decide (e.key' = k)) <;> rfl

/-- A key's lookup: found exactly when the model store has it; the zero value otherwise. -/
theorem lookupL_found (es : List entry) (k : GoString) :
    (lookupL es k).2 = (absStore es k).isSome := by
  unfold lookupL absStore
  cases es.find? (fun e => decide (e.key' = k)) <;> rfl

theorem lookupL_none (es : List entry) (k : GoString) (h : (lookupL es k).2 = false) :
    (lookupL es k).1 = zVR := by
  unfold lookupL at h ⊢
  cases hf : es.find? (fun e => decide (e.key' = k)) with
  | none => rfl
  | some e => rw [hf] at h; cases h

theorem lookupL_some (es : List entry) (k : GoString) (v : linkv.VR GoString)
    (h : absStore es k = some v) : (lookupL es k).2 = true ∧ absVR (lookupL es k).1 = v := by
  unfold lookupL
  unfold absStore at h
  cases hf : es.find? (fun e => decide (e.key' = k)) with
  | none => rw [hf] at h; cases h
  | some e => rw [hf] at h; exact ⟨rfl, Option.some.inj h⟩

theorem setStep_done_foldl (k : GoString) (r : VR) (es out : List entry) :
    es.foldl (setStep k r) (out, true) = (out ++ es, true) := by
  induction es generalizing out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, setStep, Bool.true_eq_false, false_and, if_false]
    rw [ih]; simp

theorem setKeyL_foldl (k : GoString) (r : VR) (es out : List entry) :
    setFin k r (es.foldl (setStep k r) (out, false)) = out ++ setR k r es := by
  induction es generalizing out with
  | nil => simp [setR, setFin]
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hle : go.GoStringLe k e.key'
    · by_cases he : e.key' = k
      · have hs : setStep k r (out, false) e = (out ++ [⟨k, r⟩], true) := by
          rw [setStep, if_pos (⟨rfl, hle⟩ : (out, false).2 = false ∧ go.GoStringLe k e.key'),
            if_pos he]
        rw [hs, setStep_done_foldl, setR, if_pos hle, if_pos he]; simp [setFin]
      · have hs : setStep k r (out, false) e = (out ++ [⟨k, r⟩, e], true) := by
          rw [setStep, if_pos (⟨rfl, hle⟩ : (out, false).2 = false ∧ go.GoStringLe k e.key'),
            if_neg he]
        rw [hs, setStep_done_foldl, setR, if_pos hle, if_neg he]; simp [setFin]
    · have hs : setStep k r (out, false) e = (out ++ [e], false) := by
        rw [setStep, if_neg (fun h => hle h.2)]
      rw [hs, ih, setR, if_neg hle]; simp

theorem setKeyL_eq (es : List entry) (k : GoString) (r : VR) : setKeyL es k r = setR k r es := by
  have := setKeyL_foldl k r es []
  simpa [setKeyL] using this

/-- **`setKey` writes the model store.** -/
theorem absStore_setR (k : GoString) (r : VR) (es : List entry) :
    absStore (setR k r es) = fun k' => if k' = k then some (absVR r) else absStore es k' := by
  induction es with
  | nil =>
    funext k'
    simp only [setR, absStore_cons, absStore_nil]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]
  | cons e es ih =>
    funext k'
    simp only [setR]
    by_cases hle : go.GoStringLe k e.key'
    · simp only [hle, if_true]
      by_cases he : e.key' = k
      · simp only [he, if_true, absStore_cons]
        by_cases h : k' = k
        · subst h; simp
        · simp [h, Ne.symm h]
      · simp only [he, if_false, absStore_cons]
        by_cases h : k' = k
        · subst h; simp
        · simp [h, Ne.symm h]
    · simp only [hle, if_false, absStore_cons, ih]
      have hne : e.key' ≠ k := fun h => hle (Or.inl h.symm)
      by_cases h : k' = k
      · subst h; simp [hne]
      · simp [h]

/-- **`delKey` deletes from the model store.** -/
theorem absStore_delKeyL (es : List entry) (k : GoString) :
    absStore (delKeyL es k) = (absStore es).del k := by
  funext k'
  unfold linkv.MStore.del
  induction es with
  | nil => simp [delKeyL, absStore_nil]
  | cons e es ih =>
    unfold delKeyL at ih ⊢
    rw [List.filter_cons]
    by_cases he : e.key' = k
    · simp only [he, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      rw [ih, absStore_cons]
      by_cases h : k' = k
      · simp [h]
      · have hne : ¬ e.key' = k' := fun h' => h (h'.symm.trans he)
        simp [h, hne]
    · simp only [he, decide_false, Bool.not_false, ↓reduceIte]
      rw [absStore_cons, absStore_cons, ih]
      by_cases h : k' = k
      · subst h; simp [he]
      · simp [h]

/-- **`put` puts in the model store** at the revision `n` (`W64 n` as the Go word). -/
theorem absStore_putL (es : List entry) (n : Nat) (k v : GoString) :
    absStore (putL es (W64 (n : Int)) k v) = (absStore es).put n k v := by
  unfold putL linkv.MStore.put
  rw [setKeyL_eq, absStore_setR]
  funext k'
  by_cases h : k' = k
  · subst h
    simp only [ite_true]
    cases hk : absStore es k' with
    | none =>
      have hf := lookupL_found es k'
      rw [hk] at hf
      simp only [Option.isSome_none] at hf
      simp [hf, absVR]
    | some x =>
      obtain ⟨h1, h2⟩ := lookupL_some es k' x hk
      simp only [h1, ite_true, Option.map_some, Option.getD_some, absVR, ← h2]
  · simp [h]

theorem w64_1_ne_0 : (W64 1 : w64) ≠ W64 0 := by decide
theorem w64_2_ne_0 : (W64 2 : w64) ≠ W64 0 := by decide
theorem w64_2_ne_1 : (W64 2 : w64) ≠ W64 1 := by decide

/-- A missing key's version and mod revision are `0`. -/
theorem lookupL_zero (es : List entry) (k : GoString) (h : absStore es k = none) :
    (lookupL es k).1 = zVR ∧ (lookupL es k).2 = false := by
  have hf := lookupL_found es k
  rw [h] at hf
  exact ⟨lookupL_none es k hf, hf⟩

/-- **A comparison's verdict is the model's.** -/
theorem holdsL_dec (es : List entry) (c : Cmp) (c' : linkv.MCmp GoString GoString)
    (h : decCmp c = some c') : holdsL es c = c'.holds (absStore es) := by
  unfold decCmp at h
  unfold holdsL
  by_cases h0 : c.Kind' = W64 0
  · rw [if_pos h0, Option.some.injEq] at h
    subst h
    rw [if_pos h0]
    cases hk : absStore es c.Key' with
    | none => simp only [linkv.MCmp.holds, hk, (lookupL_zero es c.Key' hk).2, Bool.false_and]
    | some x =>
      obtain ⟨h1, h2⟩ := lookupL_some es c.Key' x hk
      simp only [linkv.MCmp.holds, hk, h1, Bool.true_and, ← h2, absVR]
  · rw [if_neg h0] at h
    rw [if_neg h0]
    by_cases h1 : c.Kind' = W64 1
    · rw [if_pos h1, Option.some.injEq] at h
      subst h
      rw [if_pos h1]
      cases hk : absStore es c.Key' with
      | none =>
        simp only [linkv.MCmp.holds, hk, (lookupL_zero es c.Key' hk).1, Option.map_none,
          Option.getD_none, zVR]
      | some x =>
        obtain ⟨-, h2⟩ := lookupL_some es c.Key' x hk
        simp only [linkv.MCmp.holds, hk, Option.map_some, Option.getD_some, ← h2, absVR]
    · rw [if_neg h1] at h
      rw [if_neg h1]
      by_cases h2 : c.Kind' = W64 2
      · rw [if_pos h2, Option.some.injEq] at h
        subst h
        cases hk : absStore es c.Key' with
        | none =>
          simp only [linkv.MCmp.holds, hk, (lookupL_zero es c.Key' hk).1, Option.map_none,
            Option.getD_none, zVR]
        | some x =>
          obtain ⟨-, h3⟩ := lookupL_some es c.Key' x hk
          simp only [linkv.MCmp.holds, hk, Option.map_some, Option.getD_some, ← h3, absVR]
      · rw [if_neg h2] at h; cases h

/-! ## Good stores -/

theorem setR_keys (k : GoString) (r : VR) :
    ∀ es : List entry, ∀ e ∈ setR k r es, e.key' = k ∨ e ∈ es
  | [], e, he => by simp [setR] at he; exact Or.inl (by rw [he])
  | x :: xs, e, he => by
    simp only [setR] at he
    split at he
    · split at he
      · rcases List.mem_cons.1 he with rfl | he
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ he)
      · rcases List.mem_cons.1 he with rfl | he
        · exact Or.inl rfl
        · exact Or.inr he
    · rcases List.mem_cons.1 he with rfl | he
      · exact Or.inr List.mem_cons_self
      · rcases setR_keys k r xs e he with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `setKey` keeps the entries sorted strictly. -/
theorem setR_sorted (k : GoString) (r : VR) :
    ∀ es : List entry, (es.map entry.key').Pairwise go.GoStringLt →
      ((setR k r es).map entry.key').Pairwise go.GoStringLt
  | [], _ => by simp [setR]
  | x :: xs, hs => by
    rw [List.map_cons, List.pairwise_cons] at hs
    simp only [setR]
    by_cases hle : go.GoStringLe k x.key'
    · simp only [hle, ite_true]
      by_cases he : x.key' = k
      · simp only [he, ite_true, List.map_cons, List.pairwise_cons]
        refine ⟨?_, hs.2⟩
        intro a ha
        rw [← he]
        exact hs.1 a ha
      · simp only [he, ite_false, List.map_cons, List.pairwise_cons]
        have hlt : go.GoStringLt k x.key' := hle.resolve_left (fun h => he h.symm)
        refine ⟨?_, hs.1, hs.2⟩
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hlt
        · exact go.goStringLt_trans hlt (hs.1 a ha)
    · simp only [hle, ite_false, List.map_cons, List.pairwise_cons]
      refine ⟨?_, setR_sorted k r xs hs.2⟩
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨e, he, rfl⟩ := ha
      rcases setR_keys k r xs e he with h | h
      · rw [h]
        have h1 : ¬ go.GoStringLt k x.key' := fun h' => hle (Or.inr h')
        have h2 : x.key' ≠ k := fun h' => hle (Or.inl h'.symm)
        by_cases h3 : go.GoStringLt x.key' k
        · exact h3
        · exact absurd (go.goStringLt_eq_of_not_lt h3 h1) h2
      · exact hs.1 _ (List.mem_map_of_mem h)

theorem goodSt_setR (st : GSt) (h : GoodSt st) (k : GoString) (hk : k ∈ wks) (r : VR) (rev : w64) :
    GoodSt ⟨setR k r st.kvs, rev⟩ := by
  refine ⟨setR_sorted k r st.kvs h.1, ?_⟩
  intro e he
  rcases setR_keys k r st.kvs e he with h' | h'
  · rw [h']; exact hk
  · exact h.2 e h'

theorem goodSt_delKeyL (st : GSt) (h : GoodSt st) (k : GoString) (rev : w64) :
    GoodSt ⟨delKeyL st.kvs k, rev⟩ :=
  ⟨List.Pairwise.sublist (List.filter_sublist.map _) h.1,
    fun e he => h.2 e (List.mem_filter.1 he).1⟩

theorem goodSt_putL (st : GSt) (h : GoodSt st) (r : w64) (k v : GoString) (hk : k ∈ wks)
    (rev : w64) : GoodSt ⟨putL st.kvs r k v, rev⟩ := by
  unfold putL
  rw [setKeyL_eq]
  exact goodSt_setR st h k hk _ rev

/-! ## A transaction's operations -/

/-- A result's model result. -/
theorem decRes_getRes (p : VR × Bool) : decRes (getRes p) = .get (decVR p.2 p.1) := rfl

theorem decRes_putRes : decRes putRes = .put := by
  simp [decRes, putRes, w64_1_ne_0]

theorem decRes_delRes (n : w64) : decRes (delRes n) = .del (uint.nat n) := by
  simp [decRes, delRes, w64_2_ne_0, w64_2_ne_1]

/-- **A transaction's operations, run from an accumulator**: the store after them is the model's,
the results the model's after the accumulated ones, the changed flag the model's or the
accumulated one; the store stays good. -/
theorem runOpsL_abs (n : Nat) :
    ∀ (ops : List TOp) (ops' : List (linkv.MOp GoString GoString)) (es : List entry)
      (pre : List TRes) (ch : Bool),
      decAll decTOp ops = some ops' → GoodSt ⟨es, W64 0⟩ → (∀ op ∈ ops', mopKey op ∈ wks) →
      absStore (ops.foldl (runStep (W64 (n : Int))) (es, pre, ch)).1 =
          (linkv.runOps n (absStore es) ops').1 ∧
        (ops.foldl (runStep (W64 (n : Int))) (es, pre, ch)).2.1.map decRes =
          pre.map decRes ++ (linkv.runOps n (absStore es) ops').2.1 ∧
        (ops.foldl (runStep (W64 (n : Int))) (es, pre, ch)).2.2 =
          (ch || (linkv.runOps n (absStore es) ops').2.2) ∧
        GoodSt ⟨(ops.foldl (runStep (W64 (n : Int))) (es, pre, ch)).1, W64 0⟩ ∧
        (ops.foldl (runStep (W64 (n : Int))) (es, pre, ch)).2.1.length = pre.length + ops.length
  | [], ops', es, pre, ch, hd, hg, _ => by
    simp only [decAll, Option.some.injEq] at hd
    subst hd
    exact ⟨by simp [linkv.runOps], by simp [linkv.runOps], by simp [linkv.runOps], hg, by simp⟩
  | op :: ops, ops', es, pre, ch, hd, hg, hk => by
    simp only [decAll] at hd
    cases hop : decTOp op with
    | none => rw [hop] at hd; cases hd
    | some o =>
      rw [hop] at hd
      cases hrest : decAll decTOp ops with
      | none => rw [hrest] at hd; cases hd
      | some os =>
        rw [hrest] at hd
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hd
        subst hd
        have hk1 : mopKey o ∈ wks := hk o List.mem_cons_self
        have hk2 : ∀ op ∈ os, mopKey op ∈ wks := fun x hx => hk x (List.mem_cons_of_mem _ hx)
        unfold decTOp at hop
        simp only [List.foldl_cons, linkv.runOps]
        by_cases h0 : op.Kind' = W64 0
        · rw [if_pos h0, Option.some.injEq] at hop
          subst hop
          have hs : runStep (W64 (n : Int)) (es, pre, ch) op =
              (es, pre ++ [getRes (lookupL es op.Key')], ch) := by
            unfold runStep; rw [if_pos h0]
          rw [hs]
          obtain ⟨i1, i2, i3, i4, i5⟩ := runOpsL_abs n ops os es _ ch hrest hg hk2
          refine ⟨i1, ?_, ?_, i4, ?_⟩
          · rw [i2]; simp [linkv.MOp.run, decRes_getRes, lookupL_dec]
          · rw [i3]; simp [linkv.MOp.run]
          · rw [i5]; simp; omega
        · rw [if_neg h0] at hop
          by_cases h1 : op.Kind' = W64 1
          · rw [if_pos h1, Option.some.injEq] at hop
            subst hop
            have hs : runStep (W64 (n : Int)) (es, pre, ch) op =
                (putL es (W64 (n : Int)) op.Key' op.Val', pre ++ [putRes], true) := by
              unfold runStep; rw [if_neg h0, if_pos h1]
            rw [hs]
            have hg' := goodSt_putL ⟨es, W64 0⟩ hg (W64 (n : Int)) op.Key' op.Val' hk1 (W64 0)
            obtain ⟨i1, i2, i3, i4, i5⟩ := runOpsL_abs n ops os _ _ true hrest hg' hk2
            rw [absStore_putL] at i1 i2 i3
            refine ⟨i1, ?_, ?_, i4, ?_⟩
            · rw [i2]; simp [linkv.MOp.run, decRes_putRes]
            · rw [i3]; simp [linkv.MOp.run]
            · rw [i5]; simp; omega
          · rw [if_neg h1] at hop
            by_cases h2 : op.Kind' = W64 2
            · rw [if_pos h2, Option.some.injEq] at hop
              subst hop
              cases hk : absStore es op.Key' with
              | none =>
                have hl := (lookupL_zero es op.Key' hk).2
                have hs : runStep (W64 (n : Int)) (es, pre, ch) op =
                    (es, pre ++ [delRes (W64 0)], ch) := by
                  unfold runStep; rw [if_neg h0, if_neg h1, hl]; rfl
                rw [hs]
                obtain ⟨i1, i2, i3, i4, i5⟩ := runOpsL_abs n ops os es _ ch hrest hg hk2
                simp only [linkv.MOp.run, hk]
                refine ⟨i1, ?_, ?_, i4, ?_⟩
                · rw [i2]; simp [decRes_delRes]
                · first | (rw [i3]; simp) | rw [i3]
                · rw [i5]; simp; omega
              | some x =>
                have hl := (lookupL_some es op.Key' x hk).1
                have hs : runStep (W64 (n : Int)) (es, pre, ch) op =
                    (delKeyL es op.Key', pre ++ [delRes (W64 1)], true) := by
                  unfold runStep; rw [if_neg h0, if_neg h1, if_pos hl]
                rw [hs]
                have hg' := goodSt_delKeyL ⟨es, W64 0⟩ hg op.Key' (W64 0)
                obtain ⟨i1, i2, i3, i4, i5⟩ := runOpsL_abs n ops os _ _ true hrest hg' hk2
                rw [absStore_delKeyL] at i1 i2 i3
                simp only [linkv.MOp.run, hk]
                refine ⟨i1, ?_, ?_, i4, ?_⟩
                · rw [i2]; simp [decRes_delRes]
                · rw [i3]; simp
                · rw [i5]; simp; omega
            · rw [if_neg h2] at hop; cases hop

/-! ## The list, and the fields as lists -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr' xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **The model lists a good store's entries.** -/
theorem filterMap_absStore (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) :
    ∀ (es : List entry), (es.map entry.key').Pairwise go.GoStringLt → (∀ e ∈ es, e.key' ∈ ks) →
      ks.filterMap (fun k => (absStore es k).map fun x => (k, x)) =
        es.map fun e => (e.key', absVR e.r') := by
  induction ks with
  | nil =>
    intro es _ h
    cases es with
    | nil => rfl
    | cons w ws => exact absurd (h w List.mem_cons_self) (by simp)
  | cons k ks ih =>
    intro es hs h
    rw [List.pairwise_cons] at hks
    have hlt : ∀ k' ∈ ks, go.GoStringLt k k' := hks.1
    cases es with
    | nil =>
      simp only [List.filterMap_cons, absStore_nil, Option.map_none, List.map_nil]
      rw [List.filterMap_eq_nil_iff]
      intro _ _; rfl
    | cons w ws =>
      rw [List.map_cons, List.pairwise_cons] at hs
      have hw := h w List.mem_cons_self
      have hws : ∀ e ∈ ws, go.GoStringLt w.key' e.key' :=
        fun e he => hs.1 _ (List.mem_map_of_mem he)
      have hrest : ∀ k' ∈ ks, w.key' ≠ k' → absStore (w :: ws) k' = absStore ws k' := by
        intro k' _ hne
        rw [absStore_cons, if_neg hne]
      rcases List.mem_cons.1 hw with hwk | hwk
      · have h1 : absStore (w :: ws) k = some (absVR w.r') := by
          rw [absStore_cons, if_pos hwk]
        have hws' : ∀ e ∈ ws, e.key' ∈ ks := by
          intro e he
          rcases List.mem_cons.1 (h e (List.mem_cons_of_mem _ he)) with h2 | h2
          · exfalso
            have := hws e he
            rw [hwk, ← h2] at this
            exact go.goStringLt_irrefl _ this
          · exact h2
        have hcongr : ks.filterMap (fun k' => (absStore (w :: ws) k').map fun x => (k', x)) =
            ks.filterMap (fun k' => (absStore ws k').map fun x => (k', x)) := by
          apply filterMap_congr'
          intro k' hk'
          rw [hrest k' hk' (by rw [hwk]; exact fun e => go.goStringLt_irrefl _ (e ▸ hlt k' hk'))]
        simp only [List.filterMap_cons, h1, Option.map_some, List.map_cons, hcongr, hwk]
        rw [ih hks.2 ws hs.2 hws']
      · have hk0 : absStore (w :: ws) k = none := by
          rw [absStore_cons]
          have hne : w.key' ≠ k := fun e => go.goStringLt_irrefl _ (e ▸ hlt _ hwk)
          rw [if_neg hne]
          unfold absStore
          have : ws.find? (fun e => decide (e.key' = k)) = none := by
            rw [List.find?_eq_none]
            intro e he hek
            simp only [decide_eq_true_eq] at hek
            have h3 := hws e he
            rw [hek] at h3
            exact go.goStringLt_irrefl _ (go.goStringLt_trans (hlt _ hwk) h3)
          rw [this]; rfl
        have hall : ∀ e ∈ w :: ws, e.key' ∈ ks := by
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact hwk
          · rcases List.mem_cons.1 (h e (List.mem_cons_of_mem _ he)) with h2 | h2
            · exfalso
              have := hws e he
              rw [h2] at this
              exact go.goStringLt_irrefl _ (go.goStringLt_trans (hlt _ hwk) this)
            · exact h2
        simp only [List.filterMap_cons, hk0, Option.map_none]
        exact ih hks.2 (w :: ws) (by rw [List.map_cons]; exact List.pairwise_cons.2 hs) hall

theorem wks_sorted : wks.Pairwise go.GoStringLt := by decide

/-- A good store has at most three entries. -/
theorem goodSt_length (st : GSt) (h : GoodSt st) : st.kvs.length ≤ 3 := by
  have := filterMap_absStore wks wks_sorted st.kvs h.1 h.2
  have hl := congrArg List.length this
  rw [List.length_map] at hl
  rw [← hl]
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem kvsOfL_withKVsL (o : Output) (l : List KV) (h : l.length ≤ 3) :
    kvsOfL (withKVsL o l) = l ∧ ¬ badCount (withKVsL o l).NKVs' := by
  have hz : sint.Z (W64 (l.length : Int)) = l.length := by
    have : (l.length : Int) < 2 ^ 63 := by omega
    word
  refine ⟨?_, ?_⟩
  · unfold kvsOfL withKVsL
    simp only [hz]
    match l, h with
    | [], _ => simp
    | [a], _ => simp
    | [a, b], _ => simp
    | [a, b, c], _ => simp
  · unfold badCount withKVsL; simp only [hz]; omega

theorem resOfL_withResL (o : Output) (l : List TRes) (h : l.length ≤ 3) :
    resOfL (withResL o l) = l ∧ ¬ badCount (withResL o l).NRes' := by
  have hz : sint.Z (W64 (l.length : Int)) = l.length := by
    have : (l.length : Int) < 2 ^ 63 := by omega
    word
  refine ⟨?_, ?_⟩
  · unfold resOfL withResL
    simp only [hz]
    match l, h with
    | [], _ => simp
    | [a], _ => simp
    | [a, b], _ => simp
    | [a, b, c], _ => simp
  · unfold badCount withResL; simp only [hz]; omega

theorem thenOfL_length (x : Input) : (thenOfL x).length ≤ 3 := by
  unfold thenOfL; split <;> split <;> split <;> simp

theorem elseOfL_length (x : Input) : (elseOfL x).length ≤ 3 := by
  unfold elseOfL; split <;> simp

/-! ## One operation -/

theorem cmpsOk_dec (es : List entry) :
    ∀ (cs : List Cmp) (cs' : List (linkv.MCmp GoString GoString)), decAll decCmp cs = some cs' →
      cmpsOk es cs = cs'.all (linkv.MCmp.holds (absStore es))
  | [], cs', h => by simp only [decAll, Option.some.injEq] at h; subst h; rfl
  | c :: cs, cs', h => by
    simp only [decAll] at h
    cases hc : decCmp c with
    | none => rw [hc] at h; cases h
    | some c' =>
      rw [hc] at h
      cases hr : decAll decCmp cs with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        unfold cmpsOk at *
        simp only [List.all_cons, holdsL_dec es c c' hc]
        rw [← cmpsOk_dec es cs r hr]
        rfl

/-- **What a decoded input is**: its kind and fields. -/
theorem decIn_cases (x : Input) (i : linkv.MIn GoString GoString) (h : decIn x = some i) :
    (x.Kind' = W64 0 ∧ i = .get x.Key') ∨ (x.Kind' = W64 1 ∧ i = .list) ∨
      (x.Kind' = W64 2 ∧ i = .put x.Key' x.Val') ∨ (x.Kind' = W64 3 ∧ i = .del x.Key') ∨
      (x.Kind' = W64 4 ∧ ∃ cs t e, i = .txn cs t e ∧ decAll decCmp (cmpsOfL x) = some cs ∧
        decAll decTOp (thenOfL x) = some t ∧ decAll decTOp (elseOfL x) = some e) := by
  unfold decIn at h
  by_cases h0 : x.Kind' = W64 0
  · rw [if_pos h0] at h; exact Or.inl ⟨h0, (Option.some.inj h).symm⟩
  rw [if_neg h0] at h
  by_cases h1 : x.Kind' = W64 1
  · rw [if_pos h1] at h; exact Or.inr (Or.inl ⟨h1, (Option.some.inj h).symm⟩)
  rw [if_neg h1] at h
  by_cases h2 : x.Kind' = W64 2
  · rw [if_pos h2] at h; exact Or.inr (Or.inr (Or.inl ⟨h2, (Option.some.inj h).symm⟩))
  rw [if_neg h2] at h
  by_cases h3 : x.Kind' = W64 3
  · rw [if_pos h3] at h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, (Option.some.inj h).symm⟩)))
  rw [if_neg h3] at h
  split at h
  · rename_i hk
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hk.1, ?_⟩)))
    cases e1 : decAll decCmp (cmpsOfL x) with
    | none => rw [e1] at h; cases h
    | some cs =>
      cases e2 : decAll decTOp (thenOfL x) with
      | none => simp [e1, e2] at h
      | some t =>
        cases e3 : decAll decTOp (elseOfL x) with
        | none => simp [e1, e2, e3] at h
        | some e =>
          simp only [e1, e2, e3, Option.bind_some, Option.map_some, Option.some.injEq] at h
          exact ⟨cs, t, e, h.symm, rfl, rfl, rfl⟩
  · cases h

theorem w64_succ_eq (r : w64) : r + W64 1 = W64 ((uint.nat r + 1 : Nat) : Int) := by
  unfold uint.nat; word

theorem uint_nat_succ (r : w64) (h : uint.Z r + 1 < 2 ^ 64) : uint.nat (r + W64 1) = uint.nat r + 1 := by
  unfold uint.nat; word

/-- **`mstep` is the model's step** on a good store, for a decodable input of the workload's keys
(a revision below `2^64 - 1`): the store after it, the output decoded, and the store stays good. -/
theorem mstepL_abs (x : Input) (i : linkv.MIn GoString GoString) (hx : decIn x = some i)
    (hk : inKeys i) (st : GSt) (hg : GoodSt st) (hr : uint.Z st.rev + 1 < 2 ^ 64) :
    absSt (mstepL x st).1 = (linkv.mStep wks i (absSt st)).1 ∧
      decOut x.Kind' (mstepL x st).2 = .ok (linkv.mStep wks i (absSt st)).2 ∧
      GoodSt (mstepL x st).1 := by
  have h1 := uint_nat_succ st.rev hr
  have hW := w64_succ_eq st.rev
  have n10 : (W64 1 : w64) ≠ W64 0 := by decide
  have n20 : (W64 2 : w64) ≠ W64 0 := by decide
  have n21 : (W64 2 : w64) ≠ W64 1 := by decide
  have n30 : (W64 3 : w64) ≠ W64 0 := by decide
  have n31 : (W64 3 : w64) ≠ W64 1 := by decide
  have n32 : (W64 3 : w64) ≠ W64 2 := by decide
  have n40 : (W64 4 : w64) ≠ W64 0 := by decide
  have n41 : (W64 4 : w64) ≠ W64 1 := by decide
  have n42 : (W64 4 : w64) ≠ W64 2 := by decide
  have n43 : (W64 4 : w64) ≠ W64 3 := by decide
  rcases decIn_cases x i hx with ⟨hk0, rfl⟩ | ⟨hk0, rfl⟩ | ⟨hk0, rfl⟩ | ⟨hk0, rfl⟩ |
    ⟨hk0, cs, t, e, rfl, hcs, ht, he⟩
  · -- a get
    unfold mstepL
    rw [if_pos hk0]
    refine ⟨rfl, ?_, hg⟩
    unfold decOut
    simp only [zOut, Bool.false_eq_true, ↓reduceIte, hk0]
    rw [lookupL_dec]; rfl
  · -- a list
    unfold mstepL
    rw [if_neg (by rw [hk0]; exact n10), if_pos hk0]
    refine ⟨rfl, ?_, hg⟩
    have hlen : (st.kvs.map fun e => (⟨e.key', e.r'⟩ : KV)).length ≤ 3 := by
      rw [List.length_map]; exact goodSt_length st hg
    obtain ⟨hk1, hb⟩ := kvsOfL_withKVsL { zOut with Rev' := st.rev } _ hlen
    unfold decOut
    have herr : (withKVsL { zOut with Rev' := st.rev }
        (st.kvs.map fun e => (⟨e.key', e.r'⟩ : KV))).Err' = false := rfl
    rw [herr, if_neg Bool.false_ne_true, if_neg (by rw [hk0]; exact n10), if_pos hk0, if_neg hb,
      hk1, List.map_map]
    simp only [linkv.mStep, absSt]
    rw [filterMap_absStore wks wks_sorted st.kvs hg.1 hg.2]
    rfl
  · -- a put
    unfold mstepL
    rw [if_neg (by rw [hk0]; exact n20), if_neg (by rw [hk0]; exact n21), if_pos hk0]
    have hkk : x.Key' ∈ wks := hk
    refine ⟨?_, ?_, goodSt_putL st hg _ _ _ hkk _⟩
    · unfold absSt
      simp only [linkv.mStep]
      rw [h1, hW, absStore_putL]
    · unfold decOut
      simp only [zOut, Bool.false_eq_true, ↓reduceIte, hk0, n20, n21]
      rw [h1]; rfl
  · -- a delete
    unfold mstepL
    rw [if_neg (by rw [hk0]; exact n30), if_neg (by rw [hk0]; exact n31),
      if_neg (by rw [hk0]; exact n32), if_pos hk0]
    cases hkv : absStore st.kvs x.Key' with
    | none =>
      have hl := (lookupL_zero st.kvs x.Key' hkv).2
      rw [hl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, hg⟩
      · simp only [linkv.mStep, absSt, hkv]
      · unfold decOut
        simp only [zOut, Bool.false_eq_true, ↓reduceIte, hk0, n30, n31, n32]
        simp only [linkv.mStep, absSt, hkv]
        rfl
    | some v =>
      have hl := (lookupL_some st.kvs x.Key' v hkv).1
      rw [hl]
      simp only [↓reduceIte]
      refine ⟨?_, ?_, goodSt_delKeyL st hg _ _⟩
      · unfold absSt
        simp only [linkv.mStep, absSt, hkv]
        rw [h1, absStore_delKeyL]
      · unfold decOut
        simp only [zOut, Bool.false_eq_true, ↓reduceIte, hk0, n30, n31, n32]
        simp only [linkv.mStep, absSt, hkv]
        rw [h1]; rfl
  · -- a transaction
    unfold mstepL
    rw [if_neg (by rw [hk0]; exact n40), if_neg (by rw [hk0]; exact n41),
      if_neg (by rw [hk0]; exact n42), if_neg (by rw [hk0]; exact n43)]
    have hok := cmpsOk_dec st.kvs (cmpsOfL x) cs hcs
    have hgood : GoodSt ⟨st.kvs, W64 0⟩ := ⟨hg.1, hg.2⟩
    have hkeys : ∀ op ∈ t ++ e, mopKey op ∈ wks := hk
    -- the branch, Go's and the model's
    have hbr : ∀ b : Bool, decAll decTOp (if b then thenOfL x else elseOfL x) =
        some (if b then t else e) := by
      intro b; cases b <;> simp [ht, he]
    have hbk : ∀ b : Bool, ∀ op ∈ (if b then t else e), mopKey op ∈ wks := by
      intro b op hop
      apply hkeys
      cases b
      · exact List.mem_append_right _ hop
      · exact List.mem_append_left _ hop
    have hbl : ∀ b : Bool, (if b then thenOfL x else elseOfL x).length ≤ 3 := by
      intro b; cases b
      · exact elseOfL_length x
      · exact thenOfL_length x
    generalize hb : cmpsOk st.kvs (cmpsOfL x) = b at hok ⊢
    obtain ⟨i1, i2, i3, i4, i5⟩ := runOpsL_abs (uint.nat st.rev + 1)
      (if b then thenOfL x else elseOfL x) (if b then t else e) st.kvs [] false (hbr b) hgood
      (hbk b)
    have hq : runOpsL st.kvs (st.rev + W64 1) (if b then thenOfL x else elseOfL x) =
        (if b then thenOfL x else elseOfL x).foldl (runStep (W64 ((uint.nat st.rev + 1 : Nat) : Int)))
          (st.kvs, [], false) := by
      unfold runOpsL; rw [hW]
    simp only [hq]
    generalize hQ : (if b then thenOfL x else elseOfL x).foldl
      (runStep (W64 ((uint.nat st.rev + 1 : Nat) : Int))) (st.kvs, [], false) = Q at i1 i2 i3 i4 i5
    simp only [List.map_nil, List.nil_append, Bool.false_or, List.length_nil, Nat.zero_add] at i2 i3 i5
    have hlen : Q.2.1.length ≤ 3 := by rw [i5]; exact hbl b
    obtain ⟨hr1, hr2⟩ := resOfL_withResL
      { zOut with Rev' := if Q.2.2 then st.rev + W64 1 else st.rev, Ok' := b } Q.2.1 hlen
    simp only [linkv.mStep, absSt, ← hok]
    refine ⟨?_, ?_, ⟨i4.1, i4.2⟩⟩
    · rw [i1, i3]
      congr 1
      cases (linkv.runOps (uint.nat st.rev + 1) (absStore st.kvs) (if b then t else e)).2.2
      · rfl
      · simp only [ite_true]; exact h1
    · unfold decOut
      have herr : (withResL { zOut with Rev' := if Q.2.2 then st.rev + W64 1 else st.rev, Ok' := b }
          Q.2.1).Err' = false := rfl
      rw [herr, if_neg Bool.false_ne_true, if_neg (by rw [hk0]; exact n40),
        if_neg (by rw [hk0]; exact n41), if_neg (by rw [hk0]; exact n42),
        if_neg (by rw [hk0]; exact n43), if_neg hr2, hr1, i2]
      have hrv : (withResL { zOut with Rev' := if Q.2.2 then st.rev + W64 1 else st.rev, Ok' := b }
          Q.2.1).Rev' = if Q.2.2 then st.rev + W64 1 else st.rev := rfl
      have hok' : (withResL { zOut with Rev' := if Q.2.2 then st.rev + W64 1 else st.rev, Ok' := b }
          Q.2.1).Ok' = b := rfl
      rw [hrv, hok', i3]
      cases (linkv.runOps (uint.nat st.rev + 1) (absStore st.kvs) (if b then t else e)).2.2
      · rfl
      · simp only [ite_true]; rw [h1]

end go

end linkvtxn
end EtcdGrove
end Perennial
