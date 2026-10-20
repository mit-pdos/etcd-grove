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

end go

end linkvtxn
end EtcdGrove
end Perennial
