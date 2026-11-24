/-
Pure facts about the replicas' execution of the decided log (`execIds`, `execLog`), for the SMR
laws (package `kit`): one id at a time (`execOne`), the ids executed, the results of an executed
id are fixed, the execution depends only on the batches of the log's ids, the store is the
newest put of each key (`kvAbs` of the puts, newest first), the provenance of the puts, and the
UTF-8 facts of the answers.
-/
module

public import Dsverify.Proof.raxos.Msg

@[expose] public section

noncomputable section

namespace Perennial.raxos.pure

open Perennial.raxos.msg (strOk validUtf8 batchOk asciiOk)

/-! ## One id at a time -/

/-- One id of a slot executed (the body of `execIds`). -/
def execOne (B : GoString → Option Batch) (es : ExecSt) (x : GoString) : ExecSt :=
  if x ∈ es.done then es
  else
    let cmds := (B x).map Batch.cmds |>.getD []
    ⟨(execBatch es.store cmds).1, es.done ++ [x],
      fun y => if y = x then some (execBatch es.store cmds).2 else es.results y,
      es.puts ++ cmds.filterMap cmdPut⟩

theorem execIds_nil (B : GoString → Option Batch) (es : ExecSt) : execIds B es [] = es := rfl

theorem execIds_cons (B : GoString → Option Batch) (es : ExecSt) (x : GoString)
    (xs : List GoString) : execIds B es (x :: xs) = execIds B (execOne B es x) xs := by
  simp only [execIds, execOne]
  split <;> rfl

theorem execIds_append (B : GoString → Option Batch) (es : ExecSt) (xs ys : List GoString) :
    execIds B es (xs ++ ys) = execIds B (execIds B es xs) ys := by
  induction xs generalizing es with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, execIds_cons, ih]

theorem execLog_snoc (B : GoString → Option Batch) (L : List (List GoString))
    (ids : List GoString) : execLog B (L ++ [ids]) = execIds B (execLog B L) ids := by
  simp [execLog, List.foldl_append]

theorem execLog_append (B : GoString → Option Batch) (L M : List (List GoString)) :
    execLog B (L ++ M) = M.foldl (execIds B) (execLog B L) := by
  simp [execLog, List.foldl_append]

/-! ## The ids executed -/

theorem execOne_done (B : GoString → Option Batch) (es : ExecSt) (x y : GoString) :
    y ∈ (execOne B es x).done ↔ y ∈ es.done ∨ y = x := by
  unfold execOne
  split
  · constructor
    · exact Or.inl
    · rintro (h | rfl) <;> assumption
  · simp

theorem execIds_done (B : GoString → Option Batch) (es : ExecSt) (xs : List GoString)
    (y : GoString) : y ∈ (execIds B es xs).done ↔ y ∈ es.done ∨ y ∈ xs := by
  induction xs generalizing es with
  | nil => simp [execIds_nil]
  | cons x xs ih =>
    rw [execIds_cons, ih, execOne_done]
    simp only [List.mem_cons, or_assoc]

theorem foldl_done (B : GoString → Option Batch) (L : List (List GoString)) (es : ExecSt)
    (y : GoString) : y ∈ (L.foldl (execIds B) es).done ↔ y ∈ es.done ∨ y ∈ L.flatten := by
  induction L generalizing es with
  | nil => simp
  | cons ids L ih =>
    simp only [List.foldl_cons, ih, execIds_done, List.flatten_cons, List.mem_append, or_assoc]

theorem execLog_done (B : GoString → Option Batch) (L : List (List GoString)) (y : GoString) :
    y ∈ (execLog B L).done ↔ y ∈ L.flatten := by
  unfold execLog; rw [foldl_done]; simp [ExecSt.init]

/-! ## Results of executed ids are fixed -/

theorem execOne_results_old (B : GoString → Option Batch) (es : ExecSt) (x y : GoString)
    (hy : y ∈ es.done) : (execOne B es x).results y = es.results y := by
  unfold execOne
  split
  · rfl
  · rename_i hx
    have : y ≠ x := fun h => hx (h ▸ hy)
    simp [this]

theorem execIds_results_old (B : GoString → Option Batch) (es : ExecSt) (xs : List GoString)
    (y : GoString) (hy : y ∈ es.done) : (execIds B es xs).results y = es.results y := by
  induction xs generalizing es with
  | nil => rfl
  | cons x xs ih =>
    rw [execIds_cons, ih _ ((execOne_done B es x y).2 (Or.inl hy)),
      execOne_results_old B es x y hy]

theorem execLog_results_prefix (B : GoString → Option Batch) (L M : List (List GoString))
    (y : GoString) (hy : y ∈ (execLog B L).done) :
    (execLog B (L ++ M)).results y = (execLog B L).results y := by
  rw [execLog_append]
  generalize execLog B L = es at hy ⊢
  induction M generalizing es with
  | nil => rfl
  | cons ids M ih =>
    simp only [List.foldl_cons]
    rw [ih _ ((execIds_done B es ids y).2 (Or.inl hy)), execIds_results_old B es ids y hy]

/-! ## Only the batches of the log's ids matter -/

theorem execOne_congr (B B' : GoString → Option Batch) (es : ExecSt) (x : GoString)
    (h : B x = B' x) : execOne B es x = execOne B' es x := by
  unfold execOne; rw [h]

theorem execIds_congr (B B' : GoString → Option Batch) (es : ExecSt) (xs : List GoString)
    (h : ∀ x ∈ xs, B x = B' x) : execIds B es xs = execIds B' es xs := by
  induction xs generalizing es with
  | nil => rfl
  | cons x xs ih =>
    rw [execIds_cons, execIds_cons, execOne_congr B B' es x (h x (by simp)),
      ih _ (fun y hy => h y (by simp [hy]))]

theorem execLog_congr (B B' : GoString → Option Batch) (L : List (List GoString))
    (h : ∀ x ∈ L.flatten, B x = B' x) : execLog B L = execLog B' L := by
  unfold execLog
  generalize ExecSt.init = es
  induction L generalizing es with
  | nil => rfl
  | cons ids L ih =>
    simp only [List.foldl_cons]
    rw [execIds_congr B B' es ids (fun x hx => h x (by simp [hx])),
      ih (fun x hx => h x (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hx))]

/-! ## The store is the newest put of each key -/

theorem kvAbs_nil : kvAbs ([] : List (GoString × GoString)) = fun _ => none := by
  funext k; rfl

theorem execCmd_store (l : List (GoString × GoString)) (c : GoString) :
    (execCmd (kvAbs l.reverse) c).1 = kvAbs (l ++ [c].filterMap cmdPut).reverse := by
  unfold execCmd cmdPut
  split
  · rename_i h
    simp only [List.filterMap_cons, List.filterMap_nil, h, ite_true, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    rw [kvAbs_put]
  · rename_i h
    simp [h]

theorem execBatch_store (l : List (GoString × GoString)) (cmds : List GoString) :
    (execBatch (kvAbs l.reverse) cmds).1 = kvAbs (l ++ cmds.filterMap cmdPut).reverse := by
  induction cmds generalizing l with
  | nil => simp [execBatch]
  | cons c cs ih =>
    simp only [execBatch]
    rw [execCmd_store, ih]
    congr 2
    rw [List.append_assoc, ← List.filterMap_append]
    rfl

/-- The store of an execution state is its puts' map, newest first. -/
def storeOk (es : ExecSt) : Prop := es.store = kvAbs es.puts.reverse

theorem execOne_storeOk (B : GoString → Option Batch) (es : ExecSt) (x : GoString)
    (h : storeOk es) : storeOk (execOne B es x) := by
  unfold execOne
  split
  · exact h
  · unfold storeOk at h ⊢
    simp only [h]
    exact execBatch_store _ _

theorem execIds_storeOk (B : GoString → Option Batch) (es : ExecSt) (xs : List GoString)
    (h : storeOk es) : storeOk (execIds B es xs) := by
  induction xs generalizing es with
  | nil => exact h
  | cons x xs ih => rw [execIds_cons]; exact ih _ (execOne_storeOk B es x h)

theorem execLog_storeOk (B : GoString → Option Batch) (L : List (List GoString)) :
    storeOk (execLog B L) := by
  unfold execLog
  have h0 : storeOk ExecSt.init := by
    show (fun _ => none) = _; simp [ExecSt.init, kvAbs_nil]
  generalize ExecSt.init = es at h0
  induction L generalizing es with
  | nil => exact h0
  | cons ids L ih => exact ih _ (execIds_storeOk B es ids h0)

/-! ## Where the puts come from -/

/-- Every put of an execution state comes from a command of an executed batch. -/
def putsFrom (B : GoString → Option Batch) (es : ExecSt) : Prop :=
  ∀ p ∈ es.puts, ∃ x ∈ es.done, ∃ b, B x = some b ∧ ∃ c ∈ b.cmds, cmdPut c = some p

theorem execOne_putsFrom (B : GoString → Option Batch) (es : ExecSt) (x : GoString)
    (h : putsFrom B es) : putsFrom B (execOne B es x) := by
  intro p hp
  unfold execOne at hp ⊢
  split at hp
  · rename_i hx; simp only [hx, ite_true]; exact h p hp
  · rename_i hx
    simp only [hx, ite_false, List.mem_append, List.mem_singleton] at hp ⊢
    rcases hp with hp | hp
    · obtain ⟨y, hy, b, hb, c, hc, hcp⟩ := h p hp
      exact ⟨y, Or.inl hy, b, hb, c, hc, hcp⟩
    · cases hB : B x with
      | none => simp [hB] at hp
      | some b =>
        simp only [hB, Option.map_some, Option.getD_some, List.mem_filterMap] at hp
        obtain ⟨c, hc, hcp⟩ := hp
        exact ⟨x, Or.inr rfl, b, hB, c, hc, hcp⟩

theorem execIds_putsFrom (B : GoString → Option Batch) (es : ExecSt) (xs : List GoString)
    (h : putsFrom B es) : putsFrom B (execIds B es xs) := by
  induction xs generalizing es with
  | nil => exact h
  | cons x xs ih => rw [execIds_cons]; exact ih _ (execOne_putsFrom B es x h)

theorem execLog_putsFrom (B : GoString → Option Batch) (L : List (List GoString)) :
    putsFrom B (execLog B L) := by
  unfold execLog
  have h0 : putsFrom B ExecSt.init := by intro p hp; simp [ExecSt.init] at hp
  generalize ExecSt.init = es at h0
  induction L generalizing es with
  | nil => exact h0
  | cons ids L ih => exact ih _ (execIds_putsFrom B es ids h0)

theorem kvAbs_mem (l : List (GoString × GoString)) (k v : GoString)
    (h : kvAbs l k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    simp only [kvAbs] at h
    split at h
    · rename_i hk; subst hk; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-! ## UTF-8 -/

theorem validUtf8_ascii_cons (c : w8) (rest : List w8) (hc : c.toNat < 0x80) :
    validUtf8 (c :: rest) = validUtf8 rest := by
  rcases rest with _ | ⟨c1, _ | ⟨c2, r⟩⟩ <;> simp [validUtf8, hc]

theorem validUtf8_ascii_append (a b : List w8) (ha : ∀ c ∈ a, c.toNat < 0x80) :
    validUtf8 (a ++ b) = validUtf8 b := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    have hc := ha c (by simp)
    rw [List.cons_append, validUtf8_ascii_cons _ _ hc]
    exact ih (fun d hd => ha d (by simp [hd]))

/-- A put's value as the kit's premise admits it: nonempty, not `"nil"` (stage 3: its UTF-8
validity is no longer assumed). -/
def goodVal (v : GoString) : Prop := v ≠ [] ∧ v ≠ go!"nil"

theorem goodVal_of_put (k v : GoString) (hinp : inputOk ⟨true, k, v⟩) : goodVal v :=
  hinp.2 rfl

theorem cmdPut_cmdOf (inp : KIn) (hinp : inputOk inp)
    (p : GoString × GoString) (h : cmdPut (cmdOf inp) = some p) :
    ∃ k v, inp = ⟨true, k, v⟩ ∧ p = (k, v) := by
  obtain ⟨put, k, v⟩ := inp
  have hk := hinp.1
  simp only at hk
  cases put with
  | false =>
    have hk : ((go!"1" ++ k).take 1 = go!"0") = False := by simp
    simp [cmdOf, cmdPut, hk] at h
  | true =>
    have h1 : (go!"0" ++ k ++ v).take 1 = go!"0" := rfl
    have h2 : ((go!"0" ++ k ++ v).drop 1).take keyLen = k := by simp [← hk]
    have h3 : (go!"0" ++ k ++ v).drop (1 + keyLen) = v := by
      rw [← hk, List.append_assoc, List.drop_append, List.drop_append]; simp
    simp only [cmdOf, cmdPut, h1, h2, h3, ite_true, Option.some.injEq, ↓reduceIte] at h
    exact ⟨k, v, rfl, h.symm⟩

/-! ## Where the results come from -/

/-- Every executed batch's results are its commands' on a store of a prefix of the puts. -/
def resultsFrom (B : GoString → Option Batch) (es : ExecSt) : Prop :=
  ∀ x rs, es.results x = some rs → rs = [] ∨ ∃ b, B x = some b ∧ ∃ l, l <+: es.puts ∧
    rs = (execBatch (kvAbs l.reverse) b.cmds).2

theorem execOne_resultsFrom (B : GoString → Option Batch) (es : ExecSt) (x : GoString)
    (hs : storeOk es) (h : resultsFrom B es) : resultsFrom B (execOne B es x) := by
  intro y rs hy
  unfold execOne at hy ⊢
  split at hy
  · rename_i hx; simp only [hx, ite_true]; exact h y rs hy
  · rename_i hx
    simp only [hx, ite_false] at hy ⊢
    by_cases hyx : y = x
    · subst hyx
      simp only [ite_true, Option.some.injEq] at hy
      cases hB : B y with
      | none =>
        simp only [hB, Option.map_none, Option.getD_none] at hy
        left; rw [← hy]; rfl
      | some b =>
        simp only [hB, Option.map_some, Option.getD_some] at hy
        refine Or.inr ⟨b, rfl, es.puts, List.prefix_append _ _, ?_⟩
        rw [← hy, ← hs]
    · simp only [hyx, ite_false] at hy
      rcases h y rs hy with h0 | ⟨b, hb, l, hl, hr⟩
      · exact Or.inl h0
      · exact Or.inr ⟨b, hb, l, hl.trans (List.prefix_append _ _), hr⟩

theorem execIds_resultsFrom (B : GoString → Option Batch) (es : ExecSt) (xs : List GoString)
    (hs : storeOk es) (h : resultsFrom B es) : resultsFrom B (execIds B es xs) := by
  induction xs generalizing es with
  | nil => exact h
  | cons x xs ih =>
    rw [execIds_cons]; exact ih _ (execOne_storeOk B es x hs) (execOne_resultsFrom B es x hs h)

theorem execLog_resultsFrom (B : GoString → Option Batch) (L : List (List GoString)) :
    resultsFrom B (execLog B L) := by
  unfold execLog
  have h0 : resultsFrom B ExecSt.init := by intro x rs h; simp [ExecSt.init] at h
  have hs0 : storeOk ExecSt.init := by
    show (fun _ => none) = _; simp [ExecSt.init, kvAbs_nil]
  generalize ExecSt.init = es at h0 hs0
  induction L generalizing es with
  | nil => exact h0
  | cons ids L ih => exact ih _ (execIds_resultsFrom B es ids hs0 h0) (execIds_storeOk B es ids hs0)

end Perennial.raxos.pure
