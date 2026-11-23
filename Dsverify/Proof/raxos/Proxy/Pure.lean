/-
Package `proxy`'s pure lemmas about the replicated state machine (`Pure/Smr.lean`): how the
Go code's two-phase execution of a slot (`executeClientBatches`: the batches not executed yet,
then `residentExecute` over them) is `execIds`.
-/
module

public import Dsverify.Proof.raxos.Pure.Smr

@[expose] public section

namespace Perennial.raxos.pure

/-- The ids of a slot a replica executes, given the ids `done` executed before: each id not
done yet, once (`executeClientBatches`'s first loop). -/
def freshIds (done : List GoString) : List GoString → List GoString
  | [] => []
  | x :: xs => if x ∈ done then freshIds done xs else x :: freshIds (done ++ [x]) xs

/-- A batch's commands in the registry `B`. -/
def cmdsOf (B : GoString → Option Batch) (x : GoString) : List GoString :=
  (B x).map Batch.cmds |>.getD []

/-- Batches executed in order, each unconditionally. -/
def execSeq (B : GoString → Option Batch) (es : ExecSt) : List GoString → ExecSt
  | [] => es
  | x :: xs =>
    let (st', rs) := execBatch es.store (cmdsOf B x)
    execSeq B ⟨st', es.done ++ [x], fun y => if y = x then some rs else es.results y,
      es.puts ++ (cmdsOf B x).filterMap cmdPut⟩ xs

theorem execIds_eq_execSeq (B : GoString → Option Batch) (ids : List GoString) :
    ∀ es : ExecSt, execIds B es ids = execSeq B es (freshIds es.done ids) := by
  induction ids with
  | nil => intro es; rfl
  | cons x xs ih =>
    intro es
    by_cases hx : x ∈ es.done
    · simp only [execIds, freshIds, hx, ite_true]; exact ih es
    · simp only [execIds, freshIds, hx, ite_false, execSeq, cmdsOf]
      exact ih _

/-- Command lists executed in order on a store: the store after, and each list's results
(`residentExecute` over a list of batches). -/
def runBatches (st : Store) : List (List GoString) → Store × List (List GoString)
  | [] => (st, [])
  | c :: cs =>
    let (st1, r) := execBatch st c
    let (st2, rs) := runBatches st1 cs
    (st2, r :: rs)

theorem execSeq_store (B : GoString → Option Batch) (xs : List GoString) :
    ∀ es : ExecSt, (execSeq B es xs).store = (runBatches es.store (xs.map (cmdsOf B))).1 := by
  induction xs with
  | nil => intro es; rfl
  | cons x xs ih => intro es; simp only [execSeq, List.map_cons, runBatches]; exact ih _

theorem execSeq_done (B : GoString → Option Batch) (xs : List GoString) :
    ∀ es : ExecSt, (execSeq B es xs).done = es.done ++ xs := by
  induction xs with
  | nil => intro es; simp [execSeq]
  | cons x xs ih => intro es; simp only [execSeq]; rw [ih]; simp

theorem execSeq_results_notin (B : GoString → Option Batch) (ys : List GoString) (y : GoString) :
    ∀ (es' : ExecSt), y ∉ ys → (execSeq B es' ys).results y = es'.results y := by
  induction ys with
  | nil => intro es' _; rfl
  | cons z zs ih2 =>
    intro es' hz
    simp only [execSeq]
    rw [ih2 _ (fun h => hz (List.mem_cons_of_mem _ h))]
    simp only [List.mem_cons, not_or] at hz
    simp [hz.1]

theorem execSeq_results (B : GoString → Option Batch) (xs : List GoString) (hnd : xs.Nodup) :
    ∀ (es : ExecSt) (k : Nat) (x : GoString), xs[k]? = some x →
      (execSeq B es xs).results x = (runBatches es.store (xs.map (cmdsOf B))).2[k]? := by
  induction xs with
  | nil => intro es k x h; simp at h
  | cons y ys ih =>
    intro es k x h
    have hnd' := (List.nodup_cons.1 hnd)
    simp only [execSeq, List.map_cons, runBatches]
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have := execSeq_results_notin B ys y
      rw [this _ hnd'.1]
      simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      rw [ih hnd'.2 _ k x h]
      simp

theorem freshIds_nodup (ids : List GoString) :
    ∀ done : List GoString, (freshIds done ids).Nodup ∧
      ∀ x ∈ freshIds done ids, x ∉ done ∧ x ∈ ids := by
  induction ids with
  | nil => intro done; simp [freshIds]
  | cons y ys ih =>
    intro done
    by_cases hy : y ∈ done
    · simp only [freshIds, hy, ite_true]
      obtain ⟨h1, h2⟩ := ih done
      exact ⟨h1, fun x hx => ⟨(h2 x hx).1, List.mem_cons_of_mem _ (h2 x hx).2⟩⟩
    · simp only [freshIds, hy, ite_false]
      obtain ⟨h1, h2⟩ := ih (done ++ [y])
      refine ⟨List.nodup_cons.2 ⟨fun hm => (h2 y hm).1 (by simp), h1⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hy, by simp⟩
      · have := h2 x hx
        exact ⟨fun h => this.1 (List.mem_append_left _ h), List.mem_cons_of_mem _ this.2⟩

/-- `execLog` reads the registry only at the log's ids. -/
theorem px_execIds_congr (B B' : GoString → Option Batch) (ids : List GoString)
    (h : ∀ x ∈ ids, B x = B' x) : ∀ es, execIds B es ids = execIds B' es ids := by
  induction ids with
  | nil => intro es; rfl
  | cons x xs ih =>
    intro es
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [execIds, hx]
    split <;> exact ih' _

theorem px_execLog_congr (B B' : GoString → Option Batch) (L : List (List GoString))
    (h : ∀ x ∈ L.flatten, B x = B' x) : execLog B L = execLog B' L := by
  unfold execLog
  suffices ∀ es, L.foldl (execIds B) es = L.foldl (execIds B') es from this _
  induction L with
  | nil => intro es; rfl
  | cons ids L ih =>
    intro es
    simp only [List.foldl_cons]
    rw [px_execIds_congr B B' ids (fun x hx => h x (by simp [hx])) es]
    exact ih (fun x hx => h x (by simp [hx])) _

theorem px_execLog_snoc (B : GoString → Option Batch) (L : List (List GoString)) (ids : List GoString) :
    execLog B (L ++ [ids]) = execIds B (execLog B L) ids := by
  simp [execLog, List.foldl_append]

theorem execBatch_snoc (st : Store) (l : List GoString) (c : GoString) :
    execBatch st (l ++ [c]) =
      ((execCmd (execBatch st l).1 c).1, (execBatch st l).2 ++ [(execCmd (execBatch st l).1 c).2]) := by
  induction l generalizing st with
  | nil => simp [execBatch]
  | cons d ds ih => simp only [List.cons_append, execBatch]; rw [ih]

theorem runBatches_snoc (st : Store) (l : List (List GoString)) (c : List GoString) :
    runBatches st (l ++ [c]) =
      ((execBatch (runBatches st l).1 c).1, (runBatches st l).2 ++ [(execBatch (runBatches st l).1 c).2]) := by
  induction l generalizing st with
  | nil => simp [runBatches]
  | cons d ds ih => simp only [List.cons_append, runBatches]; rw [ih]

theorem runBatches_length (st : Store) (l : List (List GoString)) :
    (runBatches st l).2.length = l.length := by
  induction l generalizing st with
  | nil => rfl
  | cons d ds ih => simp [runBatches, ih]

theorem execBatch_length (st : Store) (l : List GoString) :
    (execBatch st l).2.length = l.length := by
  induction l generalizing st with
  | nil => rfl
  | cons d ds ih => simp [execBatch, ih]

theorem freshIds_snoc (l : List GoString) (x : GoString) :
    ∀ done, freshIds done (l ++ [x]) =
      freshIds done l ++ (if x ∈ done ++ freshIds done l then [] else [x]) := by
  induction l with
  | nil => intro done; simp [freshIds]
  | cons y ys ih =>
    intro done
    by_cases hy : y ∈ done
    · simp only [List.cons_append, freshIds, hy, ite_true]; exact ih done
    · simp only [List.cons_append, freshIds, hy, ite_false]
      rw [ih (done ++ [y])]
      simp [List.append_assoc]

end Perennial.raxos.pure
