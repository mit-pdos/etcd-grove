/-
**The snapshot send loop's termination model** (pr etcd#22125, pure). `maintenance.go`'s
`maintenanceServer.Snapshot` starts a goroutine that writes the backend snapshot into an
`io.Pipe` (`snap.WriteTo(pw)`) and closes the pipe's writer, and reads the pipe in a loop
`for total-sent > 0 { n, err := io.ReadFull(pr, buf); if err is not EOF-like { return }; sent += n;
srv.Send(...) }`, where `total = snap.Size()` and "EOF-like" is `errors.Is(err, io.EOF) ||
errors.Is(err, io.ErrUnexpectedEOF)`.

The loop's progress is a liveness property, which a weakest-precondition spec (partial
correctness) cannot state: an infinite loop meets every such spec, so a Hoare triple of
`Snapshot` holds of the code before and after the PR alike. This file states it as a pure model
instead and proves when the loop terminates.

What the reader sees is determined by the writer's final state (the model is exact for it):
`io.ReadFull` of `B` bytes returns `B` bytes once that many are written, and otherwise blocks
until the writer closes the pipe, then returns what is left and the close's error (`io.EOF`
after `Close()` or `CloseWithError(nil)`, or `io.ErrUnexpectedEOF` if some bytes were read in that
call; the error `e` itself after `CloseWithError(e)`, `e ≠ nil`). So a run is determined by `B`
(`snapshotSendBufferSize`), `total`, the bytes written, and whether the close's error is EOF-like.
`srv.Send` is assumed to succeed (its failure returns at once, which only helps termination).

- `old_hangs`: before the PR (`snap.WriteTo(pw); ...; pw.Close()`), a `WriteTo` that writes fewer
  than `total` bytes makes the loop run forever (whatever error `WriteTo` returned).
- `new_terminates`: with the PR (`pw.CloseWithError(err)` on a `WriteTo` error, `pw.Close()`
  otherwise), the loop terminates within `total + 1` iterations unless `WriteTo` returned an
  EOF-like error; it reports success exactly when `WriteTo` wrote all `total` bytes.
- `new_hangs_on_eof`: with the PR, a `WriteTo` that stops short and returns an EOF-like error still
  makes the loop run forever. bbolt's `Tx.WriteTo` does that when the database file is shorter
  than `tx.Size()` (its `io.CopyN` returns `io.EOF`): test `TestBoltWriteToShortFileReturnsEOF`,
  `notes/pr-verify/etcd-22125/maintenance_snapshot_test.go`.
- `guarded_terminates`: a loop that also returns an error when a read returns no bytes
  (`n == 0`) terminates for every writer, with either close, and reports success exactly when all
  `total` bytes were written.

`WriteTo`'s contract (`WriteToContract`) is `io.WriterTo`'s as bbolt meets it through `io.CopyN`:
it writes at most `total` bytes, and returns `nil` exactly when it wrote all of them.
Lean-first (no Rocq counterpart).
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace v3rpc
namespace snapshotLoop

/-- How the pipe's reader sees the writer's close: an EOF-like error (`io.EOF` after `Close()`,
or an error `errors.Is` to `io.EOF`/`io.ErrUnexpectedEOF`), which the loop ignores, or another
error, which it returns. -/
inductive CloseErr where
  | eofLike
  | other
  deriving DecidableEq

/-- The writer's final state: the bytes it wrote before closing, and the close's error. -/
structure Pipe where
  written : Nat
  close : CloseErr

/-- `io.ReadFull(pr, buf)` with `len(buf) = B`, after `consumed` bytes were read: the bytes read,
and whether the error is one the loop ignores (`nil`, or EOF-like). With `n < B` the error is
the close's (`io.ErrUnexpectedEOF` for an `io.EOF` close after some bytes: EOF-like too). -/
def readFull (B : Nat) (p : Pipe) (consumed : Nat) : Nat × Bool :=
  if B ≤ p.written - consumed then (B, true)
  else (p.written - consumed, decide (p.close = .eofLike))

/-- One iteration of the loop at `sent` bytes sent: `.inl true` it leaves the loop (sending the
checksum: success), `.inl false` it returns the read's error, `.inr s` it continues at `s`. With
`guard` (the suggested fix), a read of no bytes also returns an error. -/
def step (guard : Bool) (B total : Nat) (p : Pipe) (sent : Nat) : Bool ⊕ Nat :=
  if total ≤ sent then .inl true
  else
    let r := readFull B p sent
    if !r.2 then .inl false
    else if guard && r.1 = 0 then .inl false
    else .inr (sent + r.1)

/-- The loop run for at most `fuel` iterations from `sent`: `some ok` if it left the loop (with
success `ok`), `none` if it was still looping. -/
def run (guard : Bool) (B total : Nat) (p : Pipe) : Nat → Nat → Option Bool
  | 0, _ => none
  | fuel + 1, sent =>
    match step guard B total p sent with
    | .inl ok => some ok
    | .inr s => run guard B total p fuel s

/-- The loop terminates: some number of iterations leaves it. -/
def Terminates (guard : Bool) (B total : Nat) (p : Pipe) : Prop :=
  ∃ fuel ok, run guard B total p fuel 0 = some ok

/-- What `WriteTo` did: the bytes it wrote, and its error (`none`: `nil`). -/
structure WriteResult where
  written : Nat
  err : Option CloseErr

/-- `WriteTo`'s contract (bbolt's `Tx.WriteTo`, through `io.CopyN`): at most `total` bytes, and
`nil` exactly when all of them. -/
def WriteToContract (total : Nat) (r : WriteResult) : Prop :=
  r.written ≤ total ∧ (r.err = none ↔ r.written = total)

/-- Before the PR: `snap.WriteTo(pw)` (its error dropped), `snap.Close()`, `pw.Close()`. -/
def pipeOld (r : WriteResult) : Pipe := ⟨r.written, .eofLike⟩

/-- With the PR: `pw.CloseWithError(err)` if `WriteTo` failed, else `pw.Close()`. -/
def pipeNew (r : WriteResult) : Pipe :=
  ⟨r.written, match r.err with | none => .eofLike | some c => c⟩

/-! ### One iteration -/

theorem run_succ (guard : Bool) (B total : Nat) (p : Pipe) (fuel sent : Nat) :
    run guard B total p (fuel + 1) sent =
      match step guard B total p sent with
      | .inl ok => some ok
      | .inr s => run guard B total p fuel s := rfl

theorem step_done {guard B total p sent} (h : total ≤ sent) :
    step guard B total p sent = .inl true := by
  simp [step, h]

theorem step_full {guard B total p sent} (ht : ¬ total ≤ sent) (hB : 0 < B)
    (hBa : B ≤ p.written - sent) : step guard B total p sent = .inr (sent + B) := by
  have : B ≠ 0 := by omega
  simp [step, readFull, ht, hBa, this]

theorem step_short_other {guard B total p sent} (ht : ¬ total ≤ sent)
    (hBa : ¬ B ≤ p.written - sent) (hc : p.close = .other) :
    step guard B total p sent = .inl false := by
  simp [step, readFull, ht, hBa, hc]

theorem step_short_eof {guard B total p sent} (ht : ¬ total ≤ sent)
    (hBa : ¬ B ≤ p.written - sent) (hc : p.close = .eofLike) (h0 : p.written - sent ≠ 0) :
    step guard B total p sent = .inr (sent + (p.written - sent)) := by
  simp [step, readFull, ht, hBa, hc, h0]

theorem step_short_eof_zero {guard B total p sent} (ht : ¬ total ≤ sent)
    (hBa : ¬ B ≤ p.written - sent) (hc : p.close = .eofLike) (h0 : p.written - sent = 0) :
    step guard B total p sent = if guard then .inl false else .inr sent := by
  have hB : B ≠ 0 := by omega
  cases guard <;> simp [step, readFull, ht, hc, h0, hB]

theorem step_full_noguard {B total p sent} (ht : ¬ total ≤ sent)
    (hBa : B ≤ p.written - sent) : step false B total p sent = .inr (sent + B) := by
  simp [step, readFull, ht, hBa]

/-! ### The loop never stops when the writer stops short with an EOF-like close -/

theorem run_none_of_short (B total : Nat) (p : Pipe) (hshort : p.written < total)
    (hclose : p.close = .eofLike) :
    ∀ fuel sent, sent ≤ p.written → run false B total p fuel sent = none := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro sent hs
    have ht : ¬ total ≤ sent := by omega
    rw [run_succ]
    by_cases hBa : B ≤ p.written - sent
    · rw [step_full_noguard ht hBa]; exact ih _ (by omega)
    · by_cases h0 : p.written - sent = 0
      · rw [step_short_eof_zero ht hBa hclose h0]; exact ih _ hs
      · rw [step_short_eof ht hBa hclose h0]; exact ih _ (by omega)

theorem not_terminates_of_short (B total : Nat) (p : Pipe) (hshort : p.written < total)
    (hclose : p.close = .eofLike) : ¬ Terminates false B total p := by
  rintro ⟨fuel, ok, h⟩
  rw [run_none_of_short B total p hshort hclose fuel 0 (Nat.zero_le _)] at h
  cases h

/-- **Before the PR**, a `WriteTo` that writes fewer than `total` bytes (whatever its error)
makes the loop run forever. -/
theorem old_hangs (B total : Nat) (r : WriteResult) (hshort : r.written < total) :
    ¬ Terminates false B total (pipeOld r) :=
  not_terminates_of_short B total (pipeOld r) hshort rfl

/-- **With the PR**, a `WriteTo` that stops short with an EOF-like error (bbolt's on a short
database file) still makes the loop run forever. -/
theorem new_hangs_on_eof (B total : Nat) (r : WriteResult) (hshort : r.written < total)
    (herr : r.err = some .eofLike) : ¬ Terminates false B total (pipeNew r) :=
  not_terminates_of_short B total (pipeNew r) hshort (by simp [pipeNew, herr])

/-! ### When the loop terminates -/

/-- The loop terminates within `total - sent + 1` iterations from `sent ≤ written` if every
iteration that continues makes progress: the writer wrote everything, or its close is not
EOF-like, or the guard is on. On termination, success means all bytes were written; and when
all bytes were written and the close is EOF-like, it is success. -/
theorem run_some (guard : Bool) (B total : Nat) (p : Pipe) (hB : 0 < B)
    (hle : p.written ≤ total)
    (hprog : total ≤ p.written ∨ p.close = .other ∨ guard = true) :
    ∀ k sent, sent ≤ p.written → total - sent ≤ k →
      ∃ ok, run guard B total p (k + 1) sent = some ok ∧ (ok = true → total ≤ p.written) ∧
        (total ≤ p.written → p.close = .eofLike → ok = true) := by
  intro k
  induction k with
  | zero =>
    intro sent hs hk
    have ht : total ≤ sent := by omega
    exact ⟨true, by rw [run_succ, step_done ht], fun _ => by omega, fun _ _ => rfl⟩
  | succ k ih =>
    intro sent hs hk
    by_cases ht : total ≤ sent
    · exact ⟨true, by rw [run_succ, step_done ht], fun _ => by omega, fun _ _ => rfl⟩
    · by_cases hBa : B ≤ p.written - sent
      · obtain ⟨ok, h, hok⟩ := ih (sent + B) (by omega) (by omega)
        exact ⟨ok, by rw [run_succ, step_full ht hB hBa]; exact h, hok⟩
      · have hcases : p.close = .other ∨ p.close = .eofLike := by
          cases p.close <;> simp
        rcases hcases with hc | hc
        · refine ⟨false, ?_, (fun h => by cases h), (fun _ h => by rw [hc] at h; cases h)⟩
          rw [run_succ, step_short_other ht hBa hc]
        · by_cases h0 : p.written - sent = 0
          · have hg : guard = true := by
              rcases hprog with h | h | h
              · omega
              · rw [hc] at h; cases h
              · exact h
            refine ⟨false, ?_, (fun h => by cases h), (fun h _ => by omega)⟩
            rw [run_succ, step_short_eof_zero ht hBa hc h0, hg]; rfl
          · obtain ⟨ok, h, hok⟩ := ih (sent + (p.written - sent)) (by omega) (by omega)
            exact ⟨ok, by rw [run_succ, step_short_eof ht hBa hc h0]; exact h, hok⟩

/-- **With the PR**, the loop terminates (within `total + 1` iterations) unless `WriteTo` returned
an EOF-like error, and it reports success exactly when `WriteTo` wrote all `total` bytes. -/
theorem new_terminates (B total : Nat) (hB : 0 < B) (r : WriteResult)
    (hc : WriteToContract total r) (herr : r.err ≠ some .eofLike) :
    ∃ ok, run false B total (pipeNew r) (total + 1) 0 = some ok ∧
      (ok = true ↔ r.written = total) := by
  obtain ⟨hle, hnil⟩ := hc
  have hprog : total ≤ (pipeNew r).written ∨ (pipeNew r).close = .other ∨ false = true := by
    cases he : r.err with
    | none => exact Or.inl (by have := hnil.mp he; simp [pipeNew]; omega)
    | some c =>
      cases c with
      | eofLike => exact absurd he herr
      | other => exact Or.inr (Or.inl (by simp [pipeNew, he]))
  obtain ⟨ok, h, hok, hsucc⟩ :=
    run_some false B total (pipeNew r) hB hle hprog total 0 (Nat.zero_le _) (by omega)
  refine ⟨ok, h, fun hk => by have := hok hk; simp [pipeNew] at this; omega, fun hw => ?_⟩
  exact hsucc (by simp [pipeNew]; omega) (by simp [pipeNew, hnil.mpr hw])

/-- **The suggested fix** (also return an error on a read of no bytes) terminates for every writer
that writes at most `total` bytes, with either close, and success means all bytes were written. -/
theorem guarded_terminates (B total : Nat) (hB : 0 < B) (p : Pipe) (hle : p.written ≤ total) :
    ∃ ok, run true B total p (total + 1) 0 = some ok ∧ (ok = true → total ≤ p.written) := by
  obtain ⟨ok, h, hok, _⟩ :=
    run_some true B total p hB hle (Or.inr (Or.inr rfl)) total 0 (Nat.zero_le _) (by omega)
  exact ⟨ok, h, hok⟩

end snapshotLoop
end v3rpc
end EtcdGrove
end Perennial
