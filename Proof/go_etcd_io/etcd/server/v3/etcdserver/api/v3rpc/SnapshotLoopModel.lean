/-
**The snapshot stream's send loop, modelled** (pr-verify etcd#22066, pure). `maintenance.go`'s
`maintenanceServer.Snapshot` reads the backend snapshot through an `io.Pipe` in buffers of
`snapshotSendBufferSize` (32 KiB) and sends each buffer as a `SnapshotResponse`, then sends the
32-byte SHA-256 digest with `RemainingBytes = 0`. The function itself is not translated with its
body: Goose translates it, but the translation needs `crypto/sha256` and `hash`, which Perennial
does not model (`notes/pr-verify/etcd-22066.md`, "Translation"). This file models the loop
instead, as a function of four numbers:

* `avail`: the bytes the pipe yields before `EOF` (`snap.Size()` when `snap.WriteTo` succeeds;
  fewer when it fails part way, whose error the writer goroutine drops before `pw.Close()`);
* `bound`: the loop runs while `bound - sent > 0` (`total` before the PR, `total + h.Size()`
  with it);
* `rep`: the data responses carry `RemainingBytes = rep - sent` (`sent` counted after the
  buffer is read): `total` before, `total + 32` with the PR.

`io.ReadFull(pr, buf)` with `len(buf) = 32768` returns `n = min 32768 (avail - sent)` (`nil`,
`ErrUnexpectedEOF` or `EOF`, the last two tolerated by the loop), so `sent` after `k` iterations is
`min (32768 k) avail` (`sentAfter_eq`). Results:

* `exits_iff`: the loop ends iff `bound ≤ avail`;
* `pr_spins`: with the PR (`bound = avail + 32`) it never ends while `srv.Send` succeeds (the
  model leaves out `Send`'s failure, the only other exit: a client that cancels), and from iteration
  `⌈total/32768⌉` on, every response it sends is empty with `RemainingBytes = 32`
  (`pr_spin_msg`): the checksum is never sent;
* `base_spins_on_writeTo_error`: before the PR too, when the snapshot yields fewer than
  `snap.Size()` bytes;
* `fixed_remainingOk`: the loop `for total-sent > 0` with `RemainingBytes = total + 32 - sent`
  ends after `⌈total/32768⌉` iterations and every response of the stream, the checksum
  included, carries `RemainingBytes` = the blob bytes sent after it (`rpc.proto`'s
  `remaining_bytes`), which `base_not_remainingOk` shows the code before the PR does not.

int64 overflow of `total + 32` is not modelled (`total` is a database file's size).
Lean-first (no Rocq counterpart).
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace v3rpc
namespace SnapshotLoop

/-- The loop's parameters (see the file header). -/
structure Cfg where
  avail : Nat
  bound : Nat
  rep : Nat

/-- `sent` after `k` iterations. -/
def sentAfter (c : Cfg) : Nat → Nat
  | 0 => 0
  | k + 1 => sentAfter c k + min 32768 (c.avail - sentAfter c k)

theorem sentAfter_eq (c : Cfg) (k : Nat) : sentAfter c k = min (32768 * k) c.avail := by
  induction k with
  | zero => simp [sentAfter]
  | succ k ih => simp only [sentAfter, ih]; omega

/-- Iteration `k` runs (and sends a response) iff the loop condition holds before it. -/
def runs (c : Cfg) (k : Nat) : Prop := sentAfter c k < c.bound

/-- The response iteration `k` sends: its blob's length and its `RemainingBytes`. -/
def blob (c : Cfg) (k : Nat) : Nat := sentAfter c (k + 1) - sentAfter c k
def remaining (c : Cfg) (k : Nat) : Nat := c.rep - sentAfter c (k + 1)

/-- The loop ends iff `bound ≤ avail`. -/
theorem exits_iff (c : Cfg) : (∃ k, ¬ runs c k) ↔ c.bound ≤ c.avail := by
  simp only [runs, sentAfter_eq]
  constructor
  · rintro ⟨k, hk⟩; omega
  · intro h; exact ⟨c.avail, by omega⟩

/-- The configurations: the database's size `D`. -/
def base (D : Nat) : Cfg := { avail := D, bound := D, rep := D }
def pr (D : Nat) : Cfg := { avail := D, bound := D + 32, rep := D + 32 }
def fixed (D : Nat) : Cfg := { avail := D, bound := D, rep := D + 32 }
/-- Before the PR, with `snap.WriteTo` failing after `w < D` bytes. -/
def baseErr (D w : Nat) : Cfg := { avail := w, bound := D, rep := D }

/-- **With the PR the loop never ends** (as long as `srv.Send` succeeds), whatever the database's
size. -/
theorem pr_spins (D k : Nat) : runs (pr D) k := by
  simp only [runs, pr, sentAfter_eq]; omega

/-- From iteration `⌈D/32768⌉` on, the PR's loop sends empty responses with
`RemainingBytes = 32`, forever. -/
theorem pr_spin_msg (D k : Nat) (hk : (D + 32767) / 32768 ≤ k) :
    runs (pr D) k ∧ blob (pr D) k = 0 ∧ remaining (pr D) k = 32 := by
  refine ⟨pr_spins D k, ?_, ?_⟩ <;> simp only [blob, remaining, pr, sentAfter_eq] <;> omega

/-- Before the PR, a snapshot that yields fewer bytes than its size has the same effect. -/
theorem base_spins_on_writeTo_error (D w k : Nat) (hw : w < D) : runs (baseErr D w) k := by
  simp only [runs, baseErr, sentAfter_eq]; omega

/-- Before the PR, and with the fix, the loop ends after exactly `⌈D/32768⌉` iterations. -/
theorem base_exits (D k : Nat) : runs (base D) k ↔ k < (D + 32767) / 32768 := by
  simp only [runs, base, sentAfter_eq]; omega

theorem fixed_exits (D k : Nat) : runs (fixed D) k ↔ k < (D + 32767) / 32768 := by
  simp only [runs, fixed, sentAfter_eq]; omega

/-! ## The stream and `remaining_bytes` -/

/-- `Σ_{j < n} f (a + j)`. -/
def sumFrom (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f a + sumFrom f (a + 1) n

/-- The whole stream of a loop that ends after `K` iterations: response `i < K` is data
response `i`, response `K` the 32-byte checksum with `RemainingBytes = 0`. -/
def streamBlob (c : Cfg) (K i : Nat) : Nat := if i < K then blob c i else 32
def streamRem (c : Cfg) (K i : Nat) : Nat := if i < K then remaining c i else 0

/-- `rpc.proto`: "remaining_bytes is the number of blob bytes to be sent after this message":
every response `i ≤ K` carries the sum of the blobs of the responses `i+1 … K`. -/
def RemainingOk (c : Cfg) (K : Nat) : Prop :=
  ∀ i ≤ K, streamRem c K i = sumFrom (streamBlob c K) (i + 1) (K - i)

theorem sentAfter_mono (c : Cfg) {a b : Nat} (h : a ≤ b) : sentAfter c a ≤ sentAfter c b := by
  simp only [sentAfter_eq]; omega

/-- The data blobs telescope. -/
theorem sum_blob (c : Cfg) (a n : Nat) :
    sumFrom (blob c) a n = sentAfter c (a + n) - sentAfter c a := by
  induction n generalizing a with
  | zero => simp [sumFrom]
  | succ n ih =>
    simp only [sumFrom, ih, blob]
    have h1 := sentAfter_mono c (show a ≤ a + 1 by omega)
    have h2 := sentAfter_mono c (show a + 1 ≤ a + (n + 1) by omega)
    rw [show a + 1 + n = a + (n + 1) by omega]
    omega

/-- The checksum's 32 bytes come last. -/
theorem sum_stream (c : Cfg) (K a n : Nat) (h : a + n = K + 1) :
    sumFrom (streamBlob c K) a n = sumFrom (blob c) a (n - 1) + (if 0 < n then 32 else 0) := by
  induction n generalizing a with
  | zero => simp [sumFrom]
  | succ n ih =>
    simp only [sumFrom]
    cases n with
    | zero =>
      have : a = K := by omega
      subst this; simp [streamBlob, sumFrom]
    | succ m =>
      rw [ih (a + 1) (by omega)]
      have : a < K := by omega
      simp only [streamBlob, this, ite_true, show m + 1 + 1 - 1 = m + 1 by omega,
        show m + 1 - 1 = m by omega, sumFrom, Nat.zero_lt_succ]
      omega

/-- **The fix meets `remaining_bytes`'s documentation**: the loop `for total-sent > 0` with
`RemainingBytes = total + 32 - sent` (then the checksum). -/
theorem fixed_remainingOk (D : Nat) : RemainingOk (fixed D) ((D + 32767) / 32768) := by
  intro i hi
  rw [sum_stream _ _ _ _ (by omega), sum_blob]
  simp only [streamRem, remaining, fixed, sentAfter_eq]
  split <;> rename_i h
  · have hc : 0 < (D + 32767) / 32768 - i := by omega
    simp only [hc, ite_true]
    rw [show i + 1 + ((D + 32767) / 32768 - i - 1) = (D + 32767) / 32768 by omega]
    omega
  · have : i = (D + 32767) / 32768 := by omega
    subst this; simp

/-- **Before the PR it does not**: every data response undercounts by the checksum's 32 bytes
(the first, for a database of at least one byte). -/
theorem base_not_remainingOk (D : Nat) (hD : 0 < D) :
    ¬ RemainingOk (base D) ((D + 32767) / 32768) := by
  intro h
  have h0 := h 0 (Nat.zero_le _)
  rw [sum_stream _ _ _ _ (by omega), sum_blob] at h0
  simp only [streamRem, remaining, base, sentAfter_eq] at h0
  have hc : 0 < (D + 32767) / 32768 := by omega
  simp only [hc, Nat.sub_zero, ite_true] at h0
  rw [show 0 + 1 + ((D + 32767) / 32768 - 1) = (D + 32767) / 32768 by omega] at h0
  omega

end SnapshotLoop

#print axioms SnapshotLoop.pr_spins
#print axioms SnapshotLoop.pr_spin_msg
#print axioms SnapshotLoop.base_spins_on_writeTo_error
#print axioms SnapshotLoop.exits_iff
#print axioms SnapshotLoop.fixed_exits
#print axioms SnapshotLoop.fixed_remainingOk
#print axioms SnapshotLoop.base_not_remainingOk

end v3rpc
end EtcdGrove
end Perennial
