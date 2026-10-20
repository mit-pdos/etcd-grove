/-
Lean-first (no Rocq counterpart).

# linkv: the KV model of the robustness tester's workload (linkv-txn stage C, 2026-10-20)

The sequential model of `notes/linkv-txn-plan.md`, stage C: etcd's KV API as its robustness
tester models it (`tests/robustness/model/deterministic.go`, `EtcdState`): a store of every key's
value, mod revision and version (`VR`; no create revision, no lease: robustness keeps neither),
and the current revision (`MSt`, initially `1`, an empty store). The operations (`MIn`):

- `get k` and `list` (every key of the workload's `ks`, in `ks`'s order: the prefix range the
  instance lists, over a workload writing only `ks`), answered at the current revision;
- `put k v` (the next revision; the key's version one more, `1` for a new key), `del k`
  (the next revision and a count of `1` if the key is there, else nothing and `0`);
- `txn cs t e`: if every comparison holds (a value's equality, failing on a missing key; a
  version's or a mod revision's, `0` for a missing key: etcd's `applyCompare`, `cmpHolds`), the
  operations `t`, else `e`, run in order on the store the earlier ones left, every write at the
  next revision (`MOp.run`); the transaction takes the next revision if one of them changed the
  store (a put; a delete of a present key), else keeps the current one.

Every answer carries its header revision (`MOut`: robustness's `EtcdResponse.Revision`). The
model is a `PendSpec` (`PendModel.lean`): a failed write (a put, a delete, a transaction with a
write) may take effect later, at most once, or never; a failed read constrains nothing. Its
relation to etcd's state and the server's step is `TxnModelKV.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.PendModel
public import Perennial.Std.Word

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace linkv

open github_com.anishathalye.porcupine.Theory

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- A key's value, with its mod revision and version (64-bit words, as etcd's and robustness's
`int64`s: the abstraction of etcd's key-values is then exact, `TxnModelKV.lean`). -/
structure VR (V : Type) where
  val : V
  mod : w64
  ver : w64
  deriving DecidableEq

/-- A store: every key's value, if any. -/
abbrev MStore (K V : Type) := K → Option (VR V)

/-- The model's state: the store and the current revision. -/
structure MSt (K V : Type) where
  kv : MStore K V
  rev : Nat

/-- The store after a put of `k ↦ v` at revision `r`: the key's version one more. -/
def MStore.put (m : MStore K V) (r : Nat) (k : K) (v : V) : MStore K V :=
  fun k' => if k' = k then some ⟨v, W64 (r : Int), ((m k).map VR.ver).getD (W64 0) + W64 1⟩
    else m k'

/-- The store after a delete of `k`. -/
def MStore.del (m : MStore K V) (k : K) : MStore K V :=
  fun k' => if k' = k then none else m k'

/-- A comparison of a transaction: a key's value, version or mod revision, for equality. -/
inductive MCmp (K V : Type) where
  | val (k : K) (v : V)
  | ver (k : K) (n : w64)
  | mod (k : K) (n : w64)
  deriving DecidableEq

/-- A comparison's verdict on the store (etcd's `applyCompare` of a single key: a value's
comparison fails on a missing key, a version's or a mod revision's compares `0`). -/
def MCmp.holds (m : MStore K V) : MCmp K V → Bool
  | .val k v => match m k with
    | some x => decide (x.val = v)
    | none => false
  | .ver k n => decide (((m k).map VR.ver).getD (W64 0) = n)
  | .mod k n => decide (((m k).map VR.mod).getD (W64 0) = n)

/-- An operation of a transaction. -/
inductive MOp (K V : Type) where
  | get (k : K)
  | put (k : K) (v : V)
  | del (k : K)
  deriving DecidableEq

/-- An operation's result in a transaction: a get's key-value, a put, a delete's count. -/
inductive MRes (V : Type) where
  | get (r : Option (VR V))
  | put
  | del (n : Nat)
  deriving DecidableEq

/-- An operation of a transaction at revision `r` on the store `m`: the store after it, its
result, and whether it changed the store. -/
def MOp.run (r : Nat) (m : MStore K V) : MOp K V → MStore K V × MRes V × Bool
  | .get k => (m, .get (m k), false)
  | .put k v => (m.put r k v, .put, true)
  | .del k => match m k with
    | some _ => (m.del k, .del 1, true)
    | none => (m, .del 0, false)

/-- A transaction's operations in order, each on the store the earlier ones left. -/
def runOps (r : Nat) : MStore K V → List (MOp K V) → MStore K V × List (MRes V) × Bool
  | m, [] => (m, [], false)
  | m, op :: ops =>
    let p := op.run r m
    let q := runOps r p.1 ops
    (q.1, p.2.1 :: q.2.1, p.2.2 || q.2.2)

/-- An operation (porcupine's input). -/
inductive MIn (K V : Type) where
  | get (k : K)
  | list
  | put (k : K) (v : V)
  | del (k : K)
  | txn (cs : List (MCmp K V)) (t e : List (MOp K V))
  deriving DecidableEq

/-- An operation's answer, with its header revision. -/
inductive MOut (K V : Type) where
  | get (rev : Nat) (r : Option (VR V))
  | list (rev : Nat) (rs : List (K × VR V))
  | put (rev : Nat)
  | del (rev : Nat) (n : Nat)
  | txn (rev : Nat) (ok : Bool) (rs : List (MRes V))
  deriving DecidableEq

/-- A transaction operation that writes. -/
def MOp.isWrite : MOp K V → Bool
  | .get _ => false
  | _ => true

/-- An operation that may write (a failed one may take effect later). -/
def MIn.isWrite : MIn K V → Bool
  | .get _ => false
  | .list => false
  | .put _ _ => true
  | .del _ => true
  | .txn _ t e => t.any MOp.isWrite || e.any MOp.isWrite

/-- **One operation's effect and answer** (see the file header); `ks` the keys `list` lists. -/
def mStep (ks : List K) : MIn K V → MSt K V → MSt K V × MOut K V
  | .get k, s => (s, .get s.rev (s.kv k))
  | .list, s => (s, .list s.rev (ks.filterMap fun k => (s.kv k).map fun x => (k, x)))
  | .put k v, s => (⟨s.kv.put (s.rev + 1) k v, s.rev + 1⟩, .put (s.rev + 1))
  | .del k, s => match s.kv k with
    | some _ => (⟨s.kv.del k, s.rev + 1⟩, .del (s.rev + 1) 1)
    | none => (s, .del s.rev 0)
  | .txn cs t e, s =>
    let ok := cs.all (MCmp.holds s.kv)
    let q := runOps (s.rev + 1) s.kv (if ok then t else e)
    let rev' := if q.2.2 then s.rev + 1 else s.rev
    (⟨q.1, rev'⟩, .txn rev' ok q.2.1)

/-- The initial state: revision `1`, nothing stored (etcd's, robustness's `freshEtcdState`). -/
def mInit : MSt K V := ⟨fun _ => none, 1⟩

/-- **The model**, as a store with failed writes. -/
def txnSpec (ks : List K) : PendSpec (MSt K V) (MIn K V) (MOut K V) where
  init := mInit
  step := mStep ks
  isWrite := MIn.isWrite

/-! ## Facts of the step -/

/-- A read changes nothing. -/
theorem mStep_read (ks : List K) (i : MIn K V) (s : MSt K V) (h : i.isWrite = false) :
    (mStep ks i s).1 = s := by
  cases i with
  | get k => rfl
  | list => rfl
  | put k v => simp [MIn.isWrite] at h
  | del k => simp [MIn.isWrite] at h
  | txn cs t e =>
    simp only [MIn.isWrite, Bool.or_eq_false_iff, List.any_eq_false] at h
    obtain ⟨ht, he⟩ := h
    have hr : ∀ (r : Nat) (m : MStore K V) (ops : List (MOp K V)),
        (∀ op ∈ ops, ¬ op.isWrite = true) → (runOps r m ops).1 = m ∧ (runOps r m ops).2.2 = false := by
      intro r m ops
      induction ops generalizing m with
      | nil => intro _; simp [runOps]
      | cons op ops ih =>
        intro hw
        have h1 := hw op List.mem_cons_self
        have h2 := ih m (fun o ho => hw o (List.mem_cons_of_mem _ ho))
        cases op with
        | get k => simpa [runOps, MOp.run] using h2
        | put k v => simp [MOp.isWrite] at h1
        | del k => simp [MOp.isWrite] at h1
    simp only [mStep]
    by_cases hc : (cs.all (MCmp.holds s.kv)) = true
    · obtain ⟨h1, h2⟩ := hr (s.rev + 1) s.kv t ht
      simp only [hc, ite_true, h1, h2, Bool.false_eq_true, ite_false]
    · obtain ⟨h1, h2⟩ := hr (s.rev + 1) s.kv e he
      simp only [hc, Bool.false_eq_true, ite_false, h1, h2]

/-- An answer's revision is the state's after the step. -/
def MOut.rev : MOut K V → Nat
  | .get r _ => r
  | .list r _ => r
  | .put r => r
  | .del r _ => r
  | .txn r _ _ => r

theorem mStep_rev (ks : List K) (i : MIn K V) (s : MSt K V) :
    (mStep ks i s).2.rev = (mStep ks i s).1.rev := by
  cases i with
  | del k => simp only [mStep]; cases s.kv k <;> rfl
  | _ => rfl

/-- The revision never decreases, and moves by at most one. -/
theorem mStep_rev_le (ks : List K) (i : MIn K V) (s : MSt K V) :
    s.rev ≤ (mStep ks i s).1.rev ∧ (mStep ks i s).1.rev ≤ s.rev + 1 := by
  cases i with
  | get k => exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | list => exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | put k v => exact ⟨Nat.le_succ _, Nat.le_refl _⟩
  | del k => simp only [mStep]; cases s.kv k <;> simp
  | txn cs t e => dsimp only [mStep]; split <;> split <;> omega

/-! ## Sanity: histories the robustness tester checks -/

section sanity

/-- A put, then a get reading it at the put's revision with version `1`. -/
example (k : K) (v : V) :
    (mStep [] (.get k) (mStep [] (.put k v) mInit).1).2 =
      .get 2 (some ⟨v, W64 2, W64 1⟩) := by
  simp [mStep, mInit, MStore.put]

/-- A compare-and-set on the value: the swap happens when the value matches, at the next
revision, and not otherwise (the revision unchanged). -/
example (k : K) (v w : V) (hvw : v ≠ w) :
    let s := (mStep [] (.put k v) mInit).1
    (mStep [] (.txn [.val k v] [.put k w] []) s).2 = .txn 3 true [.put] ∧
      (mStep [] (.txn [.val k w] [.put k w] []) s).2 = .txn 2 false [] := by
  simp [mStep, mInit, MStore.put, MCmp.holds, runOps, MOp.run, hvw]

/-- A delete of a missing key changes nothing; of a present key, takes the next revision. -/
example (k : K) (v : V) :
    (mStep [] (.del k) (mInit : MSt K V)).2 = .del 1 0 ∧
      (mStep [] (.del k) (mStep [] (.put k v) mInit).1).2 = .del 3 1 := by
  simp [mStep, mInit, MStore.put]

end sanity

end linkv
end EtcdGrove
end Perennial
