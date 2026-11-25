/-
Ported from dsverify-lab examples/gryff/proof/Harness/Model.lean (run gryff-bump-1, lab master 915f964;
notes/dsv-gryff.md), unchanged.

The harness's models of services (harness plan M1, `notes/harness-m1.md` section 1), and what a
history linearizable for a model is.

A `Model` is a state machine with a step *relation* (outputs may be nondeterministic). The client
spec (`ClientSpec.lean`), the generic lemma and the checkers' specs are all stated over one.

A recorded history is a list of `HOp`s: an operation's input, its output (`none`: pending, the
client never learned it), and its call and return stamps. `Linearizable M h` is linearizability
with pending operations (Herlihy and Wing): some of the pending operations, each with some output,
together with every completed operation, are ordered so that the order respects real time (an
operation that returned before another was called comes first) and is a run of `M` from
`M.init`. The others are dropped (they never took effect).

Instances: the write-once register (M0's Paxos), the register with read, write and
compare-and-swap (Gryff), the key-value map with get and put (eliben/raft, hashicorp/raft), and
the key-value map with get, put and range scan (SwiftPaxos).

Pure Lean: nothing here depends on Go or Perennial.
-/
module

@[expose] public section

namespace Perennial.dsverify_lab.harness

/-- A service's model: a state machine whose step relates a state and an input to a next state and
an output. -/
structure Model where
  State : Type
  Input : Type
  Output : Type
  init : State
  step : State → Input → State → Output → Prop

namespace Model

/-- `M.Run s ios`: the operations `ios` (input, output), in order, are a run of `M` from `s`. -/
inductive Run (M : Model) : M.State → List (M.Input × M.Output) → Prop
  | nil (s : M.State) : Run M s []
  | cons (s s' : M.State) (i : M.Input) (o : M.Output) (ios : List (M.Input × M.Output)) :
      M.step s i s' o → Run M s' ios → Run M s ((i, o) :: ios)

end Model

/-- An operation of a recorded history: its input, its output (`none` if pending: called, never
returned, so the client does not know whether or how it took effect), and the stamps of its call
and (if it returned) its return. -/
structure HOp (I O : Type) where
  input : I
  output : Option O
  call : Int
  ret : Int

/-- `a` precedes `b` in real time: `a` returned before `b` was called. A pending operation precedes
nothing. -/
def HOp.precedes {I O : Type} (a b : HOp I O) : Prop :=
  a.output.isSome ∧ a.ret < b.call

/-- Every pending operation of `h` returns at or after every call of `h` (M1c). The recorder
places pending returns after every stamp (`recorder.Ops`); porcupine, which orders operations by
their closed intervals and gives a pending one no special treatment, needs it (without it a pending
operation whose return stamp precedes another's call could not be linearized after that one). -/
def PendingLast {I O : Type} (h : List (HOp I O)) : Prop :=
  ∀ p ∈ h, p.output = none → ∀ x ∈ h, x.call ≤ p.ret

/-- `h` is linearizable for `M`: a linearization `lin`, a list of (index into `h`, output), holds
each operation at most once; every completed operation, with its own output; pending ones with any
output, or not at all; it respects real time; and it is a run of `M` from `M.init`. -/
def Linearizable (M : Model) (h : List (HOp M.Input M.Output)) : Prop :=
  ∃ lin : List (Nat × M.Output),
    (lin.map Prod.fst).Nodup ∧
    (∀ k o, (k, o) ∈ lin → ∃ op, h[k]? = some op ∧ ∀ o', op.output = some o' → o = o') ∧
    (∀ k op o, h[k]? = some op → op.output = some o → (k, o) ∈ lin) ∧
    (∀ (a b : Nat) (ha : a < lin.length) (hb : b < lin.length) (opa opb : HOp M.Input M.Output),
      h[lin[a].1]? = some opa → h[lin[b].1]? = some opb → opb.precedes opa → b < a) ∧
    M.Run M.init (lin.filterMap fun ko => (h[ko.1]?).map fun op => (op.input, ko.2))

/-! ## Instances -/

/-- The write-once register (M0's Paxos): `Propose v` decides `v` if nothing is decided, and
returns the decided value. -/
def writeOnce (V : Type) : Model where
  State := Option V
  Input := V
  Output := V
  init := none
  step s v s' o := s' = some (s.getD v) ∧ o = s.getD v

/-- Inputs of the register with compare-and-swap. -/
inductive RegInput (V : Type) where
  | read
  | write (v : V)
  | cas (old new : V)

/-- Outputs of the register with compare-and-swap. -/
inductive RegOutput (V : Type) where
  | value (v : V)
  | done
  | swapped (ok : Bool)

/-- The register with read, write and compare-and-swap (Gryff), from `v0`. -/
def register (V : Type) (v0 : V) : Model where
  State := V
  Input := RegInput V
  Output := RegOutput V
  init := v0
  step s i s' o := match i with
    | .read => s' = s ∧ o = .value s
    | .write v => s' = v ∧ o = .done
    | .cas a b => (s = a ∧ s' = b ∧ o = .swapped true) ∨ (s ≠ a ∧ s' = s ∧ o = .swapped false)

/-- Inputs of the key-value map. -/
inductive KvInput (K V : Type) where
  | get (k : K)
  | put (k : K) (v : V)

/-- Outputs of the key-value map (`got none`: the key was never written). -/
inductive KvOutput (V : Type) where
  | got (v : Option V)
  | done

/-- The key-value map with get and put (eliben/raft, hashicorp/raft), from the empty map. -/
def kv (K V : Type) [DecidableEq K] : Model where
  State := K → Option V
  Input := KvInput K V
  Output := KvOutput V
  init := fun _ => none
  step s i s' o := match i with
    | .get k => s' = s ∧ o = .got (s k)
    | .put k v => s' = (fun k' => if k' = k then some v else s k') ∧ o = .done

/-- Inputs of the key-value map with range scan: keys are 64-bit words (Go's `uint64`); `scan k n`
reads the keys `k, k+1, …, k+n` (`scanKeys`). -/
inductive KvsInput (V : Type) where
  | get (k : BitVec 64)
  | put (k : BitVec 64) (v : V)
  | scan (k n : BitVec 64)

/-- Outputs of the key-value map with range scan (`got none`: the key was never written;
`scanned v`: a scan's values, concatenated). -/
inductive KvsOutput (V : Type) where
  | got (v : Option V)
  | done
  | scanned (v : V)

/-- The keys a scan of `n` from `k` reads, in increasing order: `k, k+1, …, k+n`, those below
`2^64` (the range does not wrap around). -/
def scanKeys (k n : BitVec 64) : List (BitVec 64) :=
  (List.range' k.toNat (min (n.toNat + 1) (2 ^ 64 - k.toNat))).map (BitVec.ofNat 64)

/-- The key-value map with get, put and range scan, from the empty map (SwiftPaxos's state machine;
kits/epaxos-net-stage2). Values are lists over `α` (Go strings: `kvScan w8`), so that a scan can
return the values of the keys it reads that are present, in key order, concatenated, as SwiftPaxos's
SCAN does. -/
def kvScan (α : Type) : Model where
  State := BitVec 64 → Option (List α)
  Input := KvsInput (List α)
  Output := KvsOutput (List α)
  init := fun _ => none
  step s i s' o := match i with
    | .get k => s' = s ∧ o = .got (s k)
    | .put k v => s' = (fun k' => if k' = k then some v else s k') ∧ o = .done
    | .scan k n => s' = s ∧ o = .scanned ((scanKeys k n).filterMap s).flatten

/-- Sanity check: one proposal, returned, is linearizable for the write-once register. -/
example (v : Nat) :
    Linearizable (writeOnce Nat) [{ input := v, output := some v, call := 1, ret := 2 }] := by
  refine ⟨[(0, v)], by simp, ?_, ?_, ?_, ?_⟩
  · intro k o h; simp at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, rfl, fun o' h => Option.some.inj h⟩
  · intro k op o h1 h2
    cases k with
    | zero => simp at h1; subst h1; injection h2 with h; subst h; simp
    | succ k => simp at h1
  · intro a b ha hb opa opb h1 h2 hp
    simp only [List.length_singleton] at ha hb
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp at h1 h2; subst h1 h2; simp [HOp.precedes] at hp
  · exact .cons _ _ _ _ _ ⟨rfl, rfl⟩ (.nil _)

end Perennial.dsverify_lab.harness
