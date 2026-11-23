/-
The key-value map with get, put and range scan as a pure sequential model (the lab's
`Harness/Model.lean`, `kvScan` and its vocabulary, harness lab commit 7db3cd9), which the EPaxos
protocol model (`Model/`) executes commands against. Pure Lean.

(The lab's harness checked histories against it; here the history is checked by the kit's porcupine
model, `examples/epaxosnet/model.go`, the store with pending writes; the kit's model proof relates
the two.)
-/
module

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.kvs

/-- A service's model: a state machine whose step relates a state and an input to a next state and
an output. -/
structure Model where
  State : Type
  Input : Type
  Output : Type
  init : State
  step : State → Input → State → Output → Prop

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

/-- The key-value map with get, put and range scan, from the empty map (SwiftPaxos's state
machine). Values are lists over `α` (Go strings: `kvScan w8`), so that a scan can return the values
of the keys it reads that are present, in key order, concatenated, as SwiftPaxos's SCAN does. -/
def kvScan (α : Type) : Model where
  State := BitVec 64 → Option (List α)
  Input := KvsInput (List α)
  Output := KvsOutput (List α)
  init := fun _ => none
  step s i s' o := match i with
    | .get k => s' = s ∧ o = .got (s k)
    | .put k v => s' = (fun k' => if k' = k then some v else s k') ∧ o = .done
    | .scan k n => s' = s ∧ o = .scanned ((scanKeys k n).filterMap s).flatten

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.kvs
