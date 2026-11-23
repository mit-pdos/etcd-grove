/-
The lab's service model the swiftpaxos invariant states its linearizability state in
(dsverify-lab `harness/lean/Harness/Model.lean`: `Model`, `kv`, copied). Here the kit checks
histories with `examples/lib/remote` against the kit's own `Model` (a key-value map with pending
puts); the invariant's `kv GoString GoString` state is related to it in the kit's proof.
-/
module

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos

/-- A service's model: a state machine whose step relates a state and an input to a next state
and an output (the lab's `Model`). -/
structure Model where
  State : Type
  Input : Type
  Output : Type
  init : State
  step : State → Input → State → Output → Prop

/-- Inputs of the key-value map. -/
inductive KvInput (K V : Type) where
  | get (k : K)
  | put (k : K) (v : V)

/-- Outputs of the key-value map (`got none`: the key was never written). -/
inductive KvOutput (V : Type) where
  | got (v : Option V)
  | done

/-- The key-value map with get and put, from the empty map (the lab's `kv`). -/
def kv (K V : Type) [DecidableEq K] : Model where
  State := K → Option V
  Input := KvInput K V
  Output := KvOutput V
  init := fun _ => none
  step s i s' o := match i with
    | .get k => s' = s ∧ o = .got (s k)
    | .put k v => s' = (fun k' => if k' = k then some v else s k') ∧ o = .done

end Perennial.github_com.imdea_software.swiftpaxos
