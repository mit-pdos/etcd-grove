/- Lean-first (no Rocq counterpart).

# `raft/antithesis`: the definitions its top-level statement is written in

The program the example's top-level theorem (`raft_antithesis_safe`, `notes/antithesis-s4-design.md`
§1) is about, and the functors it is stated at, so that the statement
(`Spec/.../antithesis/TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
`antGF` has the same eight slots as the trace check's `tcGF`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.runtime.Threads
public import Proof.log.NewModel
public import Code.github_com.mit_pdos.etcd_grove.examples.raft.antithesis

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def antGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-! ## The bounds of the top-level statement -/

/-- **The thread bound**: executions along which fewer than `2 ^ 31` threads are live at once.
A cap the proof needs: the network's goroutines are counted in a `sync.WaitGroup`
(`Cluster.send`, `isNetJoin`), whose counter is an `int32` in Go, so it panics past `2 ^ 31`;
the harness's specs take `[ThreadBoundLe GF (2 ^ 31)]`, which the adequacy proves from this bound. -/
def antThreadBound : Nat := 2 ^ 31

/-- **The step bound**: executions of fewer than `2 ^ 61 - 3` steps, the most the proof allows.
An execution of `n` steps gets `n + 1` time receipts (`receiptBound`), and the harness takes
`antRunFits` (`receiptBound + 3 ≤ 2 ^ 61`): raft's `readyFits` (every index raft hands
`MemoryStorage.Append` below `2 ^ 61`) and the checker's number bound (`Stream.Bounded`: every
number of the stream below `2 ^ 61`, the binding's `numBound`). -/
def antStepBound : Nat := 2 ^ 61 - 3

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The Antithesis check's program: the package's initialization, then `Main()`
(`examples/raft/antithesis/main.go`). -/
def antithesisProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.antithesis.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Main) #()

end adequacy

end EtcdGrove
end Perennial

end
