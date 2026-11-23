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
