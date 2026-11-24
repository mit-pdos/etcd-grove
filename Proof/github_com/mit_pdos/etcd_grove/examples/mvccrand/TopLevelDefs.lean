/- Lean-first (no Rocq counterpart).

# `mvccrand`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.PkgTable
public import Proof.runtime.StartFiles
public import Proof.runtime.Threads
public import Robustness.Statement

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

/-- The functors (as `putgetGF`): the universal camera (`AllG`) at slot 0, then invariants, later
credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def mvccrandGF : BundledGFunctors := fun i =>
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

end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

section adequacy

variable [go_gctx : GoGlobalContext]

/-- `Main`'s configuration (`Run(Config{Path: "mvccrand.db", Seed: 1, Ops: 1000, Readers: 4,
Reads: 200, Watchers: 8})`), with the file `b` of the directory `r` (S3e). -/
def mvccrandCfg (r : GoString) : github_com.mit_pdos.etcd_grove.examples.mvccrand.Config :=
  ⟨Fs.child r go!"mvccrand.db", W64 1, W64 1000, W64 4, W64 200, W64 8, W64 0⟩

/-- The program: `mvccrand`'s initialization, then `Run` of `Main`'s configuration with the file
`r/mvccrand.db`, its report dropped, as `Main` does (S3e; until then `Main()`, whose `mvccrand.db`
is relative). -/
def mvccrandProgram [GoSemanticsFunctions] (r : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.mvccrand.initialize' #() ;;
  ((@! github_com.mit_pdos.etcd_grove.examples.mvccrand.Run) #(mvccrandCfg r) ;; #())

end adequacy
end EtcdGrove
end Perennial

end

end
