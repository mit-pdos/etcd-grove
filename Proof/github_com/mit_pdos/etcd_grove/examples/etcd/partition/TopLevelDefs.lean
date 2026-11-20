/- Lean-first (no Rocq counterpart).

# `etcd/partition`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Adequacy.lean`, `AdequacyWatch.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.SchedLit
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

noncomputable section

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

/-- The functors: putget's (`putgetGF`: the universal camera `AllG` at slot 0, then invariants,
later credits, GooseLang's heap, prophecies and package state), and
iris-lean's non-atomic invariants at slot 11 (as the counter's `counterGF`). Every other slot is
the unit functor. -/
def linkvGF : BundledGFunctors := fun i =>
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
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- **A ghost-state instance at the local context `lctx`** (as putget's `heapAt`). -/
abbrev linkvHeapAt (hG : HeapGS .hasLC linkvGF) (lctx : GoLocalContext) : HeapGS .hasLC linkvGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The program: `linkv3p`'s initialization, then `Main(clients, ops, sched)` with the schedule
built as a slice literal. -/
def linkv3pProgram [GoSemanticsFunctions] (clients ops : w64)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.partition.initialize' #() ;;
  App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.Main)) (Val #clients))
    (Val #ops)) (schedLit steps)

/-- The program's addresses: the three members' peer addresses, their client addresses, and the
bridges' addresses (2026-10-21, `notes/client-cut-plan.md`). -/
def linkv3pAddrs : List GoString :=
  [etcd_partition.peerAddr₁, etcd_partition.peerAddr₂, etcd_partition.peerAddr₃,
    etcd_partition.clientAddr₁, etcd_partition.clientAddr₂, etcd_partition.clientAddr₃,
    etcd_partition.bridgeAddr₁, etcd_partition.bridgeAddr₂, etcd_partition.bridgeAddr₃]

/-- The metric names the program's initialization registers (its closure's `PRE_RES` packages', D16;
mustreg, 2026-11-20, until then the read package's two, `readRegPerm`): its `initNames`. -/
def linkv3pNames : List GoString := _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.etcd.partition.initNames

end adequacy
end EtcdGrove
end Perennial

end

section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

section adequacy

variable [go_gctx : GoGlobalContext]

/-- The watch run: `linkv3p`'s initialization, then `MainWatch(nw, nops, sched)` with the schedule
built as a slice literal. -/
def linkv3pWatchProgram [GoSemanticsFunctions] (nw nops : w64)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.partition.initialize' #() ;;
  App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.MainWatch)) (Val #nw))
    (Val #nops)) (schedLit steps)

end adequacy
end EtcdGrove
end Perennial

end

end
