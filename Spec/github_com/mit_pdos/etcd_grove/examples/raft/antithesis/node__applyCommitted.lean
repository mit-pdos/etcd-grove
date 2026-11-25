/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).applyCommitted(by, ents)` of normal entries: none, nothing; otherwise the `apply` report
(the handled message's `recv` first if pending), `switchConf` of each (a normal entry: nothing),
and `applied` at the last one's index.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev node.applyCommitted.spec : Prop :=
  ∀ (c : Loc) (γ : AntNames) (n : Loc) (j : Fin γ.R.N) (by_ : GoString) (sl : GoSlice) (dq : DFrac)
    (els : List Loc) (es : List EntryM) (a : w64) (cl : Loc) (o : Option AntCheck.Event) (Q : IProp GF), AllNormal es →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antCluster c γ ∗ nodeRO c γ n j ∗ emitOk n ∗ sl ↦*{dq} els ∗ ([∗list] p;e ∈ els;es, entRO p e) ∗
      n.[H.node, go!"applied"] ↦ a ∗ n.[H.node, go!"cause"] ↦ cl ∗ pendingCause cl o ∗
      reports γ.strm ((if es = [] then [] else o.toList ++ [applyEvM by_ es]).map
        (atNode (AntSim.nameOf (AntSim.nodeId j)))) Q }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"applyCommitted")) (Val #by_)) (Val #sl))
  {{ RET #(); emitOk n ∗ sl ↦*{dq} els ∗ ([∗list] p;e ∈ els;es, entRO p e) ∗
      (if es = [] then n.[H.node, go!"applied"] ↦ a ∗ n.[H.node, go!"cause"] ↦ cl ∗ pendingCause cl o
       else n.[H.node, go!"applied"] ↦ (es.getLast?.map (·.Index')).getD a ∗ n.[H.node, go!"cause"] ↦ null) ∗ Q }}

end spec

end AntHarness
end EtcdGrove
end Perennial
