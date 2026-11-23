/-
The node package's sealed slots (stage 1 interface: their names; their bodies are the node package's).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Hyps
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- Node `n` at address `a` (persistent): its fields, its store, its lock and invariant
(node package; intended: the lock invariant holds the role, the neighbors (each a client of its
address), the latest map (the store's newest committed versions; the commit log's, with the tail
token, while the active tail) and half of the store's contents; the invariant the other half,
the node's commit log `Ln` with `∀ k, cvOf Ln k = S.maxCommitted k`, and the items' facts (each a version; committed ones committed)). -/
def isNode (cfg : Cfg GF) (n : Loc) (a : GoString) : IProp GF :=
  iprop(craqCtx cfg ∗ ⌜a ∈ cfg.chain⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗
    NodeP.isNodeDef cfg n a)

/-- What node `n`'s `Start` consumes (node package; intended: its unconnected coordinator
client). -/
def nodeStartRes (cfg : Cfg GF) (n : Loc) (a : GoString) : IProp GF :=
  iprop(craqCtx cfg ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗
    NodeP.startResDef cfg n)

instance isNode_persistent (cfg : Cfg GF) (n : Loc) (a : GoString) :
    Persistent (isNode (hG := hG) cfg n a) := by
  unfold isNode; infer_instance

end slots

end github_com.despreston.go_craq

end Perennial
