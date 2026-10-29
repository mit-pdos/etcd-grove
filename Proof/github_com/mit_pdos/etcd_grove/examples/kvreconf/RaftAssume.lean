/-
Lean-first (no Rocq counterpart).

# What kvreconf's proof assumes of raft, until raft's tracks prove it (2026-10-29, track C)

The raft laws and specs kvreconf needs that the frozen designs (`notes/spec-first-study/
raft-node-unified-candidate.md`, `raft-decisions-spec.md`) state and raft's API does not have yet,
under their frozen names, collected in one record (`RaftAssume`): every kvreconf proof that needs one
takes the record as an argument, so that when tracks A and B land them the rework is one
instantiation (in kvreconf's `Link.lean`). Not axioms: nothing here is assumed globally, and every
result over it carries the record as a premise until then.

- `committed_confDecodes` (track A, `notes/spec-first-study/raft-decisions-spec.md` §5): every
  committed conf entry decodes; kvreconf's `applyEntry` panics on one that does not.
- `applyChange_asV2` (track B): a legacy change acts as its `AsV2`; kvreconf validates `cc.AsV2()`
  (`validConf`) and applies `cc`.
- The stopped node (track A, U9a; frozen K5/K9): `nodeLive n γ N q` (fractional; whole from
  `RestartNode`), `nodeStopped n γ N` (persistent), `nodeLive_stopped`, `node.Stop` taking the whole
  `nodeLive` and giving `nodeStopped`; each method's stopped answer (the frozen design's one triple is
  the running triple, today's `unifiedSpec`, plus the case `nodeStopped` given in place of the
  running precondition, stated here as `*.stoppedSpec`). kvreconf's `Main` stops every node while its
  loop may be mid-`Ready`, so its calls meet stopped nodes. (The methods' stopped specs are added
  here as the proofs reach them.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Proof.go_etcd_io.raft.v3.InvNodeRule
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.node__Advance

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section assume
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- **What kvreconf assumes of raft** (see the file header), under the frozen names. -/
structure RaftAssume where
  /-- (track A) Every committed conf entry decodes. -/
  committed_confDecodes : ∀ (γ : Cluster) (N : Namespace) (l : List LogEntry),
    isCluster (GF := GF) γ N ∗ isCommittedLogLb (GF := GF) γ l ⊢ ⌜∀ e ∈ l, e.isConfChange → ConfEntryDecodes e⌝
  /-- (track B) A legacy change acts as its `AsV2`. -/
  applyChange_asV2 : ∀ (c : ConfChangeM) (m : Membership),
    Membership.applyChange (.v1 c) m = Membership.applyChange (.v2 c.asV2) m
  /-- (track A, U9a) The running node's token, fractional. -/
  nodeLive : Loc → Cluster → Namespace → Qp → IProp GF
  /-- (track A, U9a) The node has stopped (persistent). -/
  nodeStopped : Loc → Cluster → Namespace → IProp GF
  nodeStopped_persistent : ∀ n γ N, Persistent (nodeStopped n γ N)
  nodeLive_fractional : ∀ n γ N, Fractional (nodeLive n γ N)
  nodeLive_stopped : ∀ n γ N q, nodeLive n γ N q ∗ nodeStopped n γ N ⊢ False
  /-- (track A, U9a) `node.Stop`: the whole token for the stopped node. -/
  Stop_spec : ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
        nodeLive n γ N 1 }}
      (App (Val #(methods node.ty.PointerType go!"Stop" #n)) (Val #()))
    {{ RET #(); nodeStopped n γ N }}
  /-- (track A, U9a) `node.ApplyConfChange` of a stopped node: `nil`, the change given back. -/
  ApplyConfChange_stoppedSpec : ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64)
      (c : GoInterface) (dq : DFrac) (o : ConfChangeIM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
        ownConfChangeI c dq (some o) ∗ nodeStopped n γ N }}
      (App (Val #(methods node.ty.PointerType go!"ApplyConfChange" #n)) (Val #c))
    {{ RET #null; ownConfChangeI c dq (some o) }}
  /-- (track A, U9a) `node.Advance` of a stopped node returns. -/
  Advance_stoppedSpec : ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
        nodeStopped n γ N }}
      (App (Val #(methods node.ty.PointerType go!"Advance" #n)) (Val #()))
    {{ RET #(); True }}

end assume

end kvreconf
end EtcdGrove
end Perennial
