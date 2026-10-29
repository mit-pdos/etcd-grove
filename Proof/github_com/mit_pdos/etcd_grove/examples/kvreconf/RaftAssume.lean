/-
Lean-first (no Rocq counterpart).

# What kvreconf's proof assumes of raft, until raft's tracks prove it (2026-10-29, track C)

The raft laws and specs kvreconf needs that the frozen designs (`notes/spec-first-study/
raft-node-unified-candidate.md`, `raft-decisions-spec.md`) state and raft's API does not have yet,
under their frozen names, collected in one record (`RaftAssume`): every kvreconf proof that needs one
takes the record as an argument, so that when tracks A and B land them the rework is one
instantiation (in kvreconf's `Link.lean`). Not axioms: nothing here is assumed globally, and every
result over it carries the record as a premise until then.

- (`committed_confDecodes` was here until 2026-10-29: the store's own invariant gives it, every
  committed conf entry being a proposed one or raft's automatic leave, `confShaped_of_ops`.)
- (`applyChange_asV2` was here until track B proved it, `ConfchangeApi.lean`, 2026-10-29.)
- The stopped node (track A, U9a; frozen K5/K9): `nodeLive n γ N q` (fractional; whole from
  `RestartNode`), `nodeStopped n γ N` (persistent), `nodeLive_stopped`, `node.Stop` taking the whole
  `nodeLive` and giving `nodeStopped`; each method's stopped answer (the frozen design's one triple is
  the running triple, today's `unifiedSpec`, plus the case `nodeStopped` given in place of the
  running precondition, stated here as `*.stoppedSpec`). kvreconf's `Main` stops every node while its
  loop may be mid-`Ready`, so its calls meet stopped nodes. (The methods' stopped specs are added
  here as the proofs reach them.)
- The running triples of the methods kvreconf calls on a node that may stop meanwhile, in the frozen
  one-triple form (K9: a stopped node given the running precondition owes only the stopped answer, so
  the post is the running post or the stopped answer with `nodeStopped`) and with U5's exclusions
  lifted (no `autoLeave = false` premise: U5 landed on `raft-unified` after this branch's base):
  `ApplyConfChange_spec` (today's `node.ApplyConfChange.unifiedSpec`, its stopped disjunct `nil` with
  the view unchanged).
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
  /-- (track A, U9a with K9; U5) `node.ApplyConfChange.unifiedSpec` on a node that may stop: the
  running answer, or `nil` with the node stopped and the view unchanged; no auto-leave premise. -/
  ApplyConfChange_spec : ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (c : GoInterface)
      (o o' : ConfChangeIM) (l : List LogEntry) (k : Nat) (e : LogEntry) (v : ConfigView)
      (m' : Membership),
    v.applied ≤ k → l[k]? = some e → e.isConfChange →
    Membership.applyChange o' v.membership = some m' →
    Membership.applyChange o v.membership = some m' →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
        isCluster γ N ∗ confDecided γ k (.apply o') ∗ ownConfChangeI c DFrac.discard (some o) ∗
        nodeConfig n γ N v ∗ deliveredLogLb n γ N l ∗ skippedIn γ l v.applied k }}
      (App (Val #(methods node.ty.PointerType go!"ApplyConfChange" #n)) (Val #c))
    {{ (csp : Loc), RET #csp; (∃ cs : ConfStateM, csPts csp (DFrac.own 1) cs true ∗
          nodeConfig n γ N ⟨k + 1, m'⟩ ∗ ⌜confStateIs cs m'⌝) ∨
        (⌜csp = null⌝ ∗ nodeStopped n γ N ∗ nodeConfig n γ N v) }}
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

instance RaftAssume.nodeStopped_pers (RA : RaftAssume (GF := GF)) (n : Loc) (γ : Cluster)
    (N : Namespace) : Persistent (RA.nodeStopped n γ N) :=
  RA.nodeStopped_persistent n γ N

end assume

end kvreconf
end EtcdGrove
end Perennial
