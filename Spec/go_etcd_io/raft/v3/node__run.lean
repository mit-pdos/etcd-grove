/- Lean-first (no Rocq counterpart).

## `node.run()` (node.go:343)

The node's goroutine, forked by `RestartNode`: it owns the `RawNode` (`ownRawNode`, idle:
no `Ready` outstanding), `run`'s half of `dlv` at the committed log handed out so far,
the whole of `rof` (no `Ready` handed out), and the budget's bound on its term. It never
returns (`stop` is never sent on).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `run` starts with (see the file header). -/
def runPre (γ : NodeNames) (id : w64) (n : Loc) : IProp GF :=
  iprop(∃ (nv : node) (rs : RNState) (x : List raftpb.Entry × List raftpb.Entry ×
      List raftpb.Entry),
    n ↦□ nv ∗ ownRawNode γ.raft nv.rn' id rs ∗
    ⌜rs.steps = [] ∧ rs.unpersisted = [] ∧ rs.storage = γ.stor⌝ ∗
    dghostVar γ.dlv (DFrac.own (1 : Qp).half) rs.delivered ∗
    dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗ dghostVar γ.rof (DFrac.own (1 : Qp).half) x ∗
    termLB γ.bud rs.term)

/-- See the file header. -/
abbrev node.run.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      runPre γ id n }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
