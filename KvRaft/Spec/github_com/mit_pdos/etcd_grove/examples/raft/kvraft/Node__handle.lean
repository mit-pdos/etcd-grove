/-
`nd.handle(kind, p, timeout)` (`examples/raft/kvraft/node.go`): one client request of kind `kind`
and payload `p` (holding `pl`, with its fact `reqOk F id kind pl`, what the request frame carried:
`Proto.lean`), run on the node; `good` false if it has no answer, else the answer `v`, with the fact
the reply frame carries (`ansOk F id kind pl v`), of a length a frame takes. A spec at the store's
seam `rep` (`NodeDefs.lean`), with its conf law (`confLaw`, over what `GetConfChange` reads back,
`cf`): its parameters `F`, `rep`, `cf` are fixed by the store layer.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev Node.handle.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (cf : GoInterface → List w8 → IProp GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64) (kind : w8) (p : GoSlice)
    (pl : List w8) (dq : DFrac) (tmo : _root_.Perennial.time.Duration),
  pl.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      isNodeS F rep stp nd γ N id ∗ confLaw F rep cf γ N id ∗ context.isClosedchanInit ∗
      p ↦*{dq} pl ∗ reqOk F id kind pl }}
    (App (App (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node.ty
      @!! go!"handle")) (Val #kind)) (Val #p)) (Val #tmo))
  {{ (ans : GoSlice) (good : Bool), RET (PairV #ans #good);
      ⌜good = false⌝ ∨
      ∃ (v : List w8), ⌜good = true⌝ ∗ ans ↦* v ∗ ansOk F id kind pl v }}

end spec

end kvraft
end EtcdGrove
end Perennial
