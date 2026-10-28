/-
`peerStep(srvs, kind, a, b)` (`examples/linkv3p/linkv3p.go`; `notes/client-cut-plan.md` K0): cuts
(`kind == PeerCut`) or mends the link between members `a` and `b` of `srvs`, both directions
(`EtcdServer.CutPeer`/`MendPeer`); indices out of range or equal do nothing. Lean-first (no Rocq
counterpart). Until 2026-10-21 the body of `partitioner`'s loop.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- **`peerStep(srvs, kind, a, b)`**, over the read-only slice of servers `ss`, each a member of
the network `γn` with one of its transport's reader tokens (`common.srvPeerCtl`, 2026-10-24, rafthttp
stage 6d: what its `CutPeer`/`MendPeer` borrow): it returns them. The method set's premise
`PeerPausable` (`*peer` implements `Pausable`, `CutPeer`'s). -/
abbrev peerStep.spec : Prop :=
  PeerPausable →
  ∀ (γn : NetNames GF) (srvs : GoSlice) (ss : List Loc) (kind a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      srvs ↦*□ ss ∗ ([∗list] s ∈ ss, ∃ id : w64, common.srvPeerCtl γn s id) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.peerStep))
      (Val #srvs)) (Val #kind)) (Val #a)) (Val #b))
  {{ RET #(); [∗list] s ∈ ss, ∃ id : w64, common.srvPeerCtl γn s id }}

end spec

end linkv3p
end EtcdGrove
end Perennial
