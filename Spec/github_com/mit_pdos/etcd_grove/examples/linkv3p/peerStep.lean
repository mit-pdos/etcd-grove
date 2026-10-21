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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- **`peerStep(srvs, kind, a, b)`**, over the read-only slice of servers `ss`, each a member of
the network `γn`: it returns. -/
abbrev peerStep.spec : Prop :=
  ∀ (γn : NetNames GF) (srvs : GoSlice) (ss : List Loc) (kind a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      srvs ↦*□ ss ∗ ([∗list] s ∈ ss, ∃ id : w64, srvNetMember γn s id) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.peerStep))
      (Val #srvs)) (Val #kind)) (Val #a)) (Val #b))
  {{ RET #(); True }}

end spec

end linkv3p
end EtcdGrove
end Perennial
