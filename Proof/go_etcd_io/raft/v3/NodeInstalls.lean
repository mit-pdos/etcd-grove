/- (2026-11-22, kvraft decision B: `notes/raft-cluster-global.md`) A node handle's install record, by
a countable name: what a client pins in place of the handle. -/
module

public import Proof.go_etcd_io.raft.v3.InvNodeRule
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **The ghost name of a node's record of the snapshots handed out for installation** (sealed): a
`GName`, so a client can pin it in a ghost variable where it cannot pin the handle (`NodeH` holds
the cluster's names, functions among them, so it is not `Pos.Countable`). `nodeInstalledIndex`
depends on the handle only through it (`nodeInstalledIndex_installs`). (The etcd server pins its
node's before `StartNode` returns the handle: `srvStoredOrigin`.) -/
@[no_expose] def NodeH.installs (n : NodeH) : GName := (ApiImpl.NodeH.names n).sn.installs

/-- `nodeInstalledIndex` of two handles with the same install record agree. -/
theorem nodeInstalledIndex_installs (γ : Cluster) (n n' : NodeH) (h : n.installs = n'.installs)
    (i : w64) : nodeInstalledIndex (GF := GF) γ n i ⊢ nodeInstalledIndex γ n' i := by
  unfold nodeInstalledIndex NodeH.installs at *
  iintro ⟨%γn, Htab, Hseen⟩
  iunfold ApiImpl.nodeTabOk at Htab
  icases Htab with %hγn
  subst hγn
  iexists ApiImpl.NodeH.names n'
  isplitr
  · iunfold ApiImpl.nodeTabOk; ipureintro; rfl
  rw [← h]
  iexact Hseen

end api

end EtcdGrove
end Perennial
