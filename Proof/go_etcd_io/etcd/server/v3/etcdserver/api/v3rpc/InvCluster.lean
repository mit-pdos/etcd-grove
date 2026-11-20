/-
**The Cluster service's handlers' vocabulary** (auth-mediation M2, 2026-11-20): the
`*ClusterServer`'s fields (`clusterServerIs`, what `NewClusterServer` builds), what its `header`
reads of the server (`clusterHdrOk`), and a membership handler's outcome (`memberOutC`: the
configuration change's answer, or an error `togRPCError` made of the server's, with the refusal's
reason). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthAdmin
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MemberContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*ClusterServer` `p`** (read-only): its `cluster` the server's `*RaftCluster` `cl` (as
an `api.Cluster`) and its `server` the server `s` (`NewClusterServer`'s
`&ClusterServer{cluster: s.Cluster(), server: s}`). -/
def clusterServerIs (p s cl : Loc) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer go!"cluster" p ↦□
      (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty)
        #cl : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer go!"server" p ↦□ s)

instance clusterServerIs_persistent (p s cl : Loc) :
    Persistent (clusterServerIs (GF := GF) p s cl) := by
  unfold clusterServerIs; infer_instance

/-- **What `header` reads** (persistent): the cluster `cl`'s id, the server `s`'s member id (both
read-only), its leader and term cells (atomics, in invariants). -/
def clusterHdrOk (s cl : Loc) : IProp GF :=
  iprop(∃ cid mid : w64, membership.clusterCid cl cid ∗ srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t))

instance clusterHdrOk_persistent (s cl : Loc) : Persistent (clusterHdrOk (GF := GF) s cl) := by
  unfold clusterHdrOk; infer_instance

/-- **A membership handler's outcome** (`MemberAdd`, `MemberRemove`, `MemberUpdate`): an error
grpc's server takes (`srvErrOk`); on `nil` the change's answer `Qin` at `nil`; on an error (and no
response) the error `togRPCError` made (`grpcErrOut`) of a server error `e0` that is the change's
answer `Qin`, or a refusal `W e0` (the guard's reason, or the strict check's answer) with the
caller's `Pin` kept. -/
def memberOutC (Pin : IProp GF) (Qin : GoSlice → GoInterface → IProp GF)
    (W : GoInterface → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(go_etcd_io.etcd.cache.v3.srvErrOk err ∗
    ((⌜err = GoInterface.nil⌝ ∗ ∃ sl : GoSlice, Qin sl GoInterface.nil) ∨
     (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e0 : GoInterface, ⌜e0 ≠ GoInterface.nil⌝ ∗
        grpcErrOut (fun _ => True) e0 err ∗ ((∃ sl : GoSlice, Qin sl e0) ∨ (Pin ∗ W e0)))))

end defs

end v3rpc
end EtcdGrove
end Perennial
