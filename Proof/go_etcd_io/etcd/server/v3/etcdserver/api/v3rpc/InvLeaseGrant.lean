/-
**The server's `LeaseGrant` as the Lease service's handler calls it, at the lessor's history** (the
lease-grant plan's D4, 2026-11-02, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

A sibling of `raftLessor`'s grant conjunct `lessorGrantOk` (left as it is: a premise of the served
theorems), at the same request (its `TTL` read-only, `leaseGrantReqIs`, its `ID` owned,
`leaseGrantReqIdOwn`: `LeaseGrant` writes it, `v3_server.go:436-439`; the wire model's `recvOwn`
since 2026-11-02), with the answer carrying the lease's grant in the lessor's history. `lessorGrantOkL_of_server` derives it
from `EtcdServer.LeaseGrant.spec` in a cluster that grants leases (not proved: Draft).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseGrant

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The server's `LeaseGrant` at the lessor's history** (see the file header): `lessorGrantOk`
and, on success, the response's lease granted at an index of the
lessor `E.γ.leases`'s history. -/
def lessorGrantOkL (s : Loc) (E : apply.AEnv GF) (S : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64 × w64),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseGrantReqIs r m ∗
        leaseGrantReqIdOwn r m.2 }}
      (App (App (Val (srvM s go!"LeaseGrant")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseGrantAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ (id : w64) (i : Nat),
          structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗
          lease.leaseGrantedAt E.γ.leases i id) }})

instance lessorGrantOkL_persistent (s : Loc) (E : apply.AEnv GF) (S : IProp GF) :
    Persistent (lessorGrantOkL s E S) := by
  unfold lessorGrantOkL; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The server's `LeaseGrant` meets `lessorGrantOkL`** in a cluster that grants leases, given the
run's resource `S` lending the request path's readers (`EtcdServer.LeaseGrant.spec`'s). Not proved
(Draft): the header's answer (`leaseHdrAns`: the revision reached, from the applied witness) and
the run's context (`grpcRunCtx`). -/
theorem lessorGrantOkL_of_server (hLG : EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvGrantsLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkL s E S := by
  sorry

end proof

end v3rpc
end EtcdGrove
end Perennial
