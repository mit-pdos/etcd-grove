/-
**The server's `LeaseGrant` as the Lease service's handler calls it, at the lessor's history** (the
lease-grant plan's D4, 2026-11-02, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

A sibling of `raftLessor`'s grant conjunct `lessorGrantOk` (left as it is: a premise of the served
theorems), at the same request (its `TTL` read-only, `leaseGrantReqIs`, its `ID` owned,
`leaseGrantReqIdOwn`: `LeaseGrant` writes it, `v3_server.go:436-439`; the wire model's `recvOwn`
since 2026-11-02), with the answer carrying the lease's grant in the lessor's history. `lessorGrantOkL_of_server`
(`ServerLeaseGrant.lean`) derives it from `EtcdServer.LeaseGrant.spec` in a cluster that grants
leases.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseGrant

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

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode

/-- **The server's grant at the lessor's history is `lessorGrantOkG`** at `G id := ∃ i,
leaseGrantedAt E.γ.leases i id` (the lease-grant plan's (F2)). -/
theorem lessorGrantOkG_of_L (s : Loc) (E : apply.AEnv GF) (S : IProp GF) :
    lessorGrantOkL s E S ⊢
      lessorGrantOkG s E S (fun id => iprop(∃ i : Nat, lease.leaseGrantedAt E.γ.leases i id)) := by
  iintro #H
  iunfold lessorGrantOkL at H
  iunfold lessorGrantOkG
  iintro %ci %cd %r %m !> %Φ Hpre HΦ
  wp_apply H $$ [Hpre] as %resp %err ⟨HS, Hans, Hg⟩
  · iexact Hpre
  iapply HΦ
  iframe HS Hans
  icases Hg with (%Hn | ⟨%id, %i, #Hid, #Hgr⟩)
  · ileft; ipureintro; exact Hn
  · iright; iexists id; iframe Hid; iexists i; iexact Hgr

end lemmas

end v3rpc
end EtcdGrove
end Perennial
