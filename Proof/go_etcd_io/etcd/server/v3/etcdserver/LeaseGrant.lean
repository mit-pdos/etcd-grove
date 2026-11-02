/-
**The server's lease grant** (the lease-grant plan's D3/D4, 2026-11-02, `notes/lease-grant-plan.md`):
the vocabulary of `EtcdServer.LeaseGrant`'s triple. Lean-first (no Rocq counterpart).

A cluster **grants leases** (`srvGrantsLeases`) when its KV names say so (`KVNames.lg`: its lessor
monotone, `NewServer`'s `NewLessor` call), auth is off (the grant guard `srvGrantGuard`), and the
deployment premise `lease.leasesNoExpiry` holds (no lease expires during the run: the expiry loop
sends nothing). There a grant the server answers is in the lessor's history
(`lease.leaseGrantedAt`), so every later `Leases()` lists it (`lease.leaseGrantedAt_listed`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The cluster grants leases** (see the file header): the KV names' `lg`, auth off (required:
the grant guard `srvGrantGuard` is `False` with auth on, whose layer rests on the lessor finding no
lease, `srvLessorNil`), and the deployment premise `lease.leasesNoExpiry`. -/
def srvGrantsLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop :=
  ρ.rd.kv.lg = true ∧ E.authOn = false ∧ lease.leasesNoExpiry

/-- **A decoded `*pb.LeaseGrantRequest` `r`**: its `TTL` read-only, its `ID` owned
(`LeaseGrant` writes a fresh id there when it is `0`, `v3_server.go:436-439`). -/
def leaseGrantReqOwn (r : Loc) (ttl id : w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" r ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦ id)

/-- **The server's grant response** `resp` (the apply thread's `LeaseGrant`, `backend.go`): its
lease `id` (not `0`), `TTL` and `Error` read-only, its header's id fields owned at the applied log
`log` (`apply.appliedHdr`; a witness the request was applied there, `appliedWit`) and its revision
read-only, not `0`, a revision of that log (`newHeader`'s: the store's current one), the log
certified (`mvcc.certOk`: with the revision below its length, the clients' `etcdReached`,
`v3rpc.etcdReached_of_certOk`, which `leaseHdrAns` asks; the plan's question 3), and the lease
granted at an index `i` of the lessor's history. -/
def leaseGrantedResp (E : apply.AEnv GF) (ρ : ReqNames) (resp : Loc) : IProp GF :=
  iprop(∃ (log : mvcc.Log) (id ttl : w64) (e : GoString) (i : Nat) (h : Loc) (rv : w64),
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗
    ⌜rv ≠ W64 0 ∧ sint.Z rv < log.length⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ ⌜id ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" resp ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" resp ↦□ e ∗
    apply.appliedHdr log (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp) ∗
    appliedWit ρ.rd log ∗ mvcc.certOk E.γ log ∗ lease.leaseGrantedAt E.γ.leases i id)

/-- **The apply thread's answer to a grant `rq'`, as `raftRequest` returns it** (the lease-grant
plan's D3, 2026-11-02; `appliedOk` says nothing of a grant: `dispatchAnswer`'s `LeaseGrant` arm is
`True`): the request's grant `g`, the response a `*LeaseGrantResponse` `r` with `g`'s id, its
`TTL` and `Error` read-only, its
header's id fields owned at the log `log` the entry met (`apply.appliedHdr`) and its revision a
revision of `log` (not `0`), and the lease granted at an index of the lessor's history. The
apply's `grantAnswerIs` without its error case (`raftRequest` returns the result's error). -/
def grantReplyOk (E : apply.AEnv GF) (rq' : apply.IRRModel) (log : mvcc.Log) (resp : GoInterface) :
    IProp GF :=
  iprop(∃ (g : apply.LeaseGrantModel) (r h : Loc) (rv : w64) (i : Nat),
    ⌜rq'.leaseGrant = some g ∧
      resp = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseGrantResponse.ty) #r ∧
      r ≠ null⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" r ↦□ g.id ∗ ⌜g.id ≠ W64 0⌝ ∗
    (∃ (ttl : w64) (e : GoString),
      structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" r ↦□ ttl ∗
      structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" r ↦□ e) ∗
    apply.appliedHdr log (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" r) ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" r ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗
    ⌜rv ≠ W64 0 ∧ sint.Z rv < log.length⌝ ∗
    lease.leaseGrantedAt E.γ.leases i g.id)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.raftRequest(ctx, r)` for a lease grant** (the lease-grant plan's D3, 2026-11-02): as
`raftRequest.specOff` (auth off), in a cluster that grants leases (`srvGrantsLeases`), for a
request of the grant's kind (`apply.grantKindOk`: `{LeaseGrant: r}`, its id not `0`), without a
proposal premise (`reqPropOk`'s ghost update: a grant's is `True`, `reqPropOkWG`). On success the
apply thread's grant answer (`grantReplyOk`) at the log `lb` the entry met, a witness the request
was applied there (`appliedWit`), and `lb` certified (`mvcc.certOk`: a grant leaves the KV log as
it found it). Its proof (`EtcdServer.raftRequest.wp_grant`) is open: Draft. -/
abbrev EtcdServer.raftRequest.specGrant : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel) (F : mvcc.Log),
  rq.id = W64 0 → apply.irrDepthOk rq → srvGrantsLeases E ρ → apply.grantKindOk rq →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (lb : mvcc.Log),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ grantReplyOk E rq' lb resp ∗
          appliedWit ρ.rd lb ∗ mvcc.certOk E.γ lb) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ rq))) }}

end spec

end EtcdGrove
end Perennial
