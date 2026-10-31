/-
**LeaseRevoke through the apply chain: the Draft's statements** (`notes/lease-revoke-plan.md`,
D1-D6 revised by R1-R8). Imported by nothing but the stage's tests and probes; no `axiom`, no
`sorry`. At Prove the definitions replace their counterparts in `Chain.lean`/`Contracts.lean`
(`backendStep`'s case, `authMayReject`, `revokePre`, `revokeOutcomeIs`, `isApplyLessor`'s clause)
and the `Prop`s become theorems.

- `revokeStep`: `backendStep`'s `.leaseRevoke` case, exact (D1): the lease's keys deleted at one
  revision (`mvcc.leaseDels`, none for a lease with no key).
- `authMayRejectR`: a revocation is rejected by the auth layer only when it is on (R5).
- `rdAt`: the range deleter's owner with its contract at every name set of the store (R2).
- `revokeClause`: `isApplyLessor`'s `Revoke` clause (D3, R1, R2, R6), over the rest resource `RO`.
- `revokeRes`, `revokeResAfter`: what the method takes beside `mPre` and gives back (D4, R6).
- `revokePreR`, `revokeOutcomeIsR`: the method's precondition (R3: `putOk`, `rqOk` unchanged)
  and answer (R7).
- `chainRevokeStmt`: `chain_revoke` (D5).
- `deriveRevokeStmt`: the clause of the real lessor (D3's derivation).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestLease
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

namespace apply

/-- **The log after revoking `id`** (F7 of the second review): the lease's keys deleted at one
revision, none if it has none. -/
abbrev revokeLog (log : mvcc.Log) (id : w64) : mvcc.Log :=
  mvcc.commitLog log (mvcc.leaseDels (mvcc.stateAfter log) id)

/-- **The backend's revocation, exact** (D1): the keys the item map puts on the request's lease,
deleted at one revision (`mvcc.leaseDels`: none when the lease has no key, or is `0`, or is not
live, since every lease of the item map is live; then the log stays). The answer's error
(`revokeOutcomeIsR`) is the lessor's. -/
def revokeStep (rq : IRRModel) (log : mvcc.Log) (o : Outcome) : Prop :=
  ∃ id, rq.leaseRevoke = some id ∧
    o = .applied (revokeLog log id) false

/-- **The requests the auth layer may reject** (R5): with the mode on, any; off, an admin request
or one of a kind it does not check, other than a KV request and a revocation (`checkLeasePuts`
returns `nil` with auth disabled: `checkLeasePutsKeys`'s first test). -/
def authMayRejectR (on : Bool) (rq : IRRModel) : Prop :=
  on = true ∨ needAdminPermission rq = true ∨
    (dispatchKind rq ≠ .put ∧ dispatchKind rq ≠ .range ∧ dispatchKind rq ≠ .deleteRange ∧
      dispatchKind rq ≠ .txn ∧ dispatchKind rq ≠ .leaseRevoke)

/-- **The backend's relation with the exact revocation** (F2 of the second review): `backendStep`
but for a revocation, `revokeStep`; at Prove it is `backendStep`. -/
def backendStepR (rq : IRRModel) (log : mvcc.Log) (o : Outcome) : Prop :=
  if dispatchKind rq = .leaseRevoke then revokeStep rq log o else backendStep rq log o

/-- **The chain's relation with R5** (F2): `chainStep` with the auth layer's `authMayRejectR`; at
Prove it is `chainStep`. -/
def chainStepR (B : IRRModel → mvcc.Log → Outcome → Prop) :
    Chain → IRRModel → mvcc.Log → Outcome → Prop
  | .backend, rq, log, o => B rq log o
  | .corrupt c, rq, log, o =>
      if corruptRejects (dispatchKind rq) then o = .rejected .corrupt
      else chainStepR B c rq log o
  | .capped c, rq, log, o =>
      if cappedRejects (dispatchKind rq) then o = .rejected .noSpace
      else if dispatchKind rq = .txn then o = .rejected .noSpace ∨ chainStepR B c rq log o
      else chainStepR B c rq log o
  | .auth on c, rq, log, o =>
      if authChecks (dispatchKind rq) ∨ needAdminPermission rq = true then
        (authMayRejectR on rq ∧ o = .rejected .auth) ∨ chainStepR B c rq log o
      else chainStepR B c rq log o
  | .quota c, rq, log, o => chainStepR B c rq log o

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The lessor's range deleter, held** (R2, D4-3; not persistent): the owner's half of `le.rd`
(`lease.rdOwn`) at a deleter that, at every watchable store over the inner store `s` (whatever its
names: `kvWriter` hides them), is that store's `Write` (`mvcc.rdIs`). `lessor.Revoke` reads the
field by it and gives it back. Nothing gives it yet: `mvcc.New`/`newWatchableStore` give the
deleter's contract at their own names only (true at any: the stored closure calls `s.Write`, whose
spec holds at any names), and the snapshot's `Recover` replaces the deleter; both are L3c's. -/
def rdAt (γl : GName) (s : Loc) : IProp GF :=
  iprop(∃ rd : GoFunc, lease.rdOwn γl rd ∗
    □ ∀ (ws : Loc) (γw : mvcc.WsNames), mvcc.isWatchableStore ws s γw -∗ mvcc.rdIs rd ws s γw)

/-- **`isApplyLessor`'s `Revoke` clause** (D3) at the store `s` (names `γ`), the batch lock (`P`,
`f`) and the rest resource `RO`: by the lease owner at the live set `L`, the sole writer at `log`
(room for a revision), the range deleter held, the rest at `rs`, and the certificate of the
revocation's commit:
* `id` not live: an error (`ErrLeaseNotFound`), nothing changed, `Pre` back;
* `id` live: no error, the lease's keys deleted (`mvcc.leaseDels`), `Post`, the live set without
  `id`, its record deleted from the `lease` bucket (`restRevoke`).
The write token is spent in the second case even when there is no key (`lessor.Revoke` opens a
write transaction). -/
def revokeClause (le : GoInterfaceOk) (s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RO : RestM → IProp GF) : IProp GF :=
  iprop(□ (∀ (id : w64) (log : mvcc.Log) (L : List w64) (rs : RestM) (Pre Q Post : IProp GF),
    {{ mvcc.csContract P f Pre Q Post ∗ txn.kvWriter s γ log ∗ mvcc.storeReader s γ ∗
        mvcc.storeWT γ ∗ ⌜putOk log⌝ ∗
        lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
        lease.leaseRevokers γ.leases L ∗ txn.leasesKnown L (mvcc.stateAfter log) ∗
        rdAt γ.leases s ∗ RO rs ∗
        □ mvcc.certOkNext γ log (mvcc.leaseDels (mvcc.stateAfter log) id) }}
      (App (Val #(methods le.ty go!"Revoke" le.v)) (Val #id))
    {{ (err : GoInterface), RET #err; mvcc.storeReader s γ ∗ rdAt γ.leases s ∗ applyErrIs err ∗
        ((⌜id ∉ L ∧ mvcc.leaseDels (mvcc.stateAfter log) id = []⌝ ∗
            (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
              GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) ∗ Pre ∗ mvcc.storeWT γ ∗ txn.kvWriter s γ log ∗
            lease.leaseOwn γ.leases L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗
            lease.leaseRevokers γ.leases L ∗ txn.leasesKnown L (mvcc.stateAfter log) ∗ RO rs) ∨
         (⌜id ∈ L ∧ err = GoInterface.nil⌝ ∗ Post ∗
            txn.kvWriter s γ (revokeLog log id) ∗
            lease.leaseOwn γ.leases (L.filter (· != id)) (mvcc.leaseItemsOf (mvcc.stateAfter
              (revokeLog log id))) ∗
            lease.leaseRevokers γ.leases (L.filter (· != id)) ∗
            txn.leasesKnown (L.filter (· != id)) (mvcc.stateAfter
              (revokeLog log id)) ∗
            RO (restRevoke id rs))) }}))

/-- **The certificates of the chain's logs** (F2): `certPre` over `chainStepR backendStepR`. -/
def certPreR (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) : IProp GF :=
  iprop(□ ∀ oc : Outcome, ⌜chainStepR backendStepR c rq log oc⌝ -∗ mvcc.certOk E.γ (oc.logAfter log))

/-- **The lessor's error of a revocation** (F3): none, or `ErrLeaseNotFound` (what the gRPC layer
maps to its own code, L4). -/
def revokeErrIs (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨ ∃ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e ∗
      ⌜err = GoInterface.ok e⌝)

/-- **What a revocation takes beside the method's resources** (D4): the range deleter held and the
rest at `rs`. -/
def revokeRes (E : AEnv GF) (rs : RestM) : IProp GF :=
  iprop(rdAt E.γ.leases E.s ∗ E.RO rs)

/-- **What it gives back** (R6): the range deleter, the rest with the lease's record deleted when
the revocation succeeded (`err = nil`: the lease was live), else as it was. Which of "not live"
and "live with no key" the apply layer cannot tell (the same log): the server's model can (L3c). -/
def revokeResAfter (E : AEnv GF) (id : w64) (rs : RestM) (err : GoInterface) : IProp GF :=
  iprop(rdAt E.γ.leases E.s ∗ E.RO (if err = GoInterface.nil then restRevoke id rs else rs))

/-- **`LeaseRevoke(r)`'s precondition** (R3): the request's, room for a revision (`putOk`, in place
of `rqOk`, which keeps excluding the kind for `dispatch`), the certificate, the write token, the
method's resources and the revocation's. -/
def revokePreR (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (r : Loc) (rq : IRRModel) (id : w64)
    (log : mvcc.Log) (rs : RestM) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(⌜rq.leaseRevoke = some id ∧ dispatchKind rq = .leaseRevoke ∧ putOk log⌝ ∗
    certPreR E c rq log ∗ leaseRevokeIs r id ∗
    mvcc.storeWT E.γ ∗ mPre E c a info log Pre Q Post ∗ revokeRes E rs)

/-- **A revocation's answer** (R7, F3): rejected, no response and the layer's error; applied, a
response whose header is `newHeader`'s (not nil; its fields are the server's, `newHeader`'s spec
says no more), and the lessor's error (`revokeErrIs`). -/
def revokeOutcomeIsR (resp : Loc) (err : GoInterface) : Outcome → IProp GF
  | .rejected k => iprop(⌜resp = null⌝ ∗ rejErrIs (fun _ => iprop(False)) k err)
  | .applied _ _ => iprop(⌜resp ≠ null⌝ ∗ (∃ h : Loc,
      structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" resp ↦ h ∗ ⌜h ≠ null⌝) ∗
      applyErrIs err ∗ revokeErrIs err)

end defs

section stmts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`chain_revoke`** (D5): a revocation through the uber-applier's chain: an outcome of the chain
over the exact backend (`chainStepR backendStepR`: corrupt, or the auth layer's rejection, or the
backend's), its answer, the log it commits, the rest after it; an outcome that passed the auth
layer has the request's class and its lease's (`reqLeaseClass`'s `.leaseRevoke` case,
`leaseKeysClass`: in the mode `on`, the principal an admin or allowed to write every key the item
map put on the lease before the revocation, the keys it deletes). -/
def chainRevokeStmt (E : AEnv GF) (ns cr : Bool) (a : GoInterface) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
    □ (∀ (r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log) (rs : RestM) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      {{ revokePreR E (alarmChain E.authOn ns cr) (.ok ai) info r rq id log rs Pre Q Post }}
        (App (Val #(methods ai.ty go!"LeaseRevoke" ai.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          ∃ oc : Outcome, ⌜chainStepR backendStepR (alarmChain E.authOn ns cr) rq log oc⌝ ∗
            revokeOutcomeIsR resp err oc ∗ kvOwn E (oc.logAfter log) ∗
            chainRes (alarmChain E.authOn ns cr) (.ok ai) info ∗ (Post ∨ Pre) ∗
            revokeResAfter E id rs err ∗
            (∀ _ : authPassed oc, reqClass E.authMode info rq ∗
              reqLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq) }}))

/-- **The clause of the real lessor** (D3's derivation, beside `isApplyLessor_of_lessorInv`'s): the
lessor `lp` (its invariant), its backend's write right lent by the rest resource (`roLens`'s form:
the tracked buckets and the lessor's `le.b` half at the store's real backend; only the buckets
change, not `roLens`, which would let the members change too; a grant writes through `RW`, a
revocation through `RO`, the server's resource of the buckets at its model), the store watchable
(`kvWriter` then holds `watchWriter`'s parts) and its hook's facts. -/
def deriveRevokeStmt : Prop :=
  lease.lessor.Revoke.spec (GF := GF) (hG := hG) →
  ∀ (lp s : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RO : RestM → IProp GF),
    ⌜γ.watchQ = true⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      lease.lessorInv lp γ.leases ∗ mvcc.hookOk γ P f ∗
      □ (∀ rs : RestM, RO rs -∗ ∃ d : mvcc.KBReal, ⌜γ.kb = some d⌝ ∗
          mvcc.storeRb γ rs.bk ∗ lease.lessorBeOn lp d.be ∗
          (∀ bk, mvcc.storeRb γ bk ∗ lease.lessorBeOn lp d.be -∗ RO { rs with bk := bk })) ⊢
      revokeClause ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty, #lp⟩ s γ P f RO

end stmts

end apply
end EtcdGrove
end Perennial
