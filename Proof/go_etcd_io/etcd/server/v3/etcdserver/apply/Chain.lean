/-
The applier chain (`server/v3/etcdserver/apply`): its shape, what a request's run through it
can come to, and the predicate of an `applierV3` value. Lean-first (no Rocq counterpart); plan:
`notes/decisions.md`, "The server's apply". Unit 0's skeleton: the chain and the outcome
relation are in place; the layers' method triples in `applierSpec` are unit 1's (they depend on
the hook threading of the txn package's write path, unit A).

**The chain** (`Chain`): `newApplierV3` builds `auth (quota backend)` (`baseChain`);
`uberApplier.restoreAlarms` wraps it in `capped` (a `NOSPACE` alarm) and then `corrupt` (a
`CORRUPT` alarm) (`alarmChain`). Each wrapper embeds the next `applierV3` (an interface: its
methods are promoted), overriding some methods.

**The outcome** (`Outcome`, `chainStep B c rq log o`): what a request `rq` dispatched through `c`
at the log `log` comes to, by recursion on `c`, over the backend's relation `B` (the txn
package's results for a KV request, unit 1): `corrupt` rejects the KV requests, compactions and
lease grants and revocations (`ErrCorrupt`); `capped` rejects puts and lease grants, and
transactions that cost (`ErrNoSpace`; the cost is the quota's, opaque: either); `auth` may
reject what it checks (an auth error, before any write); `quota` passes and may turn the
backend's success into `ErrNoSpace` after the write (the write committed: `quotaApplierV3.Put`
applies first, then reports). Compaction is out of the model (`notes/decisions.md`): no
`dispatch` premise lets it through, so `B` need not say anything of it.

**An applier value** (`applierSpec c a`): `a` is the `applierV3` interface value of the chain
`c`'s outer layer: its struct and its embedded inner applier, recursively; unit 1 adds each
layer's method triples over its inner's (the inner is a dynamic interface call, so its triples
live in the predicate, as `batchTxSpec`'s do), and the constructors' specs package them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply

/-! ## The chain, purely -/

/-- The layers of an applier chain, outermost first. -/
inductive Chain where
  | backend
  | auth (c : Chain)
  | quota (c : Chain)
  | capped (c : Chain)
  | corrupt (c : Chain)
  deriving DecidableEq

/-- `newApplierV3`'s chain: `authApplierV3` over `quotaApplierV3` over `applierV3backend`. -/
def baseChain : Chain := .auth (.quota .backend)

/-- `restoreAlarms`' chain: the base chain, `capped` if a `NOSPACE` alarm is set, then `corrupt`
if a `CORRUPT` alarm is. -/
def alarmChain (noSpace corrupt : Bool) : Chain :=
  let c := if noSpace then Chain.capped baseChain else baseChain
  if corrupt then .corrupt c else c

/-- An error a layer rejects a request with, before any write. -/
inductive RejectKind where
  /-- `ErrCorrupt` (the corrupt applier). -/
  | corrupt
  /-- `ErrNoSpace` (the capped applier). -/
  | noSpace
  /-- the auth store's error (a permission check failed). -/
  | auth
  /-- the backend's own error before a write (the txn package's checks, the lessor's, ...). -/
  | backend
  deriving DecidableEq

/-- **What a request dispatched through a chain comes to** at the log `log`. -/
inductive Outcome where
  /-- An error before any write: nothing written, the log unchanged. -/
  | rejected (e : RejectKind)
  /-- The backend ran: the log after it (`log'`, the txn package's commit); `noSpace`: the quota
  reports `ErrNoSpace` after the write. -/
  | applied (log' : mvcc.Log) (noSpace : Bool)

/-- The requests the corrupt applier rejects (`corrupt.go`). -/
def corruptRejects : ReqKind → Bool
  | .range | .put | .deleteRange | .txn | .compaction | .leaseGrant | .leaseRevoke => true
  | _ => false

/-- The requests the capped applier always rejects (`capped.go`; a transaction only if it
costs). -/
def cappedRejects : ReqKind → Bool
  | .put | .leaseGrant => true
  | _ => false

/-- The requests the auth applier checks in its methods (`auth.go`; the admin ones are checked
in its `Apply`, `needAdminPermission`). -/
def authChecks : ReqKind → Bool
  | .range | .put | .deleteRange | .txn | .leaseRevoke | .authUserGet | .authRoleGet => true
  | _ => false

/-- The requests the quota applier checks (`quota.go`). -/
def quotaChecks : ReqKind → Bool
  | .put | .txn | .leaseGrant => true
  | _ => false

/-- **The outcome relation** of the chain `c` on `rq` at `log`, over the backend's `B`. -/
def chainStep (B : IRRModel → mvcc.Log → Outcome → Prop) :
    Chain → IRRModel → mvcc.Log → Outcome → Prop
  | .backend, rq, log, o => B rq log o
  | .corrupt c, rq, log, o =>
      if corruptRejects (dispatchKind rq) then o = .rejected .corrupt
      else chainStep B c rq log o
  | .capped c, rq, log, o =>
      if cappedRejects (dispatchKind rq) then o = .rejected .noSpace
      else if dispatchKind rq = .txn then o = .rejected .noSpace ∨ chainStep B c rq log o
      else chainStep B c rq log o
  | .auth c, rq, log, o =>
      if authChecks (dispatchKind rq) ∨ needAdminPermission rq = true then
        o = .rejected .auth ∨ chainStep B c rq log o
      else chainStep B c rq log o
  | .quota c, rq, log, o =>
      if quotaChecks (dispatchKind rq) then
        ∃ o', chainStep B c rq log o' ∧
          (o = o' ∨ ∃ log', o' = .applied log' false ∧ o = .applied log' true)
      else chainStep B c rq log o

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## An applier value -/

/-- **The `applierV3` value `a` of the chain `c`** (unit 0's skeleton: the layers' structs and
their embedded inner appliers; unit 1 adds each layer's method triples over its inner's, and the
backend's over the contracts of `Contracts.lean`). -/
def applierSpec : Chain → GoInterface → IProp GF
  | .backend, a =>
      iprop(∃ p : Loc, ⌜a = interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p⌝)
  | .auth c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p⌝ ∗
        structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ∗ applierSpec c inner)
  | .quota c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p⌝ ∗
        structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ∗ applierSpec c inner)
  | .capped c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p⌝ ∗
        structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ∗ applierSpec c inner)
  | .corrupt c, a =>
      iprop(∃ (p : Loc) (inner : GoInterface),
        ⌜a = interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p⌝ ∗
        structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ∗ applierSpec c inner)

instance applierSpec_persistent (c : Chain) (a : GoInterface) :
    Persistent (applierSpec (GF := GF) c a) := by
  induction c generalizing a <;> unfold applierSpec <;> infer_instance

end defs

end apply
end EtcdGrove
end Perennial
