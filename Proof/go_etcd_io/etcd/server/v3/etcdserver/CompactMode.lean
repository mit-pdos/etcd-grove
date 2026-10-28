/-
**The server's compaction mode** (M2, `notes/m2-plan.md`, phase 1, S2-S3; 2026-10-28): the
statements of a server whose auto-compactor is on (`NewServer.specCompact`), beside the compaction-
off ones, which stay as they are (a variant per statement, as the auth mode's `specOn`, until the
proofs exist: an unproved case of one statement would reach every result over it).

* `compactPropOk`: a compaction request as the server proposes it (S2: `reqPropOk`'s compaction
  form; no permit, C3 being deferred, and a latest read is never compacted at any revision).
* `irrNoDelPut`: a request whose write deletes no key it puts again in its revision (phase 0's
  decision 3, option (a) of S2: the admitted writes, in compaction mode only;
  `issues/etcd-compaction-delete-then-put.md`).
* `reqPropOkC`: what the compaction mode admits: a request `reqPropOk` admits that deletes no key it
  puts again, or a compaction.
* `apply.dispatchOkC`: `dispatchOk` without the compaction conjunct.
* `compactResultIs`: the apply thread's result of a compaction (`applierV3backend.Compaction`
  through the uber-applier): the response, or the error the request path reports.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A compaction request**, as `EtcdServer.Compact` proposes it (`&pb.InternalRaftRequest{
Compaction: r}`): of the kind `compaction`, at some revision. -/
def compactPropOk (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq = .compaction ∧ ∃ r : w64, rq.compaction = some r

/-- **A request that deletes no key it puts again** in the revision it makes (S2, option (a)):
whatever the chain, a dispatch that appends a revision appends one with `mvcc.NoDelPutAt`, so a
later compaction at that revision keeps the key's live value
(`issues/etcd-compaction-delete-then-put.md`). -/
def irrNoDelPut (rq : apply.IRRModel) : Prop :=
  ∀ (c : apply.Chain) (log : mvcc.Log) (o : apply.Outcome),
    apply.dispatchStep c rq true log o → (o.logAfter log).length = log.length + 1 →
      mvcc.NoDelPutAt (o.logAfter log) log.length

/-- **The premise on a request's kind in compaction mode**: `dispatchOk` without its compaction
conjunct (S2). -/
def apply.dispatchOkC (on : Bool) (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq ≠ .none ∧ (apply.dispatchKind rq = .authEnable → on = true)

/-- `dispatchOk` gives `dispatchOkC`. -/
theorem apply.dispatchOkC_of (on : Bool) (rq : apply.IRRModel) (h : apply.dispatchOk on rq) :
    apply.dispatchOkC on rq := ⟨h.2.1, h.2.2⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the compaction mode admits** (S2, `reqPropOk`'s compaction form): a request
`reqPropOk` admits whose write deletes no key it puts again, or a compaction (its result
predicate trivial). -/
def reqPropOkC (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    IProp GF :=
  iprop((reqPropOk γk rq Qr ∗ ⌜irrNoDelPut rq⌝) ∨
    ⌜compactPropOk rq ∧ Qr = fun _ => iprop(True)⌝)

/-- **The result of a compaction** (S2-S3): the apply thread's `*apply.Result`, read-only, with
the compaction's response (`*pb.CompactionResponse`, its header if any, owned: `Compact` writes
the revision into it) or the error the request path reports (`applyErrIs`: the store's
`ErrCompacted` or `ErrFutureRev`). -/
def compactResultIs (res : Loc) : IProp GF :=
  iprop(⌜res ≠ null⌝ ∗ ∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, res ↦□ v ∗
    ((⌜v.Err' = GoInterface.nil⌝ ∗ ∃ rp : Loc,
        ⌜v.Resp' = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty) #rp⌝ ∗
        (⌜rp = null⌝ ∨ ∃ cv : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse, rp ↦ cv ∗
          (⌜cv.Header' = null⌝ ∨ ∃ hv : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader, cv.Header' ↦ hv))) ∨
      (⌜v.Err' ≠ GoInterface.nil⌝ ∗ applyErrIs v.Err')))

end defs

end EtcdGrove
end Perennial
