/-
`txn.WarnOfExpensiveReadOnlyRangeRequest` (`util.go`, translated: unit P4, 2026-10-14; it was a
trust-boundary axiom, "it returns" with no premise, false of the code: unit P1). Lean-first (no
Rocq counterpart); the request path (`notes/decisions.md`, "The request path").

When the range took longer than `d`, it formats the response (unless nil: its `Kvs`' length and
`proto.Size`) and warns through `lg` (`warnOfExpensiveGenericRequest`: `lg.Warn` with the
request's `String()`, then `slowApplies.Inc()`). So: a logger, a request whose `String()` returns
(`stringerOk`), and a nil response or its `Kvs` (read-only) and `proto.Size` of it (`sizeOk`,
lent `P`: the server's `Range` lends its header's id fields, `rangeHdr`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `WarnOfExpensiveReadOnlyRangeRequest(lg, d, now, req, resp, err)`, with a logger, a request
whose `String()` returns, and a nil response or one whose `Kvs` it can read and `proto.Size` of
which returns lent `P`: it returns, `P` given back. -/
abbrev txn.WarnOfExpensiveReadOnlyRangeRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (req : GoInterface) (resp : Loc)
    (err : GoInterface) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜lg ≠ null⌝ ∗
      txn.stringerOk req ∗ P ∗
      (⌜resp = null⌝ ∨
        (∃ sl : GoSlice, structFieldRef etcdserverpb.RangeResponse go!"Kvs" resp ↦□ sl) ∗
        txn.sizeOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeResponse.ty) #resp) P) }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyRangeRequest)) (Val #lg)) (Val #d))
      (Val #now)) (Val #req)) (Val #resp)) (Val #err))
  {{ RET #(); P }}

end spec

end EtcdGrove
end Perennial
