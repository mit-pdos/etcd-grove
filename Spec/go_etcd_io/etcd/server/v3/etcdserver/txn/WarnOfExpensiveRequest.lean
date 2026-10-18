/-
`txn.WarnOfExpensiveRequest`: the trust boundary (the txn package's `util.go` is names-only (`isNil` uses reflect)). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `WarnOfExpensiveRequest(lg, d, now, req, resp, err)` logs if the request took longer than
`d`: it returns. The logger is not nil and `req` is the uber-applier's stringer, a fresh
`*pb.InternalRaftStringer` of a non-nil request (it calls `lg.Warn` and `req.String()`, which reads
`Request`'s fields: a nil logger, stringer or request panics; the premises since audit B4b,
2026-10-18). -/
abbrev txn.WarnOfExpensiveRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (req resp err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜lg ≠ null⌝ ∗
      (∃ (sp p : Loc), ⌜req = interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.api.v3.etcdserverpb.InternalRaftStringer.ty) #sp ∧ p ≠ null⌝ ∗
        sp ↦ (go_etcd_io.etcd.api.v3.etcdserverpb.InternalRaftStringer.mk p)) }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveRequest)) (Val #lg)) (Val #d))
      (Val #now)) (Val #req)) (Val #resp)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
