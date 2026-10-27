/-
`txn.WarnOfFailedRequest`: the trust boundary (the txn package's `util.go` is names-only (`isNil` uses reflect)). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `WarnOfFailedRequest(lg, now, req, resp, err)` logs the failure: it returns. The logger and
the stringer as `WarnOfExpensiveRequest`'s (audit B4b, 2026-10-18). -/
abbrev txn.WarnOfFailedRequest.spec : Prop :=
  ∀ (lg : Loc) (now : time.Time) (req resp err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜lg ≠ null⌝ ∗
      (∃ (sp p : Loc), ⌜req = interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.api.v3.etcdserverpb.InternalRaftStringer.ty) #sp ∧ p ≠ null⌝ ∗
        sp ↦ (go_etcd_io.etcd.api.v3.etcdserverpb.InternalRaftStringer.mk p)) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfFailedRequest)) (Val #lg)) (Val #now))
      (Val #req)) (Val #resp)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
