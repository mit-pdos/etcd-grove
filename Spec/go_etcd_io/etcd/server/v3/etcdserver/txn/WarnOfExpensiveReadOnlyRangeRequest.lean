/-
`txn.WarnOfExpensiveReadOnlyRangeRequest`: the trust boundary (the txn package's `util.go` is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- `WarnOfExpensiveReadOnlyRangeRequest(lg, d, now, req, resp, err)` logs if the read took longer than `d`: it returns. -/
abbrev txn.WarnOfExpensiveReadOnlyRangeRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (req : GoInterface) (resp : Loc) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyRangeRequest)) (Val #lg)) (Val #d))
      (Val #now)) (Val #req)) (Val #resp)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
