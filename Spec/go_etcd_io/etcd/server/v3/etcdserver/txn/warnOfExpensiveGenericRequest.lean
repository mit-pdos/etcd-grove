/-
`txn.warnOfExpensiveGenericRequest` (`util.go`: the warning of a slow request, then
`slowApplies.Inc()`). Lean-first (no Rocq counterpart); unit P4 (2026-10-14).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- `warnOfExpensiveGenericRequest(lg, d, now, req, prefix, resp, err)` with a logger (`lg.Warn`)
and a request whose `String()` returns (`stringerOk`): it returns. -/
abbrev txn.warnOfExpensiveGenericRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (req : GoInterface) (pfx resp : GoString)
    (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜lg ≠ null⌝ ∗
      txn.stringerOk req }}
    (App (App (App (App (App (App (App
      (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.warnOfExpensiveGenericRequest)) (Val #lg))
      (Val #d)) (Val #now)) (Val #req)) (Val #pfx)) (Val #resp)) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
