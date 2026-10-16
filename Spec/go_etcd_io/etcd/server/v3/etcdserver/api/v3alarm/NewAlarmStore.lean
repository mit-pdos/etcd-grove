/-
`v3alarm.NewAlarmStore(lg, be)` (`alarms.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
Pending (`?` in `etc/link-lean-first-server.txt`): a hypothesis of `NewServer`'s linked result
until unit N1 settles it (then an axiom at the trust boundary).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `NewAlarmStore(lg, be)` on a fresh backend: an alarm store (its lock, `isAlarmStore`; the apply
contract at any batch-lock invariant and hook), or an error (the backend's). -/
abbrev v3alarm.NewAlarmStore.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm ∗
      ⌜lg ≠ null⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore)) (Val #lg))
      (Val #be))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil ∧ a ≠ null⌝ ∗ isAlarmStore a ∗
        □ (∀ (P : IProp GF) (f : val), apply.isAlarmStore a P f) }}

end spec

end EtcdGrove
end Perennial
