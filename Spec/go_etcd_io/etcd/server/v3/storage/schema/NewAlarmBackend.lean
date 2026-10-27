/-
`schema.NewAlarmBackend(lg, be)` (`alarm.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

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

/-- `NewAlarmBackend(lg, be)` returns an `AlarmBackend`: a fresh `*alarmBackend` wrapping `be`
(its fields `lg`, `be`, persistent: no method writes them). (Unit N1, 2026-10-17: the result is the
interface value Go returns; N4c, 2026-10-17: the pointer and its fields named, from the body.) -/
abbrev schema.NewAlarmBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewAlarmBackend)) (Val #lg))
      (Val #be))
  {{ (ab : GoInterface), RET #ab; ∃ l : Loc,
      ⌜ab = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty) #l⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"lg" l ↦□ lg ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.alarmBackend go!"be" l ↦□ be }}

end spec

end EtcdGrove
end Perennial
