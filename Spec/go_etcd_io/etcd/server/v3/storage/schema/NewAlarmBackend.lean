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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewAlarmBackend(lg, be)` returns an `AlarmBackend` (an interface: a fresh `*alarmBackend`
wrapping `be`). (Unit N1, 2026-10-17: the result is the interface value Go returns, not the
pointer, as stated at N0.) -/
abbrev schema.NewAlarmBackend.spec : Prop :=
  ∀ (lg : Loc) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.NewAlarmBackend)) (Val #lg))
      (Val #be))
  {{ (ab : GoInterface), RET #ab; True }}

end spec

end EtcdGrove
end Perennial
