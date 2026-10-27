/-
`newBoltLoggerZap` (`backend.go`): the trust boundary (names-only: its body is zap's
`Named("bbolt")`, `WithOptions(zap.AddCallerSkip(1))` and `Sugar()`, wrapped as a
`*zapBoltLogger`, a `bolt.Logger`). Go: on a non-nil logger it returns a logger whose methods log
through zap (`Fatal`/`Panic` stop the process or panic, as bbolt expects of its logger): what
`boltLogger` names, the logger bbolt's `Open` takes. Lean-first (no Rocq counterpart);
2026-10-17, branch `construct` (the backend's constructor).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `newBoltLoggerZap(bcfg)` (the configuration's logger not nil): a logger bbolt may call. -/
abbrev backend.newBoltLoggerZap.spec : Prop :=
  ∀ (cfg : BackendConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      ⌜cfg.Logger' ≠ Loc.null⌝ }}
    (App (Val (@! newBoltLoggerZap)) (Val #cfg))
  {{ (l : GoInterface), RET #l; boltLogger l }}

end spec

end EtcdGrove
end Perennial
