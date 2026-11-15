/- Lean-first (no Rocq counterpart).

`Run(cfg)` (`examples/mvccrand/mvccrand.go`): the tester (`runChecks`), then the lessor stopped
(`le.Stop()`) and the backend closed (`check(be.Close() == nil, …)`). **Every check passes**: it
returns the report. (2026-11-08, for the closed theorem.) The premises are `runChecks`'s, and
`dbCloseOk` (bbolt's `Close` does not fail for the environment's reasons, `DB.Close_kv`'s premise):
`backend.Close` returns an error only under `¬ dbCloseOk`, and the check panics on one.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.runChecks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (cfg : Config) [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)],
  0 ≤ sint.Z cfg.Ops' → sint.Z cfg.Ops' < 2 ^ 38 →
  0 ≤ sint.Z cfg.Readers' → sint.Z cfg.Readers' + 2 ≤ 2 ^ 28 →
  0 ≤ sint.Z cfg.Watchers' → sint.Z cfg.Watchers' < 2 ^ 32 →
  backend.dbOpenOk → backend.dbCloseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      backend.fileHolds cfg.Path' ∅ ∗
      threadTok ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.Run)) (Val #cfg))
  {{ (rep : Report), RET #rep; True }}

end spec

end mvccrand
end EtcdGrove
end Perennial
