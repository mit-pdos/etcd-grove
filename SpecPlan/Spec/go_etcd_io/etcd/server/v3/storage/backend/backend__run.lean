/-
`b.run()` (`backend.go:462-476`): translated; internal (the commit goroutine). Each tick, a commit
if anything is pending (`safePending`, `Commit`: the hooks and the client's commit step); on
`stopc`, `CommitAndStop` and exit. Changes: over `beRun`. Margin: the timer.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`b.run()`**: commits until stopped; then the final commit, no write transaction left. -/
def backend.run.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beRun γ }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"run")) (Val #()))
  {{ RET #(); btStopped γ }}

end spec

end Backend
end EtcdGrove
end Perennial
