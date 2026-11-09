/-
## `NewHooks(onPreCommitUnsafe)` (`hooks.go:34-36`): translated

**Users.** Tests and tools (`hooks_test.go`); the server uses its own `*BackendHooks` (2e).
**Proof sketch.** The struct `hooks{f}` as a `Hooks` value; its method calls `f(tx)`
(`hooks.OnPreCommitUnsafe.spec`), so the hooks' contract is `f`'s. **Changes.** From `specs-ref`'s:
over `hookOk`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

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

/-- **`NewHooks(f)`**: a `Hooks` value whose contract is `f`'s (`hookOk` at the struct as at `f`). -/
def NewHooks.spec : Prop :=
  ∀ (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.NewHooks)) (Val #f))
  {{ (h : GoInterface), RET #h; ⌜h ≠ interface.nil⌝ ∗
      □ ∀ (γ : BeNames) (Fh : Fp) (Pk : IProp GF),
        hookFnOk γ f Fh Pk -∗ hookOk γ h Fh Pk }}

end spec

end Backend
end EtcdGrove
end Perennial
