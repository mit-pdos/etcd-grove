/-
## `(*readTx).RUnlock()` (`read_tx.go:132`): translated

**Users.** The `RLock` users. **Proof sketch.** `rt.mu.RUnlock()`: the reader slot back.
**Changes.** The slot back. **Margin.** None.
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

/-- **`rt.RUnlock()`**: the read ends; the reader slot back. -/
def readTx.RUnlock.spec : Prop :=
  ∀ (γ : BeNames) (F : Fp) (V : Image),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRd γ (rtLoc γ) F V ∗ beLive γ (rtLoc γ) 1 }}
    (App (Val ((rtLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); beRdToks γ 1 }}

end spec

end Backend
end EtcdGrove
end Perennial
