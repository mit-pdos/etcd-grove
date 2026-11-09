/-
`b.begin(write)` (`backend.go:1050-1063`): translated; internal. `unsafeBegin` under `mu.RLock`, the
size and open-transaction atomics stored. Changes: over `btPhys`. Margin: the atomics' values.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

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

/-- **`b.begin(write)`**: a bbolt transaction at the committed image (a write one under the batch
lock). -/
def backend.begin.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (d : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗ btStopped γ ∗ beCommitted γ I }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"begin")) (Val #true))
  {{ (tx : Loc), RET #tx; btHeld γ ∗ btPhys γ I 0 d }}

end spec

end Backend
end EtcdGrove
end Perennial
