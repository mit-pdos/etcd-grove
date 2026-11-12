/-
`b.unsafeBegin(write)` (`backend.go:1065-1073`): translated; internal. bbolt's `Begin(write)` (4c);
an error is `lg.Fatal`. Changes: over `btPhys`; verify-round (A11-completeness F4): both modes, as
`begin`. Margin: as `begin`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal
public import Perennial.ProgramLogic.Bounds

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

/-- **`b.unsafeBegin(write)`**: as `begin`, without the atomics. -/
def backend.unsafeBegin.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (I : Image) (d : Nat) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ btHeld γ ∗
      (if w then btStopped γ ∗ beCommitted γ I else rtHeld γ ∗ btPhys γ I 0 d ∗ threadTok) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"unsafeBegin")) (Val #w))
  {{ (tx : Loc), RET #tx; btHeld γ ∗
      (if w then btPhys γ I 0 d else rtHeld γ ∗ btPhys γ I 0 d ∗ rtNew γ tx I) }}

end spec

end Backend
end EtcdGrove
end Perennial
