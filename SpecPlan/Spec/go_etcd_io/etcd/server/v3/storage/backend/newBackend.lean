/-
`newBackend(bcfg)` (`backend.go:199-261`): translated; internal (`New`'s body, returning the
`*backend`). Proof sketch: `New.spec`'s. Changes: as `New` (repair3-boot: the file through `beOpenUpd`). Margin: as `New`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal
public import SpecPlan.Spec.go_uber_org.zap.Api
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

/-- **`newBackend(cfg)`**: `New`'s backend, as a `*backend`. -/
def newBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig) (o : Option Image) (Bs : BktInfo → Prop) (Fh : Fp)
    (Pk K R : BeNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk ∗ threadTok ∗ ⌜dbOpenOk cfg ∧ cfg.Mlock' = false ∧ bktsOk Bs⌝ ∗
      (⌜cfg.NonBlockingDefrag' = false⌝ ∨ safeRegOk) ∗
      (⌜cfg.Logger' = null⌝ ∨ Zap.isLogger cfg.Logger') ∗ beOpenUpd cfg.Path' o cfg.UnsafeNoFsync' R ∗
      (∀ γ : BeNames, R γ -∗ beNew γ (o.getD Image.empty) ={⊤}=∗
        Pk γ ∗ hookOk γ cfg.Hooks' Fh (Pk γ) ∗ commitOk γ (Pk γ) ∗ K γ) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.newBackend)) (Val #cfg))
  {{ (b : Loc), RET #b; ∃ γ : BeNames, isBackend γ b cfg.Path' (Pk γ) ∗ K γ ∗ beHookFp γ Fh ∗
      (□ ∀ bi, ⌜Bs bi⌝ -∗ beBkt γ bi) ∗ beDurInv γ cfg.Path' ∗
      (if cfg.UnsafeNoFsync' then iprop(True) else beSynced γ) }}

end spec

end Backend
end EtcdGrove
end Perennial
