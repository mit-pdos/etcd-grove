/-
## `newRevision(lg, clock, h, rg, c)` (`revision.go`): translated

**Users.** `New`. **Proof sketch.** A struct literal, a cancellable context
.
**Changes**: from `specs-ref`'s `newRevision.lean`. **Margin.** None.
Changes: verify-round (A7 completeness F2): the compactor's handles carry the gate `R` of its `Compactable`
(`compactable c R`: `Compact` is safe once `□ R`, the server's start); `Run` takes `□ R`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Api
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3compactor

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

/-- **A revision compactor.** -/
def newRevision.spec : Prop :=
  ∀ (R : IProp GF) (lg : Loc) (clk : GoInterface) (h : w64) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ Zap.isLogger lg ∗ clockOk clk ∗ revGetter rg ∗ compactable c R ∗ ⌜True⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision)) (Val #lg)) (Val #clk)) (Val #h)) (Val #rg)) (Val #c))
  {{ (p : Loc), RET #p; isRevision p R }}

end spec

end V3compactor
end EtcdGrove
end Perennial
