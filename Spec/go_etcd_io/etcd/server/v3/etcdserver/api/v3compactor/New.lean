/-
## `v3compactor.New(lg, mode, retention, rg, c)` (`compactor.go:59-77`): translated

**Users.** `NewServer` (`server.go:376`, at a non-zero retention, with the store and the server).
Snippet: `etcdserverboot/compactor.go`.

**Proof sketch.** A nil logger replaced; by mode, `newPeriodic` (the real clock: `clockOk`, the
`clockwork` boundary; its retention bound) or `newRevision`, or an error for another mode.

**Changes** (from `specs-ref`'s `New.lean`: `compactorOk` at C1's permit, `runPre`, `modePermit`):
the compactor's safety needs no permit in W0's model (`Api.lean`'s header).

**Margin.** None.
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

/-- **A compactor** in `mode` (`periodic` or `revision`), or an error for another mode. -/
def New.spec : Prop :=
  ∀ (R : IProp GF) (lg : Loc) (mode : GoString) (ret : time.Duration) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ revGetter rg ∗ compactable c R ∗
      ⌜mode = go!"periodic" → (10 ≤ sint.Z ret ∨ sint.Z ret ≤ -10)⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New)) (Val #lg)) (Val #mode)) (Val #ret)) (Val #rg)) (Val #c))
  {{ (cp err : GoInterface), RET (PairV #cp #err);
      (⌜err = GoInterface.nil⌝ ∗ isCompactor cp R) ∨
      ⌜err ≠ GoInterface.nil ∧ mode ≠ go!"periodic" ∧ mode ≠ go!"revision"⌝ }}

end spec

end V3compactor
end EtcdGrove
end Perennial
