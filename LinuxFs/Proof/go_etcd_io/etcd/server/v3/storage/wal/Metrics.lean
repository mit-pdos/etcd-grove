/-
**The WAL's prometheus metrics** (metrics.go, names-only: `walFsyncSec`, `walWriteSec`
histograms and the `walWriteBytes` gauge; WAL leaf specs, 2026-11-13), as the main tree's backend
and mvcc treat theirs (`Proof/go_etcd_io/etcd/server/v3/storage/{backend,mvcc}/Base.lean`):
`Observe(x)` and `Add(x)` return and do nothing the model sees. `wal.metricsInit` is the
package fact for them, to be given by the WAL package's `Init.lean` (`etc/gen-init.py`, the part's
`LFS_PKGS` and `SPECIAL`) from the trust-boundary axioms on their untranslated initializers
(`<X>_init`, as the backend's `rebalanceSec_init`). The calls: `walFsyncSec.Observe` (wal.go:249,
:943, :989, repair.go:96), `walWriteSec.Observe` and `walWriteBytes.Add` (encoder.go:130, :137,
:138). Lean-first.
-/
module

public import Perennial.Proof.time
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A prometheus `Histogram`'s `Observe(x)` returns (metrics have no effect the model sees). -/
def wal.histSpec (h : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
    {{ RET #(); True }}))

instance wal.histSpec_persistent (h : GoInterfaceOk) : Persistent (wal.histSpec (GF := GF) h) := by
  unfold wal.histSpec; infer_instance

/-- A prometheus `Gauge`'s `Add(x)` returns (any `x`: a gauge may go up or down). -/
def wal.gaugeAddSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Add" g.v)) (Val #x))
    {{ RET #(); True }}))

instance wal.gaugeAddSpec_persistent (g : GoInterfaceOk) :
    Persistent (wal.gaugeAddSpec (GF := GF) g) := by
  unfold wal.gaugeAddSpec; infer_instance

/-- **The WAL's metrics, as its package fact** (persistent): each variable holds for good a fixed
interface value whose method returns. -/
def wal.metricsInit : IProp GF :=
  iprop((∃ h : GoInterfaceOk,
      globalAddr _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.walFsyncSec ↦□
        GoInterface.ok h ∗ wal.histSpec h) ∗
    (∃ h : GoInterfaceOk,
      globalAddr _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.walWriteSec ↦□
        GoInterface.ok h ∗ wal.histSpec h) ∗
    (∃ g : GoInterfaceOk,
      globalAddr _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.walWriteBytes ↦□
        GoInterface.ok g ∗ wal.gaugeAddSpec g))

instance wal.metricsInit_persistent : Persistent (wal.metricsInit (GF := GF)) := by
  unfold wal.metricsInit; infer_instance

end defs

end EtcdGrove
end Perennial
