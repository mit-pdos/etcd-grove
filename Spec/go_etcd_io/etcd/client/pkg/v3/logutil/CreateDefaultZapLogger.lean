/-
`logutil.CreateDefaultZapLogger` (`client/pkg/v3/logutil/zap.go`).

Users: `clientv3.newClient` (no logger configured), the server's defaults.

Proof sketch: `DefaultZapLoggerConfig` with the level (zap's `NewAtomicLevelAt`), `Config.Build()`
(zap's boundary: W0's `Zap` API, `isLogger`, or an error).

Changes: new (no old spec).

Margin: none.
-/
module

public import Spec.go_uber_org.zap.Api
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.logutil
public import Spec.PkgInit.go_etcd_io.etcd.client.pkg.v3.logutil

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Logutil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `CreateDefaultZapLogger(level)`: a logger, or an error. -/
def CreateDefaultZapLogger.spec : Prop :=
  ∀ (lvl : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.logutil }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.logutil.CreateDefaultZapLogger)) (Val #lvl))
  {{ (lg : Loc) (err : GoInterface), RET (PairV #lg #err);
      (⌜err = GoInterface.nil⌝ ∗ Zap.isLogger lg) ∨ ⌜lg = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end Logutil
end EtcdGrove
end Perennial
