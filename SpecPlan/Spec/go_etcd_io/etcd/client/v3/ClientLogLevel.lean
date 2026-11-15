/-
`clientv3.ClientLogLevel` (`client/v3/logger.go`).

Users: `newClient` (the default logger's level).

Proof sketch: reads `ETCD_CLIENT_DEBUG` (`os.Getenv`), `zapcore.Level.Set` (zap's boundary).

Changes: new (no old spec).

Margin: the level is not described.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `ClientLogLevel()`: some level. -/
def ClientLogLevel.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.ClientLogLevel)) (Val #()))
  {{ (l : w8), RET #l; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
