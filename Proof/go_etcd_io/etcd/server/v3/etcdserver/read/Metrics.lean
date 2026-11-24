/-
The read package's metrics registration (`read/metrics.go`; item 8, 2026-10-17): the names its
`init()` registers with prometheus's default registry (until prom-registry, 2026-11-22, also the
rights its initializer took, `readRegPerm`, unused since mustreg). `notes/decisions.md`, "D16: prometheus's default registry".
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace read

open Iris Iris.BI

/-- `slowReadIndex`'s fully-qualified name (`etcd_server_slow_read_indexes_total`). -/
abbrev slowReadIndexName : GoString :=
  prometheus.fqName go!"etcd" go!"server" go!"slow_read_indexes_total"

/-- `readIndexFailed`'s fully-qualified name (`etcd_server_read_indexes_failed_total`). -/
abbrev readIndexFailedName : GoString :=
  prometheus.fqName go!"etcd" go!"server" go!"read_indexes_failed_total"

end read
end EtcdGrove
end Perennial
