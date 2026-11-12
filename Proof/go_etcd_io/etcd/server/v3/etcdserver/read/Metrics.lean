/-
The read package's metrics registration (`read/metrics.go`; item 8, 2026-10-17): the names its
`init()` registers with prometheus's default registry, and the rights its initializer takes
(`readRegPerm`). `notes/decisions.md`, "D16: prometheus's default registry".
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

/-- **The read package's registration rights**: its initializer's `init()` registers its two
counters (`prometheus.MustRegister(slowReadIndex)`, `MustRegister(readIndexFailed)`), which needs
the right to register each name. A premise of its `wp_initialize'` and of its importers'. -/
def readRegPerm {GF : BundledGFunctors} : IProp GF :=
  iprop(prometheus.nameFree slowReadIndexName ∗ prometheus.nameFree readIndexFailedName)

end read
end EtcdGrove
end Perennial
