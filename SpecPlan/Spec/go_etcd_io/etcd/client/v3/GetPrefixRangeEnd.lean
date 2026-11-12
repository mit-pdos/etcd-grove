/-
`clientv3.GetPrefixRangeEnd` (`client/v3/op.go`).

Users: the cache (`cache/cache.go` `validateRange`), Kubernetes' store and watcher (`etcd3/store.go`, `etcd3/watcher.go`: the range end of a prefix).

Proof sketch: `getPrefix.spec` on a fresh copy of the string's bytes; the string of the result.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/GetPrefixRangeEnd.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `GetPrefixRangeEnd(prefix)`: the range end of every key with the prefix. -/
def GetPrefixRangeEnd.spec : Prop :=
  ∀ (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.GetPrefixRangeEnd)) (Val #pfx))
  {{ RET #(prefixEnd pfx); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
