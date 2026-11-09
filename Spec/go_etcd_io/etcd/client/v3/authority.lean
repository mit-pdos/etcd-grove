/-
`clientv3.authority` (`client/v3/client.go`).

Users: `dial` (the target string).

Proof sketch: `strings.SplitN`, `strings.HasPrefix`, slicing past a prefix it checked.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/authority.lean`.

Margin: the string is not described (only `dial`'s target uses it).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `authority(ep)`: no panic. -/
def authority.spec : Prop :=
  ∀ (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.authority)) (Val #ep))
  {{ (s : GoString), RET #s; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
