/-
`clientv3.getPrefix` (`client/v3/op.go`).

Users: `WithPrefix`, `GetPrefixRangeEnd`, `Cmp.WithPrefix`.

Proof sketch: a copy of the key, the loop from the last byte; `noPrefixEnd` (`init.spec`) when every byte is `0xff`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/getPrefix.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `getPrefix(key)`: the prefix's range end, read-only (a fresh slice, or the package's
`noPrefixEnd`). -/
def getPrefix.spec : Prop :=
  ∀ (key : GoSlice) (k : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ key ↦*{dq} k }}
    (App (Val (@! go_etcd_io.etcd.client.v3.getPrefix)) (Val #key))
  {{ (s : GoSlice), RET #s; key ↦*{dq} k ∗ s ↦*□ prefixEnd k }}

end spec

end ClientV3
end EtcdGrove
end Perennial
