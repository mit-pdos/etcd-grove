/-
## `read.uint64ToBigEndianBytes(number)` (internal helper)

Users: `sendReadIndex`. Mirrors the code: `make([]byte, 8)`, `binary.BigEndian.PutUint64`.
Changes: unchanged in content. Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- A fresh 8-byte slice holding `n` big-endian. -/
def uint64ToBigEndianBytes.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.uint64ToBigEndianBytes)) (Val #n))
  {{ (sl : GoSlice), RET #sl; sl ↦* be64 n }}

end spec
end Read
end EtcdGrove
end Perennial
