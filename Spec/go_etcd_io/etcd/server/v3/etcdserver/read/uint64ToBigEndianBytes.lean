/-
`read.uint64ToBigEndianBytes(number)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Inv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.read

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `uint64ToBigEndianBytes(n)`: a new slice of the eight big-endian bytes of `n`. -/
abbrev read.uint64ToBigEndianBytes.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.uint64ToBigEndianBytes)) (Val #n))
  {{ (sl : GoSlice), RET #sl; sl ↦* beBytes n }}

end spec

end EtcdGrove
end Perennial
