/-
`sliceCapWithLimit[S](limit, s)` (`kvstore_txn.go:154`): `len(s)`, or `limit` when it is positive and
below it. Internal (`rangeKeys`). Mirrors its code.

**Changes** from `specs-ref`'s file: the result stated inline; no slice ownership (only its length is
read).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `len(s)` unless `0 < limit ≤ len(s)` (signed). -/
def sliceCapWithLimit.spec : Prop :=
  ∀ (S : go.GoType) (limit : w64) (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.mvcc.sliceCapWithLimit [S]))
      (Val #limit)) (Val #s))
  {{ RET #(if sint.Z limit ≤ 0 ∨ sint.Z s.len < sint.Z limit then s.len else limit); True }}

end spec
end Mvcc
end EtcdGrove
end Perennial
