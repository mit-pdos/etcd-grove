/-
`IsTombstone(b)` (`revision.go:124`): `isTombstone`. Exported; no caller in the verified code.
**Changes**: over `isTombBytes`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `IsTombstone(b)`. -/
def IsTombstone.spec : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ pkgInit ∗ s ↦*{dq} bs }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.IsTombstone)) (Val #s))
  {{ RET #(isTombBytes bs); s ↦*{dq} bs }}

end spec
end Mvcc
end EtcdGrove
end Perennial
