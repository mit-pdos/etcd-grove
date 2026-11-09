/-
`newBucketKey(main, sub, isTombstone)` (`revision.go:69`): the struct. Internal (`delete`,
`RevToBytes`). **Changes**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

/-- `newBucketKey(main, sub, tomb)`. -/
def newBucketKey.spec : Prop :=
  ∀ (main sub : w64) (tomb : Bool),
  {{ pkgInit }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newBucketKey)) (Val #main))
      (Val #sub)) (Val #tomb))
  {{ RET #({ Revision' := { Main' := main, Sub' := sub }, tombstone' := tomb } : BucketKey); True }}

end spec
end Mvcc
end EtcdGrove
end Perennial
