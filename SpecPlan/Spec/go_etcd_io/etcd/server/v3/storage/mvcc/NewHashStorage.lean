/-
`NewHashStorage(lg, s)` (`hash.go:128`). Internal: `NewStore` (`s.hashes`). A fresh `*hashStorage`
over `s` (`hashStorageFresh`; `hashStorageFresh_share` makes its handle once the store's exists).

**Changes** from `specs-ref`'s file: `hashStorageFresh` in place of `hashStorageOk`; the logger
`Zap.isLogger`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

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

/-- `NewHashStorage(lg, s)`: a new hash storage over `s`, as a `HashStorage`. -/
def NewHashStorage.spec : Prop :=
  ∀ (lg s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ Zap.isLogger lg }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage)) (Val #lg)) (Val #s))
  {{ (hs : Loc), RET #(interface.mkOk (go.GoType.PointerType hashStorage.ty) #hs);
      hashStorageFresh hs s }}

end spec
end Mvcc
end EtcdGrove
end Perennial
