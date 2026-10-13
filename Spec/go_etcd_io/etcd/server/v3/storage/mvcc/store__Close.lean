/-
`store.Close` (`kvstore.go`): the trust boundary (untranslated). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Close()` of the store, with the right to close it once (`storeCloser`: its `stopc` field;
`Close` closes `s.stopc` and stops the store's scheduler, a second call would close `stopc` again,
a panic): returns `nil`. -/
abbrev mvcc.store.Close.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeCloser s }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Close")) (Val #()))
  {{ RET #(GoInterface.nil); True }}

end spec

end EtcdGrove
end Perennial
