/-
`hashStorage.Hash` (`hash.go`): `s.store.hash()`. Lean-first (no Rocq counterpart); for
etcd-io/etcd#22609 (branch `pr-verify/etcd-22609`).
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

/-- `hs.Hash()` of the hash storage of the store `s` (its `store` field, which `NewHashStorage`
sets): `store.hash`'s spec. -/
abbrev mvcc.hashStorage.Hash.spec : Prop :=
  ∀ (hs s : Loc) (γ : mvcc.StoreNames) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      structFieldRef hashStorage go!"store" hs ↦□ s ∗
      mvcc.isStore s γ ∗ mvcc.storeHashOk s ∗ mvcc.storeReaderC s γ ∗ mvcc.storeWT γ ∗
      mvcc.idxCert γ.idx log₀ }}
    (App (Val (hs @!! go.GoType.PointerType hashStorage.ty @!! go!"Hash")) (Val #()))
  {{ (h : w32) (rev : w64) (err : GoInterface), RET (PairV (PairV #h #rev) #err);
      mvcc.storeReaderC s γ ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
