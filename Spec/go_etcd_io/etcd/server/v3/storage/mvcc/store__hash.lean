/-
`store.hash` (`kvstore.go`; `HashStorage.Hash`, the `Maintenance.Hash` RPC's), as
etcd-io/etcd#22609 changes it (branch `pr-verify/etcd-22609`). Lean-first (no Rocq
counterpart); see `InvStore.lean`.
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

/-- `s.hash()`: commits the backend (`ForceCommit`, for a write session's token `storeWT`, which
it spends), hashes it (`b.Hash`, whose contract is the premise `storeHashOk`), and returns that
hash, an error, and the last revision of a committed log read under `s.revMu`, which extends
the caller's certificate `log₀` (so it is at least the caller's revision). The hash is
unconstrained (the backend's `Hash` is the trust boundary), and so is its relation to the
revision (the code's TODO: the two are read at different times). A reader's tokens
(`storeReaderC`: slots of `s.mu` and `s.revMu`, the backend's reader token) are given back. -/
abbrev mvcc.store.hash.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeHashOk s ∗ mvcc.storeReaderC s γ ∗ mvcc.storeWT γ ∗
      mvcc.idxCert γ.idx log₀ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"hash")) (Val #()))
  {{ (h : w32) (rev : w64) (err : GoInterface), RET (PairV (PairV #h #rev) #err);
      mvcc.storeReaderC s γ ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
