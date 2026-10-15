/-
`writeView.DeleteRange` (kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `wv.DeleteRange(key, end)`: a write transaction deleting the range, committed if it
deleted something: the keys deleted (`delKeys` of the committed log `ilog` the transaction
found) and the revision; the range's keys fit a revision (trivially, for one key). Under the
batch lock, by the critical-section contract (`csContract`). -/
abbrev mvcc.writeView.DeleteRange.spec : Prop :=
  ∀ (wv s : Loc) (γ : mvcc.StoreNames) (P Pre Q Post : IProp GF) (f : val)
    (key endk : GoSlice) (k e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWriteView wv s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ mvcc.storeWT γ ∗
      mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post ∗ key ↦*□ k ∗
      endk ↦*□ e ∗
      ⌜∀ ilog : mvcc.Log, (mvcc.delKeys ilog [] (decide (endk = slice.nil)) k e).length < mvcc.putMax γ⌝ }}
    (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"DeleteRange")) (Val #key))
      (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev); mvcc.storeReader s γ ∗ Post ∗
      ∃ ilog : mvcc.Log,
        mvcc.idxCert γ.idx (mvcc.commitLog ilog
          ((mvcc.delKeys ilog [] (decide (endk = slice.nil)) k e).map .del)) ∗
        ⌜n = W64 ((mvcc.delKeys ilog [] (decide (endk = slice.nil)) k e).length : Int) ∧
          rev = W64 ((mvcc.writeRev ilog
            ((mvcc.delKeys ilog [] (decide (endk = slice.nil)) k e).map .del) : Nat) : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
