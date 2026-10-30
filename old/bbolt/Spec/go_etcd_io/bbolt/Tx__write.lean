module
public import Proof.go_etcd_io.bbolt.DBWrite
public import Proof.go_etcd_io.bbolt.WriteAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.write()` of the writer `txl`: its dirty pages (the page cache `T.pm`, their bytes
`T.bufs`; `dirtyOK`: slots no view sees, inside the file) are written to the file at their ids
through `db.ops.writeAt` (the file's `WriteAt`), in chunks of at most `MaxAllocSize - 1` bytes;
then the file is synced (`fdatasync`, unless `NoSync`), and the one-slot pages are zeroed and
put back in the page pool. The file `bs'` after it differs from the database's only in dirty
slots, so the database's facts are kept (`dbOK_dirty`); without an error every dirty page is
written. In either case the transaction's page cache is a new empty map (cleared before the
writes).

**Safety finding** (`σ.ps < 2 ^ 31`): a one-slot page goes back to the pool as
`UnsafeByteSlice(p, 0, 0, pageSize)`, which slices a `[MaxAllocSize]byte` array up to
`pageSize`: with a page size above `MaxAllocSize` (`0x7FFFFFFF`) it panics (the database's
facts only bound the page size by `2 ^ 32`). -/
abbrev Tx.write.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64) (σ : DBState)
    (T : WTx),
  dirtyOK σ T → T.t.db' = W.dbl → σ.ps < 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl txid σ ∗
      ownWriteTxG W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ (bs' : List w8) (pl : Loc) (st : TxStats),
      dbWR I γ W txl txid { σ with bs := bs' } ∗
      ownWriteTxG W txl ⟨{ T.t with pages' := pl, stats' := st }, T.mv, ∅, ∅, T.bs⟩ ∗ wView W ∗
      ⌜dirtyOnly T σ.ps σ.bs bs' ∧ (err = interface.nil → dirtyAll T σ.ps bs')⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
