module
public import Proof.go_etcd_io.bbolt.WriteAlloc
public import Proof.go_etcd_io.bbolt.DBWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- The transaction with the dirty page `p` (id `id`, bytes `bs`) added. -/
def allocT (T : WTx) (st : go_etcd_io.bbolt.TxStats) (hwm id : w64) (p : Loc) (bs : List w8) :
    WTx :=
  ⟨{ T.t with stats' := st }, { T.mv with pgid' := hwm }, <[id := p]> T.pm, <[id := bs]> T.bufs,
    T.bs⟩

/-- What `tx.allocate(count)` did (the transaction `T`, possibly dereferenced first into
`T0`, becomes `T'`): an error and nothing more, or the dirty page `p` with id `id`, its
bytes `freshPage`, recorded in the page cache; the id is new (no page of the view covers its
slots) and below the high-water mark, which does not go down; and no view of the database
after the allocation (`ρ'`) sees its slots, none of which is the current freelist page's. -/
def allocRes (W : WView) (T T0 T' : WTx) (count : w64) (p : Loc) (err : GoInterface)
    (data' : Loc) (ρ' : DBState) : Prop :=
  ((T0 = T ∧ data' = W.data) ∨ (derefRel T T0 ∧ noView T0)) ∧
  ((err ≠ interface.nil ∧ T' = T0) ∨
   (err = interface.nil ∧ ∃ (id : w64) (st : go_etcd_io.bbolt.TxStats) (hwm' : w64),
      2 ≤ uint.nat id ∧ uint.nat T0.mv.pgid' ≤ uint.nat hwm' ∧
      uint.nat id + uint.nat count ≤ uint.nat hwm' ∧
      uint.Z hwm' * W.ps < 2 ^ 48 ∧
      (∀ k < uint.nat count, ¬ coversSlot W.pages (uint.nat id + k)) ∧
      (∀ k < uint.nat count, ∀ v0 v1, dbOK ρ' v0 v1 →
        unseenBy ρ' (curPages ρ' v0 v1) (uint.nat id + k) ∧ ¬ inFlPage ρ' v0 v1 (uint.nat id + k)) ∧
      T' = allocT T0 st hwm' id p (freshPage id (uint.nat count) W.ps)))

/-- What `tx.allocate(count)` did to the database (`ρ` to `ρ'`; the transaction `T` to `T'`):
nothing on an error, else what `db.allocate` did (`allocOK`) for the writer `w`. -/
def allocDB (ρ ρ' : DBState) (T T' : WTx) (count : w64) (err : GoInterface) : Prop :=
  (err ≠ interface.nil → ρ' = ρ) ∧
  (err = interface.nil → ∃ (w : Reader) (id : w64), ρ.wr = some w ∧
    allocOK ρ ρ' w T.mv T'.mv T.mv.txid' id (uint.nat count))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.allocate(count)` of the write transaction at `txl` (`count` at least one page), the
database's state an abstract resource `dbWR I γ W txl T.mv.txid' ρ` (the database whose writer
is `txl`, with the view `W`). If the allocation grows the mapping, the
transaction is dereferenced (`Bucket.dereference.spec`, hence `derefReady`) and stands over a
view at the new location `data'` (the same pages). If the remap fails after the
transaction was dereferenced, the database is lost (`dbLost`: the writer can only be rolled
back, `Tx.rollback.lspec`) and the transaction is kept, dereferenced. -/
abbrev Tx.allocate.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (T : WTx) (ρ : DBState) (count : w64),
  0 < sint.Z count → sint.Z count ≤ 2 ^ 32 → sint.Z count * W.ps < 2 ^ 47 →
  uint.Z T.mv.pgid' * W.ps < 2 ^ 48 → W.hwm ≤ uint.nat T.mv.pgid' →
  derefReady T (structFieldRef Tx go!"root" txl) → T.t.db' = W.dbl → W.data.locCar ≠ 0 →
  (∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl) → 16 ≤ W.ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl T.mv.txid' ρ ∗ ownWriteTxG W txl T ∗
      wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (∃ (ρ' : DBState) (data' : Loc) (T0 T' : WTx), dbWR I γ { W with data := data' } txl T.mv.txid' ρ' ∗
        ownWriteTxG { W with data := data' } txl T' ∗ wView { W with data := data' } ∗
        ⌜allocRes W T T0 T' count p err data' ρ' ∧ allocDB ρ ρ' T T' count err⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ (T0 : WTx), ⌜derefRel T T0 ∧ noView T0⌝ ∗
        dbLost I W.dbl txl T.mv.txid' ρ.fl ∗ ownWriteTxG W txl T0) }}

end spec

end bbolt
end EtcdGrove
end Perennial
