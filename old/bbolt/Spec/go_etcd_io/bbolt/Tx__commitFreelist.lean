module
public import Proof.go_etcd_io.bbolt.CommitFL
public import Proof.go_etcd_io.bbolt.DBLost
public import Proof.go_etcd_io.bbolt.DBRollback

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

/-- `tx.commitFreelist()` of the write transaction at `txl` (the database `dbWR`, its freelist's
state `ρ.fl` with fewer than `2^32` free and pending ids): allocates a page of
`flAllocCount n ps` slots (`Tx.allocate.wspec`, `n` the free and pending ids before) and makes it
a freelist page of the free and pending ids after the allocation, sorted (`out`; its bytes
`flWritten`, in the page cache at its id), recorded as the meta's freelist page. If the
allocation fails, the transaction is rolled back: the database rolled back and without the
writer (`Tx.rollback.wspec`), or, if the remap failed after the dereference, lost
(`Tx.rollback.lspec`); the transaction's references cleared either way. -/
abbrev Tx.commitFreelist.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (T : WTx) (ρ : DBState),
  I.EstimatedWritePageSizeSpec → I.WriteSpec → I.RollbackSpec → I.ReloadSpec →
  I.IfaceFreeCountSpec → I.PendingCountSpec →
  ρ.fl.allIds.length < 2 ^ 32 →
  uint.Z T.mv.pgid' * W.ps < 2 ^ 48 → W.hwm ≤ uint.nat T.mv.pgid' →
  derefReady T (structFieldRef Tx go!"root" txl) → T.t.db' = W.dbl → W.data.locCar ≠ 0 →
  (∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl) → T.t.writable' = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl T.mv.txid' ρ ∗
      ownWriteTxG W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"commitFreelist")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (ρ' : DBState) (data' : Loc) (T0 T' : WTx) (id : w64) (p : Loc)
          (out : List w64),
        dbWR I γ { W with data := data' } txl T.mv.txid' ρ' ∗
        ownWriteTxG { W with data := data' } txl
          { T' with mv := { T'.mv with freelist' := id },
                    bufs := <[id := flWritten id (uint.nat (flAllocCount ρ.fl.allIds.length W.ps)) W.ps
                      ρ'.fl.allIds.length out]> T'.bufs } ∗
        wView { W with data := data' } ∗
        ⌜allocRes W T T0 T' (flAllocCount ρ.fl.allIds.length W.ps) p interface.nil data' ρ' ∧
          allocDB ρ ρ' T T' (flAllocCount ρ.fl.allIds.length W.ps) interface.nil ∧
          (∃ (st : TxStats) (hwm' : w64), T' = allocT T0 st hwm' id p
            (freshPage id (uint.nat (flAllocCount ρ.fl.allIds.length W.ps)) W.ps)) ∧
          PgidsSorted out ∧ out.Perm ρ'.fl.allIds⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ (w : Reader) (free' : List w64) (t : Tx),
        ⌜ρ.wr = some w ∧ PgidsIncr free'⌝ ∗
        ownDB I W.dbl γ
          ({ ρ with fl := { ρ.fl.rollback T.mv.txid' with free := free' } }.removeWriter w) ∗
        txl ↦ t ∗ ⌜t.db' = null⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ (t : Tx), txl ↦ t ∗ ⌜t.db' = null⌝) }}

end spec

end bbolt
end EtcdGrove
end Perennial
