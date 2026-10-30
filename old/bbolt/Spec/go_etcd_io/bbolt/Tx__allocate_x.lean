module
public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.SpillOwn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- What `tx.allocate(count)` did during the spill (`allocRes`, with the database's state): the
transaction `T`, possibly dereferenced first into `T0` (each node keeping its struct but its
key, `derefKeep`; `derefRelX`), becomes `T'`; on an error nothing more (the database `ρ` unchanged), else the
dirty page `p` with id `id` (`allocT`), allocated as `db.allocate` says (`allocOK`: from the
freelist, or at the high-water mark). -/
def xallocRes (W : WView) (T T0 T' : WTx) (count : w64) (p : Loc) (err : GoInterface)
    (data' : Loc) (ρ ρ' : DBState) : Prop :=
  ((T0 = T ∧ data' = W.data) ∨ (derefRelX T T0 ∧ derefKeep T T0 ∧ noView T0)) ∧
  ((err ≠ interface.nil ∧ T' = T0 ∧ ρ' = ρ) ∨
   (err = interface.nil ∧ ∃ (id : w64) (st : go_etcd_io.bbolt.TxStats) (w : Reader),
      ρ.wr = some w ∧ allocOK ρ ρ' w T.mv T'.mv T.mv.txid' id (uint.nat count) ∧
      T' = allocT T0 st T'.mv.pgid' id p (freshPage id (uint.nat count) W.ps)))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.allocate(count)` (`Tx.allocate.wspec`) during the spill: the transaction's nodes
`nodeOwnX` (`SpillOwn.lean`), and what the allocation did to the database (`xallocRes`); if
the remap failed after the dereference, the database is lost (`dbLost`), the transaction
dereferenced kept. -/
abbrev Tx.allocate.xspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (T : WTx) (ρ : DBState) (count : w64),
  0 < sint.Z count → sint.Z count ≤ 2 ^ 32 → sint.Z count * W.ps < 2 ^ 47 →
  uint.Z T.mv.pgid' * W.ps < 2 ^ 48 → W.hwm ≤ uint.nat T.mv.pgid' →
  derefReadyX T (structFieldRef Tx go!"root" txl) → T.t.db' = W.dbl → W.data.locCar ≠ 0 →
  (∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl) → 16 ≤ W.ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl T.mv.txid' ρ ∗
      ownWriteTxGX W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (∃ (ρ' : DBState) (data' : Loc) (T0 T' : WTx), dbWR I γ { W with data := data' } txl T.mv.txid' ρ' ∗
        ownWriteTxGX { W with data := data' } txl T' ∗ wView { W with data := data' } ∗
        ⌜xallocRes W T T0 T' count p err data' ρ ρ'⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ (T0 : WTx), ⌜derefRelX T T0 ∧ derefKeep T T0 ∧ noView T0⌝ ∗
        dbLost I W.dbl txl T.mv.txid' ρ.fl ∗ ownWriteTxGX W txl T0) }}

end spec

end bbolt
end EtcdGrove
end Perennial
