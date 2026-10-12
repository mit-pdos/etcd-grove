module
public import Proof.go_etcd_io.bbolt.WriteTxLemmas

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
slots) and below the high-water mark, which does not go down. -/
def allocRes (W : WView) (T T0 T' : WTx) (count : w64) (p : Loc) (err : GoInterface)
    (data' : Loc) : Prop :=
  ((T0 = T ∧ data' = W.data) ∨ (derefRel T T0 ∧ noView T0)) ∧
  ((err ≠ interface.nil ∧ T' = T0) ∨
   (err = interface.nil ∧ ∃ (id : w64) (st : go_etcd_io.bbolt.TxStats) (hwm' : w64),
      2 ≤ uint.nat id ∧ uint.nat T0.mv.pgid' ≤ uint.nat hwm' ∧
      uint.nat id + uint.nat count ≤ uint.nat hwm' ∧
      uint.Z hwm' * W.ps < 2 ^ 48 ∧
      (∀ k < uint.nat count, ¬ coversSlot W.pages (uint.nat id + k)) ∧
      T' = allocT T0 st hwm' id p (freshPage id (uint.nat count) W.ps)))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.allocate(count)` of the write transaction at `txl` (`count` at least one page), the
database's state an abstract resource `dbR W txl ρ` (the database whose writer is `txl`,
with the view `W`). If the allocation grows the mapping, the
transaction is dereferenced (`Bucket.dereference.spec`, hence `derefReady`) and stands over a
view at the new location `data'` (the same pages). If the remap fails after the
transaction was dereferenced, the database is lost (an error, the transaction alone). -/
abbrev Tx.allocate.wspec (R : Type) (dbR : WView → Loc → R → IProp GF) : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx) (ρ : R) (count : w64),
  0 < sint.Z count → sint.Z count ≤ 2 ^ 32 → sint.Z count * W.ps < 2 ^ 47 →
  uint.Z T.mv.pgid' * W.ps < 2 ^ 48 →
  derefReady T (structFieldRef Tx go!"root" txl) → T.t.db' = W.dbl →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbR W txl ρ ∗ ownWriteTxG W txl T ∗
      wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (∃ (ρ' : R) (data' : Loc) (T0 T' : WTx), dbR { W with data := data' } txl ρ' ∗
        ownWriteTxG { W with data := data' } txl T' ∗ wView { W with data := data' } ∗
        ⌜allocRes W T T0 T' count p err data'⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ (T0 : WTx), ⌜derefRel T T0⌝ ∗ ownWriteTxG W txl T0) }}

end spec

end bbolt
end EtcdGrove
end Perennial
