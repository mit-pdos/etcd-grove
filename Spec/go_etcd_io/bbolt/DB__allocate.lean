module
public import Proof.go_etcd_io.bbolt.DBRemap
public import Proof.go_etcd_io.bbolt.WriteTxDeref
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Proof.os.FileInfoAlias
public import Proof.runtime.GOOS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- What `db.allocate(txid, count)` did to the database (`σ` to `σ'`) and the writer's meta
(`mv` to `mv'`), returning page `id`: either `count` free ids from `id` on, now allocated by
`txid` (the high-water mark unchanged), or the ids from the high-water mark on, which moves
up by `count` (the mapping possibly grown: `remap`). The page's slots are none the writer's
view `w` covers, and the high-water mark stays below `2^48` bytes. -/
def allocOK (σ σ' : DBState) (w : Reader) (mv mv' : internal.common.Meta) (txid id : w64)
    (n : Nat) : Prop :=
  2 ≤ uint.Z id ∧ (∀ k < n, ¬ coversSlot w.pages (uint.nat id + k)) ∧
  mv' = { mv with pgid' := mv'.pgid' } ∧ uint.Z mv.pgid' ≤ uint.Z mv'.pgid' ∧
  uint.Z mv'.pgid' * σ.ps < 2 ^ 48 ∧
  ((σ.fl.canAllocate id n ∧ σ' = { σ with fl := σ.fl.allocate txid id n } ∧ mv' = mv) ∨
   (id = mv.pgid' ∧ uint.Z mv'.pgid' = uint.Z mv.pgid' + n ∧
    (σ' = σ ∨ ∃ d' sz', σ.sz ≤ sz' ∧ σ' = σ.remap d' sz')))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

/-- `db.allocate(txid, count)` (sequential use; no `Mlock`, Linux) of the database's writer `w`
(its share of the `data` field and its pages, half the `freelist` field, its meta `mv` at
`ml`, the rest of it `WR`): a page of `count` slots, its bytes `freshPage` (a zeroed buffer
but the header's id and overflow). If the page is at the high-water mark and the mapping too
small, `db.mmap` remaps: the writer is dereferenced (`WR` to `WR'`, the hypothesis on
`tx.root.dereference()`) and its share follows the mapping. Errors: before that, nothing
changed; after it, the mapping is lost and with it the database (only `WR'` remains). -/
abbrev DB.allocate.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) (w : Reader) (ml : Loc)
    (mv : internal.common.Meta) (WR WR' : IProp GF) (txid count : w64),
  I.AllocateSpec → σ.wr = some w → 0 < sint.Z count → sint.Z count * σ.ps < 2 ^ 47 →
  uint.Z mv.pgid' * σ.ps < 2 ^ 48 → w.hwm ≤ uint.nat mv.pgid' →
  (σ.rwtx ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ WR ∗
        pagesView σ.data σ.ps w.q w.pages }}
      (App (Val (structFieldRef Tx go!"root" σ.rwtx @!! go.GoType.PointerType Bucket.ty @!!
        go!"dereference")) (Val #()))
    {{ RET #(); WR' ∗ pagesView σ.data σ.ps w.q w.pages }}) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own w.q} σ.data ∗
      pagesView σ.data σ.ps w.q w.pages ∗
      structFieldRef DB go!"freelist" dbl ↦{DFrac.own halfQ} I.iface ∗
      structFieldRef Tx go!"meta" σ.rwtx ↦ ml ∗ ml ↦ mv ∗ WR }}
    (App (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"allocate")) (Val #txid))
      (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err ≠ interface.nil⌝ ∗ ownDB I dbl γ σ ∗
        structFieldRef DB go!"data" dbl ↦{DFrac.own w.q} σ.data ∗
        pagesView σ.data σ.ps w.q w.pages ∗
        structFieldRef DB go!"freelist" dbl ↦{DFrac.own halfQ} I.iface ∗
        structFieldRef Tx go!"meta" σ.rwtx ↦ ml ∗ ml ↦ mv ∗ WR) ∨
      (⌜err ≠ interface.nil⌝ ∗ WR') ∨
      (⌜err = interface.nil⌝ ∗ ∃ (σ' : DBState) (mv' : internal.common.Meta) (id : w64),
        ⌜allocOK σ σ' w mv mv' txid id (uint.nat count)⌝ ∗ ownDB I dbl γ σ' ∗
        structFieldRef DB go!"data" dbl ↦{DFrac.own w.q} σ'.data ∗
        pagesView σ'.data σ.ps w.q w.pages ∗
        structFieldRef DB go!"freelist" dbl ↦{DFrac.own halfQ} I.iface ∗
        structFieldRef Tx go!"meta" σ.rwtx ↦ ml ∗ ml ↦ mv' ∗
        ((⌜σ'.data = σ.data⌝ ∗ WR) ∨ WR') ∗
        bytesPointsto p (DFrac.own 1) (freshPage id (uint.nat count) σ.ps)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
