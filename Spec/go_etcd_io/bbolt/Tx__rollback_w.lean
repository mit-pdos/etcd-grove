module
public import Proof.go_etcd_io.bbolt.DBRollback
public import Proof.go_etcd_io.bbolt.WriteAlloc
public import Proof.go_etcd_io.bbolt.DBWrite
public import Proof.go_etcd_io.bbolt.FLPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `rollback` needs of the database `σ` (its freelist already rolled back) to reload the
free ids from the current meta's freelist page, for the metas the database's facts hold of:
the meta records a freelist page (`hasSyncedFreelist`), whose slots are inside the mapping and
seen by no view (so the database holds them whole), a well-formed freelist page whose ids
`Reload` accepts; and the database's facts hold with the free ids reloaded (the page's ids but
the pending ones, sorted). The database's facts do not record the freelist page (`dbOK` does not
say that the current meta's freelist page holds the free and pending ids of its commit), so the
caller (`Commit`) proves this. -/
def rbReloadOK (σ : DBState) : Prop :=
  ∀ v0 v1, dbOK σ v0 v1 →
    (if metaPick v0 v1 then v1 else v0).freelist' ≠ W64 18446744073709551615 ∧
    let fid := uint.nat (if metaPick v0 v1 then v1 else v0).freelist'
    let pg := pageAt σ.bs σ.ps fid
    (∀ k < pageSpan σ.bs σ.ps fid, fid + k < σ.nslots ∧ slotUnseen σ (fid + k)) ∧
    pageFlags pg = 16 ∧ flOff pg + 8 * flN pg ≤ pg.length ∧
    (fpOverflow (pageOf pg) → 0 ≤ sint.Z (flPageCount pg)) ∧
    (flIds pg).Nodup ∧ (∀ x ∈ flIds pg, 2 ≤ uint.Z x) ∧
    (flIds pg).length + σ.fl.pendingCount < 2 ^ 63 ∧ (flIds pg ≠ [] ∨ σ.fl.free = []) ∧
    ∀ free', PgidsIncr free' → free'.Perm ((flIds pg).filter (fun x => decide (x ∉ σ.fl.pendingIds))) →
      dbOK { σ with fl := { σ.fl with free := free' } } v0 v1

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.rollback()` of the writer `txl` (its meta's txid `txid`), the current meta still the one
its view is of: the freelist rolled back for `txid` (the pages it freed allocated again, those it
allocated dropped), the free ids reloaded from the current meta's freelist page (`Reload`: the
page's ids but the pending ones; `rbReloadOK`), and the writer closed (`Tx.close.wspec`). -/
abbrev Tx.rollback.wspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64) (σ : DBState)
    (T : WTx),
  I.RollbackSpec → I.ReloadSpec → I.IfaceFreeCountSpec → I.PendingCountSpec →
  I.EstimatedWritePageSizeSpec →
  T.t.writable' = true → T.t.db' = W.dbl → (T.bs !! structFieldRef Tx go!"root" txl).isSome →
  T.mv.txid' = txid → rbReloadOK { σ with fl := σ.fl.rollback txid } →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbWR I γ W txl txid σ ∗
      ownWriteTxG W txl T ∗ wView W }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"rollback")) (Val #()))
  {{ RET #(); ∃ (w : Reader) (free' : List w64) (t : Tx),
      ⌜σ.wr = some w ∧ PgidsIncr free'⌝ ∗
      ownDB I W.dbl γ
        ({ σ with fl := { σ.fl.rollback txid with free := free' } }.removeWriter w) ∗
      txl ↦ t ∗ ⌜t.db' = null⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
