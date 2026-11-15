/-
`tx.writeMeta()` (`tx.go`): the meta page (4d's `Meta.Write`: checksum, page `txid % 2`) written
under `metalock` by one `pwrite` of one aligned page, then `fdatasync` unless `NoSync`. **The
commit point.** (internal, mirrors the code)

**Proof sketch.** `make([]byte, pageSize)`, `pageInBuffer(buf, 0)`; 4d's `Meta.Write` (its premises
`root < pgid` and `freelist < pgid ∨ pgidNoFreelist` from `wtxAt`'s meta, the writer's high-water
mark) leaves `withMeta (withHdr buf …) (metaSummed m)`, valid by `metaValid_summed`, read back by
`meta_withMeta` (`metaOf`), page `txid % 2`; header and meta within the first sector
(`meta_in_sector`, decision 4c-D1). At the `pwrite`'s first step, fire the commit update with `ok` = whether the
page was written: a prophecy (`etc/proph-patches/bbolt/`) resolved before `metalock.Unlock` on the
mapped meta page's txid being the new one, not on the error (D9 makes the page all or nothing
in-process, but the write may succeed and report an errno, and `WriteAt` retries on `EINTR`, so
`err ≠ nil` with the page written is a run: 4c-D2). `metalock` keeps readers out until it is
written; a crash during or after it finds the old or the new meta (decision 4c-D1's sector rule, the
user's open decision, (a) or (b): the slot was clean and idle when written, and the header and meta
lie in its first sector, `BboltCommon.meta_in_sector`), both recoverable by `BoltSt.commit`/`attempt`. Then `fdatasync`
(unless `NoSync`); its outcome, and an error reported after the page was written, is what
`Commit`'s settling update records (`failed`).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) `tx.writeMeta()`: the commit update fired at the meta write with `ok` = the page
was written; `err` is nil iff the write reported no error and the sync (unless `NoSync`)
succeeded; `failed` covers a failed sync and an error reported after the page was written; `synced`
whether a sync ran and succeeded. -/
def Tx.writeMeta.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (Q : Bool → IProp GF),
  {{ wtxAt (GF := GF) tx γ T CommitStage.flushed ∗
      AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (ok : Bool), ⌜σ.data = T.base⌝ ∗
           boltState γ 1 (if ok then σ.commit T.cur T.noSync else σ.attempt T.cur T.noSync),
           COMM Q ok }> }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"writeMeta")) (Val #()))
  {{ (err : GoInterface), RET #err; wtxAt tx γ T CommitStage.flushed ∗
      ∃ ok synced failed : Bool, Q ok ∗
        ⌜(err = GoInterface.nil ↔ (ok = true ∧ failed = false)) ∧
          (synced = true ↔ (ok = true ∧ T.noSync = false ∧ failed = false)) ∧
          (failed = true → ok = true)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
