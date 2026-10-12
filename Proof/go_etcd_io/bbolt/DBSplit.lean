module

public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section split
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The fields of a `DB` other than the ones read transactions share (`data`, `pageSize`), the
logger (never written after `Open`: persistent in `ownDB`) and the synchronization ones
(`dbSync`). -/
def dbPlain (dbl : Loc) (dq : DFrac) (dv : DB) : IProp GF :=
  iprop("StrictMode" ∷ structFieldRef DB go!"StrictMode" dbl ↦{dq} dv.StrictMode' ∗
    "NoSync" ∷ structFieldRef DB go!"NoSync" dbl ↦{dq} dv.NoSync' ∗
    "NoFreelistSync" ∷ structFieldRef DB go!"NoFreelistSync" dbl ↦{dq} dv.NoFreelistSync' ∗
    "FreelistType" ∷ structFieldRef DB go!"FreelistType" dbl ↦{dq} dv.FreelistType' ∗
    "NoGrowSync" ∷ structFieldRef DB go!"NoGrowSync" dbl ↦{dq} dv.NoGrowSync' ∗
    "PreLoadFreelist" ∷ structFieldRef DB go!"PreLoadFreelist" dbl ↦{dq} dv.PreLoadFreelist' ∗
    "MmapFlags" ∷ structFieldRef DB go!"MmapFlags" dbl ↦{dq} dv.MmapFlags' ∗
    "MaxBatchSize" ∷ structFieldRef DB go!"MaxBatchSize" dbl ↦{dq} dv.MaxBatchSize' ∗
    "MaxBatchDelay" ∷ structFieldRef DB go!"MaxBatchDelay" dbl ↦{dq} dv.MaxBatchDelay' ∗
    "AllocSize" ∷ structFieldRef DB go!"AllocSize" dbl ↦{dq} dv.AllocSize' ∗
    "MaxSize" ∷ structFieldRef DB go!"MaxSize" dbl ↦{dq} dv.MaxSize' ∗
    "Mlock" ∷ structFieldRef DB go!"Mlock" dbl ↦{dq} dv.Mlock' ∗
    "path" ∷ structFieldRef DB go!"path" dbl ↦{dq} dv.path' ∗
    "openFile" ∷ structFieldRef DB go!"openFile" dbl ↦{dq} dv.openFile' ∗
    "file" ∷ structFieldRef DB go!"file" dbl ↦{dq} dv.file' ∗
    "dataref" ∷ structFieldRef DB go!"dataref" dbl ↦{dq} dv.dataref' ∗
    "datasz" ∷ structFieldRef DB go!"datasz" dbl ↦{dq} dv.datasz' ∗
    "meta0" ∷ structFieldRef DB go!"meta0" dbl ↦{dq} dv.meta0' ∗
    "meta1" ∷ structFieldRef DB go!"meta1" dbl ↦{dq} dv.meta1' ∗
    "opened" ∷ structFieldRef DB go!"opened" dbl ↦{dq} dv.opened' ∗
    "rwtx" ∷ structFieldRef DB go!"rwtx" dbl ↦{dq} dv.rwtx' ∗
    "stats" ∷ structFieldRef DB go!"stats" dbl ↦{dq} dv.stats' ∗
    "batch" ∷ structFieldRef DB go!"batch" dbl ↦{dq} dv.batch' ∗
    "ops" ∷ structFieldRef DB go!"ops" dbl ↦{dq} dv.ops' ∗
    "readOnly" ∷ structFieldRef DB go!"readOnly" dbl ↦{dq} dv.readOnly')

/-- The synchronization fields of a `DB` (its locks, `sync.Once`, `sync.Pool`), which `Open`
turns into their protocols. -/
def dbSync (dbl : Loc) (dq : DFrac) (dv : DB) : IProp GF :=
  iprop("freelistLoad" ∷ structFieldRef DB go!"freelistLoad" dbl ↦{dq} dv.freelistLoad' ∗
    "pagePool" ∷ structFieldRef DB go!"pagePool" dbl ↦{dq} dv.pagePool' ∗
    "batchMu" ∷ structFieldRef DB go!"batchMu" dbl ↦{dq} dv.batchMu' ∗
    "rwlock" ∷ structFieldRef DB go!"rwlock" dbl ↦{dq} dv.rwlock' ∗
    "metalock" ∷ structFieldRef DB go!"metalock" dbl ↦{dq} dv.metalock' ∗
    "mmaplock" ∷ structFieldRef DB go!"mmaplock" dbl ↦{dq} dv.mmaplock' ∗
    "statlock" ∷ structFieldRef DB go!"statlock" dbl ↦{dq} dv.statlock')

/-- A `DB` is its fields: those read transactions share, the logger, the freelist, the
synchronization ones, the rest. -/
theorem DB_split (dbl : Loc) (dq : DFrac) (dv : DB) :
    (dbl ↦{dq} dv : IProp GF) ⊣⊢
      structFieldRef DB go!"data" dbl ↦{dq} dv.data' ∗
      structFieldRef DB go!"pageSize" dbl ↦{dq} dv.pageSize' ∗
      structFieldRef DB go!"logger" dbl ↦{dq} dv.logger' ∗
      structFieldRef DB go!"freelist" dbl ↦{dq} dv.freelist' ∗
      dbSync dbl dq dv ∗ dbPlain dbl dq dv ∗ ⌜dbl ≠ null⌝ := by
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef, dbSync, dbPlain]
  constructor
  · iintro ⟨H, %Hn⟩
    iNamed H
    iframe
    ipureintro; exact Hn
  · iintro ⟨Hd, Hp, Hl, Hf, Hs, Hr, %Hn⟩
    iNamed Hs
    iNamed Hr
    iframe
    ipureintro; exact Hn

end split

end bbolt
end EtcdGrove
end Perennial
