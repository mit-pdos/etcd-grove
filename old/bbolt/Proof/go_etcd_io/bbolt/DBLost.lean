/-
The database after a failed remap (`db.mmap` failing once the writer was dereferenced and the
old mapping unmapped: `data`, `dataref` nil): no transaction can read it any more, but its
writer can still be rolled back (`Tx.rollback` skips the reload of the freelist when `data` is
nil, then `Tx.close` releases the write lock). `dbLost` holds what that needs: the fields it
reads and writes, the freelist (its `Rollback` does not panic: `canRollback` for the writer's
txid), the write lock (held) and the statistics.
-/
module

public import Proof.go_etcd_io.bbolt.DBPred

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt sync

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The database at `dbl` whose mapping was lost while `txl` (txid `txid`) was its writer, its
freelist's state `fl` (see the module doc). -/
def dbLost (I : FLImpl (GF := GF)) (dbl txl : Loc) (txid : w64) (fl : FLState) : IProp GF :=
  iprop(∃ (fls sp : Loc) (ps : w64),
    ⌜fl.canRollback txid ∧ dbl ≠ null⌝ ∗ ownFL I fls fl ∗
    structFieldRef DB go!"data" dbl ↦ (null : Loc) ∗
    structFieldRef DB go!"freelist" dbl ↦ I.iface ∗
    structFieldRef DB go!"rwtx" dbl ↦ txl ∗
    structFieldRef DB go!"pageSize" dbl ↦□ ps ∗
    isMutex (structFieldRef DB go!"rwlock" dbl) iprop(True) ∗
    ownMutex (structFieldRef DB go!"rwlock" dbl) ∗
    ownRWMutex (structFieldRef DB go!"statlock" dbl) statsInv ∗
    structFieldRef DB go!"stats" dbl ↦ sp ∗ (⌜sp = null⌝ ∨ ∃ (sv : Stats), sp ↦ sv))

end defs

end bbolt
end EtcdGrove
end Perennial
