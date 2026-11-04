/-
The remap, `db.mmap(minsz)` by the live writer (U4, `notes/bbolt-proof-plan.md`; design §3.11,
risk R5): stated; the proof is to do, split across modules (the plan below).

`DB.mmap` is `mmaplock.Lock()`, `defer mmaplock.Unlock()`, `db.mmapUnlocked(minsz)`, which:
1. `lg := db.Logger()`; `fileSize, err := db.fileSize()` (error: logged, returned: nothing changed);
2. `size := max(fileSize, minsz)`; `size, err = db.mmapSize(size)` (error: nothing changed);
3. `db.MaxSize > 0 && size > db.MaxSize` (and `size > fileSize`): `ErrMaxSizeReached` (nothing
   changed); `db.Mlock` is false (`dbFixed`);
4. `db.rwtx.root.dereference()` (`Bucket.dereference.spec`: `derefRel X Xd`);
5. `db.munmap()` (`Mmap/Munmap`): before it `store_wreturn` (the view home), `store_gather` (the
   store slots' halves, the meta lend quarter), the writer's quarter of `metaCellsQ`, `wCells`;
   the cells joined by `Mmap/Cells`' `mapCells_gather` over `slots_partition` (from `wdbOK`);
   an error: the mapping lost (`wtxLost`/`wdbLost`, `junk` the leaked mapping if `munmap` left it);
6. `mmap(db, size)` (`Mmap/Map`'s `mmapF`): an error, or Madvise's (the mapping leaked as `junk`),
   leaves the mapping lost; the deferred rollback `munmap` runs only if `err != nil` after this;
7. `store_cells_agree` + `store_carve` on the new mapping (the store slots' cells split off
   `mapCells`, the rest to `wCells`, `W` re-derived for the new length: `wdbRemap`);
8. `db.meta0/1 = db.page(0/1).Meta()`, `Validate` of both (`metaOk`: the current one is valid, so
   the "both invalid" error is unreachable);
9. `store_wborrow` (the view re-borrowed at the new base), `wtxHeap_rebase` (`Mmap/Rebase`) for
   the writer's records, `Unlock` with `Pm 1` back.

Proof modules to write: `Mmap/RemapLock` (1-3 and the lock), `Mmap/RemapUnmap` (4-5),
`Mmap/RemapMap` (6-8), `Mmap/RemapEnd` (9), this file assembling them.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section remap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **An error whose value is a location when its dynamic type is a pointer type** (U4c): what
`err == ErrMaxSizeReached` needs to step (`go_eq_interface` compares at the dynamic type, and
pointer equality is over locations; cf. Perennial's `errors.TreeTyped`). Every error `DB.mmap`
returns is one (`errors.New`'s, `fmt.Errorf`'s pointers, `syscall.Errno`). -/
def errPtrTyped [GooseExts] [GoGlobalContext] (e : GoInterface) : Prop :=
  ∀ ii : GoInterfaceOk, e = GoInterface.ok ii → ∀ T : go.GoType, ii.ty = go.GoType.PointerType T →
    ∃ l : Loc, ii.v = #l

/-- **`db.mmap(minsz)` by the live writer `tx`**: on success the records dereferenced and
re-based on the new mapping (`derefRel`, `WX.rebase`), the writer side remapped (`wdbRemap`),
the mapping at least `minsz` long; on an error (`fmtErrorOk`, `errPtrTyped`), nothing changed (before
`dereference`: `fileSize`, `mmapSize`, `ErrMaxSizeReached`), or the mapping lost. -/
abbrev DB.mmap.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (minsz : w64),
  0 < sint.Z minsz → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (K.db @!! go.GoType.PointerType DB.ty @!! go!"mmap")) (Val #minsz))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (Xd : WX) (b : Loc) (w' : WDb),
        wtxW K tx r m (Xd.rebase b) ∗ wdbW K tx (Xd.rebase b).v w' ∗
        ⌜derefRel X Xd ∧ wdbRemap w w' ∧ sint.nat minsz ≤ mapLen w'.ms⌝) ∨
      (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW K tx X.v w) ∨
         (∃ (Xd : WX) (b : Loc) (w' : WDb), wtxLost K tx r m (Xd.rebase b) ∗
           wdbLost K tx (Xd.rebase b).v w' ∗
           ⌜derefRel X Xd ∧ w'.C = w.C ∧ w'.fl = w.fl⌝))) }}

theorem DB.mmap.wp_proof : DB.mmap.spec (GF := GF) (hG := hG) := by
  sorry

end remap

end bbolt
end EtcdGrove
end Perennial
