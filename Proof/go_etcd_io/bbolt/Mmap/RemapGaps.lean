/-
**The remap's missing shared facts** (U4d, `notes/bbolt-proof-plan.md`): what `DB.mmap`'s proof
(`Mmap/RemapBody`) needs that no shared statement gives yet, each a `sorry` here, with the fix it
waits for (reported to the maintainer). Nothing else in the remap's proof is assumed.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Remap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section gaps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Gap 1 (`wdbOK`): the file is below `2 ^ 63` bytes** (`DB.fileSize`'s `Stat` reports an
`int64`; `DB.fileSize.spec` takes it). Fix: a `wdbOK` clause `w.m.size < 2 ^ 63` (`Open` reads the
size with `Stat`; `DB.grow` truncates to an `int64`). -/
theorem wdbOK_size_lt (w : WDb) (hok : wdbOK w) : w.m.size < 2 ^ 63 :=
  hok.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **Gap 2 (`wdbOK`): a file past the mapping ends on a page.** `wdbOK`'s `W` holds the slots
below `max (mapLen w.ms) w.m.size / 4096` (rounded down), so the page-cache bytes of a partial last
page of the file past the mapping are no one's; a remap that maps that page makes it a `W` slot,
whose bytes (`wBytes`) it cannot produce. bbolt never makes such a file (a file is unaligned only
as `Open` found it, and `Open` maps at least the file; `DB.grow` past the mapping truncates to
`sz + AllocSize`, whole pages). Fix: this `wdbOK` clause (`DB.grow`'s spec then needs a whole-page
`sz` above `AllocSize`), or `W`'s bound rounded up for the file (`(w.m.size + 4095) / 4096`). -/
theorem wdbOK_size_page (w : WDb) (hok : wdbOK w) (b : Loc) (l : Nat) (hms : w.ms = some (b, l)) :
    w.m.size ≤ l ∨ w.m.size % 4096 = 0 :=
  hok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b l hms

/-- **Gap 3 (`wtxCore`): the writer's view at a new base.** `wtxW … (Xd.rebase b)` holds
`viewOf r (Xd.rebase b).v`, a fragment of the transaction's view registry `r.n.vw` at the new base
`b`, which needs the registry's authority; no one holds it (`Inv/Names`: "discarded fragments").
Fix: `wtxCore` holds the writer's `ghostMapAuth r.n.vw 1 V` with every entry the view at its key
(`∀ k u, V !! k = some u → u = { X.v with base := k }`), so that a remap inserts the new base (or
finds it). -/
theorem wtxCore_viewOf_rebase (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (b : Loc)
    (E : CoPset) :
    wtxCore (GF := GF) K tx r m X ⊢
      |={E}=> wtxCore K tx r m X ∗ viewOf r { X.v with base := b } := by
  sorry

/-- **Gap 4 (`isBoltCoreP`): the database's namespace is disjoint from OsFs's.** `store_cells_agree`
opens `pagesInv` around a step that opens `osInv` (`↑osN ⊆ ⊤ \ ↑(pagesN N)`). `Open`'s spec takes
`↑N ## ↑osN`; fix: `isBoltCoreP` records it. -/
theorem core_osN_disj (K : BC) : K.core (GF := GF) ⊢ ⌜↑osN ## ↑(pagesN K.N)⌝ := by
  unfold BC.core isBoltCoreP
  iintro ⟨-, -, %H, -⟩
  ipureintro
  intro x hx
  exact H.2.2 x ⟨nclose_subseteq K.N "pages" x hx.2, hx.1⟩

/-- **Gap 5 (Perennial's `fmt.Errorf`): the remap's errors are pointer-typed** (`errPtrTyped`):
`syscall.Errno` values are no pointers, `errors.New`'s and `fmt.Errorf`'s are fresh pointers. The
callee specs (`DB.fileSize`, `DB.mmapSize`, `DB.munmap`, `mmap`) give only `fmtErrorOk`; fix:
`fmt.Errorf.spec`'s post with `IsPointerError` (`notes/perennial-changes.md`, "`fmt.Errorf`'s
result: a fresh pointer error"), then `errPtrTyped` in the callee specs' error posts. -/
theorem fmtErrorOk_errPtrTyped (err : GoInterface) : fmtErrorOk (GF := GF) err ⊢ ⌜errPtrTyped err⌝ := by
  sorry

end gaps

end bbolt
end EtcdGrove
end Perennial
