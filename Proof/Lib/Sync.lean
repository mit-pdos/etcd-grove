/-
Facts about Perennial's model of Go's `sync` (the `RWMutex`'s reader slots and guard) that
belong to no Go package of this repository.

They are kept here until Perennial has them: each is a candidate for an independent Perennial
proposal (CLAUDE.md, "Changes to Perennial"), and goes once its Perennial counterpart lands.
The copies they replace were each proved in a package's section, under that package's
assumptions (`notes/decisions.md`, "Proof/Lib: facts that belong to no Go package").
-/
module

public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- Perennial's `RWMutex` admits at least two readers. -/
theorem actualMaxReaders_ge_2 : 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
  rw [sync.rwmutex.actualMaxReaders_unseal]; decide

section slots
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A guard of a lock from its reader slots (there is at least one). -/
theorem guard_of_slots [sync.Assumptions] (rw : Loc) (P : Qp → IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ⊢
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ∗
        sync.isRWMutexGuard rw P := by
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨Htok, Htoks⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  iframe Hguard
  iapply BigSepL.bigSepL_cons.2
  iframe Htok Htoks

end slots

end EtcdGrove
end Perennial
