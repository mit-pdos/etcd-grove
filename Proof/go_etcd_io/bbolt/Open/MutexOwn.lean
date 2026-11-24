/-
`Lock`/`Unlock` of an owned, not yet shared `sync.Mutex` (U11e; for `loadFreelist`'s
`metalock.Lock(); db.freelist = fl; metalock.Unlock()` in the synced case, run before `Open`'s core
phase makes `metalock` a shared lock over `metaR`): the mutex is owned, so `Lock` succeeds at once
and `Unlock` gives the zero `Mutex` back (`Proof/sync/MutexOwned`). A local stand-in for an
owned-mutex spec of Perennial's `sync` (a proposal, like `Open/OnceOwn`).
-/
module

public import Perennial.Proof.sync.Results
public import Proof.sync.MutexOwned

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- An owned, locked `Mutex`. -/
def mutexHeld (m : Loc) : IProp GF := typedPointsto (GF := GF) m mutexLocked (DFrac.own 1)

/-- `m.Lock()` on an owned zero `Mutex`. -/
theorem Mutex.wp_Lock_own (m : Loc) :
    {{ typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); mutexHeld m }} := by
  exact wp_Mutex_Lock_owned m

/-- `m.Unlock()` on an owned locked `Mutex`: the zero `Mutex` back. -/
theorem Mutex.wp_Unlock_own (m : Loc) :
    {{ mutexHeld (GF := GF) m }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) }} := by
  exact wp_Mutex_Unlock_owned m

end own

end bbolt
end EtcdGrove
end Perennial
