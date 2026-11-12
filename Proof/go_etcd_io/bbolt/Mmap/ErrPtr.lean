/-
**Pointer-typed errors** (U4c's `errPtrTyped`, moved here from `Mmap/Remap` by maintainer 10 for
37.9): the remap's callees (`DB.fileSize`, `DB.mmapSize`, `DB.munmap`, `mmapF`) state it in their
error posts, from `fmt.Errorf`'s `IsPointerError` (`errPtrTyped_of_ptr`), `errors.New`'s pointer
(`errPtrTyped_ptrOk`) and `syscall.Errno`, no pointer (`errPtrTyped_errno`).
-/
module

public import Perennial.Proof.errors.Base
public import Proof.syscall.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


section errptr
variable [GooseExts] [GoGlobalContext]

/-- **An error whose value is a location when its dynamic type is a pointer type** (U4c): what
`err == ErrMaxSizeReached` needs to step (`go_eq_interface` compares at the dynamic type, and
pointer equality is over locations; cf. Perennial's `errors.TreeTyped`). Every error `DB.mmap`
returns is one (`errors.New`'s, `fmt.Errorf`'s pointers, `syscall.Errno`). -/
def errPtrTyped (e : GoInterface) : Prop :=
  ∀ ii : GoInterfaceOk, e = GoInterface.ok ii → ∀ T : go.GoType, ii.ty = go.GoType.PointerType T →
    ∃ l : Loc, ii.v = #l

/-- `fmt.Errorf`'s error (`IsPointerError`) is `errPtrTyped`. -/
theorem errPtrTyped_of_ptr (ii : GoInterfaceOk) (h : errors.IsPointerError ii) :
    errPtrTyped (GoInterface.ok ii) := by
  intro ii' he T hT
  cases he
  obtain ⟨_, l, _, hl⟩ := h
  exact ⟨l, hl⟩

/-- A pointer error (`errors.New`'s `*errorString`) is `errPtrTyped`. -/
theorem errPtrTyped_ptrOk (T : go.GoType) (l : Loc) :
    errPtrTyped (interface.mkOk (go.GoType.PointerType T) #l) := by
  intro ii h T' hT
  unfold interface.mkOk at h
  cases h
  exact ⟨l, rfl⟩

/-- A `syscall.Errno` error is `errPtrTyped` (its type is no pointer type). -/
theorem errPtrTyped_errno (e : w64) : errPtrTyped (errnoErr e) := by
  intro ii h T hT
  unfold errnoErr at h
  split at h
  · cases h
  · unfold interface.mkOk at h
    cases h
    rw [← errno_ty_eq] at hT
    cases hT

end errptr

end bbolt
end EtcdGrove
end Perennial
