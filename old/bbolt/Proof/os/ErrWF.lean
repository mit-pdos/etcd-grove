/-
The errors a comparison with an error variable can take (`err == io.EOF`, ...): comparing two
interfaces of one type checks that the type is comparable and compares the values, which for a
pointer type needs them to be locations. The file system's errors (`errWF`) are pointers (an
`*os.PathError`, an `errors.New`) or a `syscall.Errno`: comparable, so the comparison does not
panic.
-/
module

public import Proof.os.FileModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section shape
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- An error (if any) holds a location of a pointer type, or is a `syscall.Errno`. -/
def errWF (e : GoInterface) : Prop :=
  ∀ ei, e = interface.ok ei →
    (∃ (t : go.GoType) (l : Loc), ei.ty = go.GoType.PointerType t ∧ ei.v = #l) ∨
    (∃ x : w64, ei.ty = _root_.Perennial.syscall.Errno.ty ∧ ei.v = #x)

theorem errWF_nil : errWF interface.nil := by
  intro ei h; cases h

theorem errWF_ptr (t : go.GoType) (l : Loc) :
    errWF (interface.mkOk (go.GoType.PointerType t) #l) := by
  intro ei h
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h; exact Or.inl ⟨t, l, rfl, rfl⟩

theorem errWF_errno (x : w64) :
    errWF (interface.mkOk _root_.Perennial.syscall.Errno.ty #x) := by
  intro ei h
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h; exact Or.inr ⟨x, rfl, rfl⟩

/-- An error of a pointer type holds a location. -/
theorem errWF_ptr_val {e : GoInterface} (h : errWF e) {ei : GoInterfaceOk}
    (hei : e = interface.ok ei) {t : go.GoType} (hty : ei.ty = go.GoType.PointerType t) :
    ∃ l : Loc, ei.v = #l := by
  rcases h ei hei with ⟨_, l, _, hv⟩ | ⟨_, h1, _⟩
  · exact ⟨l, hv⟩
  · rw [h1] at hty; simp [_root_.Perennial.syscall.Errno.ty] at hty

end shape

end bbolt
end EtcdGrove
end Perennial
