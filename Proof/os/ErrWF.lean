/-
The errors a comparison with an error variable can take (`err == io.EOF`, ...): comparing two
interfaces of one pointer type compares their pointers, which needs the values to be
locations (`errWF`: Go's are, a pointer-typed interface holding a pointer). A
`syscall.Errno` is no pointer.
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

/-- An error whose dynamic type is a pointer type holds a location. -/
def errWF (e : GoInterface) : Prop :=
  ∀ ei, e = interface.ok ei → ∀ t, ei.ty = go.GoType.PointerType t → ∃ l : Loc, ei.v = #l

theorem errWF_nil : errWF interface.nil := by
  intro ei h; cases h

theorem errWF_ptr (t : go.GoType) (l : Loc) :
    errWF (interface.mkOk (go.GoType.PointerType t) #l) := by
  intro ei h t' _
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h; exact ⟨l, rfl⟩

theorem errWF_errno (x : w64) :
    errWF (interface.mkOk _root_.Perennial.syscall.Errno.ty #x) := by
  intro ei h t ht
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h
  simp [_root_.Perennial.syscall.Errno.ty] at ht

end shape

end bbolt
end EtcdGrove
end Perennial
