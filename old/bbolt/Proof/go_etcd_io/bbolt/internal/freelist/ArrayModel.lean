/-
The `array` freelist as an implementation of the freelist interface (`FLImpl`): its handle is
the `shared` field of the `array` struct at `a` (set once, persistent), its own part the `ids`
field and the slice it holds: the free ids, strictly increasing (not its capacity: `array`
never appends to it).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- Ids `j` and `j+1` of `f` are consecutive. -/
def consec (f : List w64) (j : Nat) : Prop := uint.Z (f.getD (j + 1) 0) = uint.Z (f.getD j 0) + 1

/-- A run of `n` consecutive ids of `f` ends at position `i` (`array.Allocate` takes the first
such run). -/
def runEnd (f : List w64) (n i : Nat) : Prop :=
  n ≤ i + 1 ∧ i < f.length ∧ ∀ j, i + 1 - n ≤ j → j < i → consec f j

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The `array` at `a` points to its `shared` at `s`. -/
def arrayHdl (a : Loc) (s : Loc) : IProp GF :=
  iprop(structFieldRef array' go!"shared" a ↦□ s)

instance arrayHdl_persistent (a s : Loc) : Persistent (arrayHdl (GF := GF) a s) := by
  unfold arrayHdl; infer_instance

/-- The `array` at `a` holds the free ids `free`. -/
def ownArrayPart (a : Loc) (_s : Loc) (free : List w64) : IProp GF :=
  iprop(∃ (ids : GoSlice),
    "Hidsf" ∷ structFieldRef array' go!"ids" a ↦ ids ∗ "%Hincr" ∷ ⌜PgidsIncr free⌝ ∗
    "Hids" ∷ ids ↦* free)

/-- The `array` at `a` as an implementation of the freelist interface. -/
def arrayImpl (a : Loc) : FLImpl (GF := GF) :=
  ⟨go.GoType.PointerType array'.ty, #a, ownArrayPart a, arrayHdl a,
    fun _ => by unfold arrayHdl; infer_instance⟩

end preds

end bbolt
end EtcdGrove
end Perennial
