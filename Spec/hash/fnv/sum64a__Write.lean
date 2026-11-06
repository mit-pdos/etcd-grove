/-
`h.Write(b)` on a `*sum64a` (`hash/fnv`, translated with bodies): the cell's FNV-1a 64 state `h`
advanced over `b`'s bytes (`fnv64aFrom`), returning `len(b), nil`; `b` is only read, at any
fraction. Proved in `Proof/hash/fnv/sum64a__Write.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.hash.PkgInit
public import Spec.hash.fnv.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.fnv.Assumptions]

/-- See the file header. -/
abbrev hash.fnv.sum64a.Write.spec : Prop :=
  ∀ (l : Loc) (h : w64) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ (l ↦ h : IProp GF) ∗ s ↦*{dq} bs }}
    (App (Val (l @!! go.GoType.PointerType hash.fnv.sum64a.ty @!! go!"Write")) (Val #s))
  {{ RET (PairV #s.len #interface.nil); l ↦ hash.fnv.fnv64aFrom h bs ∗ s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
