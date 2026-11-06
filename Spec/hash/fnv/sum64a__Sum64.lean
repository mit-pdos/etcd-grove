/-
`h.Sum64()` on a `*sum64a` (`hash/fnv`, translated with bodies): the cell's value, the FNV-1a 64
state. Proved in `Proof/hash/fnv/sum64a__Sum64.lean`. Lean-first (no Rocq counterpart).
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
abbrev hash.fnv.sum64a.Sum64.spec : Prop :=
  ∀ (l : Loc) (h : w64) (dq : DFrac),
  {{ (l ↦{dq} h : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType hash.fnv.sum64a.ty @!! go!"Sum64")) (Val #()))
  {{ RET #h; l ↦{dq} h }}

end spec

end EtcdGrove
end Perennial
