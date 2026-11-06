/-
`fnv.New64a()` (`hash/fnv`, translated with bodies): a new `*sum64a` cell holding FNV-64's offset
basis, boxed as a `hash.Hash64`. Its state is the cell's value: `(*sum64a).Write` and
`(*sum64a).Sum64` (`Spec/hash/fnv/sum64a__Write.lean`, `sum64a__Sum64.lean`) work on it.
Proved in `Proof/hash/fnv/New64a.lean`. Lean-first (no Rocq counterpart).
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
abbrev hash.fnv.New64a.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! hash.fnv.New64a)) (Val #()))
  {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType hash.fnv.sum64a.ty) #l);
      l ↦ hash.fnv.fnv64aOffset }}

end spec

end EtcdGrove
end Perennial
