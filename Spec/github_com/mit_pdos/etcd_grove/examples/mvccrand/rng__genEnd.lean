/- Lean-first (no Rocq counterpart).

`r.genEnd()` (`examples/mvccrand/mvccrand.go`): a range end, as a byte slice: `nil` (a single
key), empty (from the key on), an extra end or a key; the generator's state advanced. Its contents
are `[]` when it is `nil`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev rng.genEnd.spec : Prop :=
  ∀ (r : Loc) (g : rng),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      r ↦ g }}
    (App (Val (r @!! go.GoType.PointerType rng.ty @!! go!"genEnd")) (Val #()))
  {{ (sl : GoSlice), RET #sl; (∃ g' : rng, r ↦ g') ∗
      ∃ e : GoString, sl ↦* e ∗ ownSliceCap w8 sl (DFrac.own 1) ∗
        ⌜(e = [] ∨ e ∈ extraEndList ∨ e ∈ keyList) ∧ (sl = slice.nil → e = [])⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
