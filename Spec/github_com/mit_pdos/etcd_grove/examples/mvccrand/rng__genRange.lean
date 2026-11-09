/- Lean-first (no Rocq counterpart).

`r.genRange(cur)` (`examples/mvccrand/mvccrand.go`), for a revision `cur ≥ 0` (with room for
`cur + 2`): a range read's request, its key one of the tester's keys and its end `genEnd`'s, at
revision `0`, `-1` (the transaction's) or one of `0 … cur + 1`, with a limit in `[0, 4)` and any
flags; the generator's state advanced.
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
abbrev rng.genRange.spec : Prop :=
  ∀ (r : Loc) (g : rng) (cur : w64), 0 ≤ sint.Z cur → sint.Z cur + 2 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      r ↦ g }}
    (App (Val (r @!! go.GoType.PointerType rng.ty @!! go!"genRange")) (Val #cur))
  {{ (q : rangeReq), RET #q; (∃ g' : rng, r ↦ g') ∗
      ∃ kk e : GoString, q.key' ↦* kk ∗ ownSliceCap w8 q.key' (DFrac.own 1) ∗
        q.end' ↦* e ∗ ownSliceCap w8 q.end' (DFrac.own 1) ∗
        ⌜kk ∈ keyList ∧ (e = [] ∨ e ∈ extraEndList ∨ e ∈ keyList) ∧ (q.end' = slice.nil → e = []) ∧
          -1 ≤ sint.Z q.ro'.Rev' ∧ sint.Z q.ro'.Rev' ≤ sint.Z cur + 1 ∧
          0 ≤ sint.Z q.ro'.Limit' ∧ sint.Z q.ro'.Limit' < 4⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
