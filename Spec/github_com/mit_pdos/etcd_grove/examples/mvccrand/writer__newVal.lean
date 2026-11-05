/- Lean-first (no Rocq counterpart).

`w.newVal()` (`examples/mvccrand/mvccrand.go`): the next value, `"v"` and the incremented count in
decimal (`itoaM`), the count incremented (for a count below `2 ^ 63 - 1`: the writer's at most
`Ops` operations, each at most three values).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.itoa

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
abbrev writer.newVal.spec : Prop :=
  ∀ (w : Loc) (wv : writer), 0 ≤ sint.Z wv.vals' → sint.Z wv.vals' + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      w ↦ wv }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"newVal")) (Val #()))
  {{ RET #(go!"v" ++ itoaM (sint.nat (wv.vals' + W64 1)));
      w ↦ { wv with vals' := wv.vals' + W64 1 } }}

end spec

end mvccrand
end EtcdGrove
end Perennial
