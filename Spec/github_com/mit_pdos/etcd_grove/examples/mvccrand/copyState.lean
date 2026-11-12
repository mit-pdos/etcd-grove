/- Lean-first (no Rocq counterpart).

`copyState(st)` (`examples/mvccrand/mvccrand.go`): a fresh map with `st`'s contents (the writer's
pending state, a copy of the last revision's).
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
abbrev copyState.spec : Prop :=
  ∀ (l : Loc) (M : GMap GoString kvRec) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      l ↦${dq} M }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.copyState)) (Val #l))
  {{ (c : Loc), RET #c; l ↦${dq} M ∗ c ↦$ M }}

end spec

end mvccrand
end EtcdGrove
end Perennial
