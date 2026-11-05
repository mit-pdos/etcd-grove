/- Lean-first (no Rocq counterpart).

`w.checkHook(i)` (`examples/mvccrand/mvccrand.go`): returns when the hook saved the index `i` being
applied (`saved`, the writer's own counter: only the writer's hook, under the batch lock of the
writer's own write, stores it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base
public import Perennial.Proof.sync.atomic.Base

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
abbrev writer.checkHook.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (dq : DFrac) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      w ↦{dq} wv ∗ sync.atomic.ownInt64 wv.saved' (DFrac.own 1) i }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"checkHook")) (Val #i))
  {{ RET #(); w ↦{dq} wv ∗ sync.atomic.ownInt64 wv.saved' (DFrac.own 1) i }}

end spec

end mvccrand
end EtcdGrove
end Perennial
