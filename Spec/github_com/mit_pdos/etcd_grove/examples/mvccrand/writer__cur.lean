/- Lean-first (no Rocq counterpart).

`w.cur()` (`examples/mvccrand/mvccrand.go`): the published revision, which the writer knows
exactly (its half of `γ.pv`, `World.lean`: only it publishes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.World

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev writer.cur.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (dq : DFrac) (γ : RandNames) (p : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      w ↦{dq} wv ∗ inv worldN (worldInv wv.h' γ) ∗ ghostVar γ.pv (1 : Qp).half p }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"cur")) (Val #()))
  {{ RET #p; w ↦{dq} wv ∗ ghostVar γ.pv (1 : Qp).half p }}

end spec

end mvccrand
end EtcdGrove
end Perennial
