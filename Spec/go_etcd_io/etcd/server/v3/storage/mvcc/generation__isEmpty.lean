/-
`(*generation).isEmpty()` (`key_index.go:361`): `nil` or no revision. Internal. **Changes**: over
`ownGenAt` (`none`: a `nil` receiver).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `g.isEmpty()`. -/
def generation.isEmpty.spec : Prop :=
  ∀ (p : Loc) (og : Option Gen) (dq : DFrac),
  {{ pkgInit ∗ match og with | none => ⌜p = null⌝ | some g => ownGenAt p g dq }}
    (App (Val (p @!! go.GoType.PointerType generation.ty @!! go!"isEmpty")) (Val #()))
  {{ RET #(match og with | none => true | some g => decide (g.revs = []));
      match og with | none => True | some g => ownGenAt p g dq }}

end spec
end Mvcc
end EtcdGrove
end Perennial
