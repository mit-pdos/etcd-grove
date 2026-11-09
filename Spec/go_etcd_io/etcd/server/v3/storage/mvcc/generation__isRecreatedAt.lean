/-
`(*generation).isRecreatedAt(rev)` (`key_index.go:365`): non-empty, its first revision's main is
`rev` (`genRecreatedAt`). Internal (`doCompact`). **Changes**: over `ownGenAt`.
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

/-- `g.isRecreatedAt(rev)`. -/
def generation.isRecreatedAt.spec : Prop :=
  ∀ (p : Loc) (og : Option Gen) (dq : DFrac) (rev : w64),
  {{ pkgInit ∗ match og with | none => ⌜p = null⌝ | some g => ownGenAt p g dq }}
    (App (Val (p @!! go.GoType.PointerType generation.ty @!! go!"isRecreatedAt")) (Val #rev))
  {{ RET #(match og with | none => false | some g => genRecreatedAt g rev);
      match og with | none => True | some g => ownGenAt p g dq }}

end spec
end Mvcc
end EtcdGrove
end Perennial
