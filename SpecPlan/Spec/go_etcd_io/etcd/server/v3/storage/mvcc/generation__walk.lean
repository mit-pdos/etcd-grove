/-
`(*generation).walk(f)` (`key_index.go:374`): `f` on the revisions from the last back until it
returns false; that index, or `-1` (`genWalk` at `f`'s answers `pf`). `f` may have effects (`doCompact`'s
writes `available`): its triple is over the caller's `I i` (after `i` calls). Internal (`get`,
`doCompact`). **Changes**: the closure's effects as a family `I`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

/-- `g.walk(f)`, `f`'s answers `pf`. -/
def generation.walk.spec : Prop :=
  ∀ (p : Loc) (g : Gen) (dq : DFrac) (f : GoFunc) (pf : Rev → Bool) (I : Nat → IProp GF),
  {{ pkgInit ∗ ownGenAt p g dq ∗ I 0 ∗
      □ (∀ (i : Nat) (r : Rev) (Φ : val → IProp GF), ⌜g.revs.reverse[i]? = some r⌝ -∗ I i -∗
          ▷ (I (i + 1) -∗ Φ #(pf r)) -∗ WP (App (Val #f) (Val #(revVal r))) {{ Φ }}) }}
    (App (Val (p @!! go.GoType.PointerType generation.ty @!! go!"walk")) (Val #f))
  {{ RET #(W64 (genWalk g.revs pf)); ownGenAt p g dq ∗
      I (if genWalk g.revs pf = -1 then g.revs.length else g.revs.length - (genWalk g.revs pf).toNat) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
