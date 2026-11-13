/-
`shared.Count()` (U2 internal): `FreeCount()` (through the interface) plus `PendingCount()`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__PendingCount

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.Count()`: the number of free and pending ids. -/
abbrev shared.Count.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (c : GMap w64 Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownShC s I.iface fl c ∗ I.own fl.free }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Count" #s)) (Val #()))
  {{ RET #(W64 (fl.allIds.length : Int)); ownShC s I.iface fl c ∗ I.own fl.free }}

theorem shared.Count.wp_proof (I : FLImpl (GF := GF)) (hFC : I.FreeCountSpec) :
    shared.Count.spec I := by
  intro s fl c
  wp_start as ⟨Hsh, Hown⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hFC fl.free) $$ [Hown] as Hown
  · iframe
  ihave Hsh : ownShC s I.iface fl c $$ [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
  · iunfold ownShC; iexists al, ca, pe, pp; iframe
  wp_apply (shared.PendingCount.wp_proof s I.iface fl c) $$ [Hsh] as Hsh
  · iframe
  have : (fl.allIds.length : Int) = fl.free.length + fl.pendingIds.length := by
    simp [FLPg.allIds]
  rw [show W64 (fl.free.length : Int) + W64 (fl.pendingIds.length : Int) =
    (W64 (fl.allIds.length : Int) : w64) by rw [this]; word]
  iapply HΦ
  iframe
end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
