/-
`membership.RaftCluster.IsIDRemoved` (`cluster.go:181-185`: under the lock, `c.removed[id]`).
Lean-first (no Rocq counterpart); D21 M2 (2026-10-19): `EtcdServer.Process`'s check of the sender.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.IsIDRemoved(id)` (`c` a cluster, `isRaftClusterG`) returns the removed map's entry for `id`,
for a removed map of which the side condition says `Pr` (D43 M4, 2026-10-26; until then `false`,
the static cluster's: `spec_static`). -/
abbrev membership.RaftCluster.IsIDRemoved.spec : Prop :=
  ∀ (c : Loc) (RM : membership.RcSide GF) (Pr : GMap w64 Bool → Prop) (id : w64),
  (∀ lid ms rm, RM lid ms rm ⊢ ⌜Pr rm⌝ ∗ RM lid ms rm) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.isRaftClusterG c RM }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsIDRemoved")) (Val #id))
  {{ (b : Bool), RET #b; ⌜∃ rm, Pr rm ∧ b = (rm !! id).getD false⌝ }}

/-- The static cluster's (`isRaftCluster`): its removed map is empty, so `false`. -/
theorem membership.RaftCluster.IsIDRemoved.spec_static
    (h : membership.RaftCluster.IsIDRemoved.spec (GF := GF) (hG := hG)) (c : Loc) (id : w64) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.isRaftCluster c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsIDRemoved")) (Val #id))
  {{ RET #false; True }} := by
  rw [(membership.isRaftCluster_static c).to_eq]
  iintro %Φ Hpre HΦ
  iapply (h c membership.rcStatic (fun rm => rm = ∅) id
    (fun lid ms rm => by
      unfold membership.rcStatic
      iintro %H
      isplitr <;> ipureintro
      · exact H.2
      · exact H)) $$ Hpre
  iintro %b %Hb
  obtain ⟨rm, Hrm, Hb⟩ := Hb
  subst Hrm
  simp only [GMap.lookup_empty, Option.getD_none] at Hb
  subst Hb
  iapply HΦ
  itrivial

end spec

end EtcdGrove
end Perennial
