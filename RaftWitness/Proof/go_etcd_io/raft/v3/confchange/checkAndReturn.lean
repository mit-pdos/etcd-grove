/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/checkAndReturn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.checkAndReturn
public import Spec.go_etcd_io.raft.v3.confchange.checkInvariants

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confchange.checkAndReturn.wp_proof
    (wp_confchange_checkInvariants : confchange.checkInvariants.spec (GF := GF) (hG := hG)) :
    confchange.checkAndReturn.spec (GF := GF) (hG := hG) := by
  intro cfg trk c prs pvs dqc dqm dqp
  wp_start as ⟨Hc, Htrk, Hprs⟩
  wp_auto
  wp_apply wp_confchange_checkInvariants cfg trk c prs pvs dqc dqm dqp $$ [$Hc $Htrk $Hprs]
    as %err ⟨Hc, Htrk, Hprs, %Herr⟩
  cases err with
  | nil =>
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact .inl ⟨Herr.1 rfl, rfl, rfl, rfl⟩
  | ok e =>
    wp_auto
    wp_apply wp_map_make1 (K := w64) (V := Loc) as %m Hm
    iapply HΦ
    iframe
    ipureintro
    exact .inr ⟨fun h => (nomatch Herr.2 h), fun h => (nomatch h)⟩

end proof

end EtcdGrove
end Perennial
