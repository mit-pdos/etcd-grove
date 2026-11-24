/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/newLeaseExpiredNotifier.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.newLeaseExpiredNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.newLeaseExpiredNotifier.wp_proof :
    lease.newLeaseExpiredNotifier.spec (GF := GF) (hG := hG) := by
  wp_start as -
  (try wp_auto)
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mp Hm
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %s ⟨Hs, Hcap⟩
  · ipureintro; word
  (try wp_auto)
  irename «$r0» => Hn
  generalize «$r0_ptr» = np at *
  iStructNamed Hn
  iapply HΦ
  iunfold notifierAt
  iexists ∅
  iunfold notifierAtM
  iexists mp, s, []
  iframe
  iunfold queueAt
  simp only [List.map_nil, List.replicate_zero]
  iframe
  isplitl []
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  ipureintro
  exact ⟨List.nodup_nil, fun id p => by simp⟩

end proof

end EtcdGrove
end Perennial
