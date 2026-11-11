/-
The proof of `Spec/go_etcd_io/bbolt/DB__Begin.lean` (U5, `notes/bbolt-proof-plan.md`): the
internal `DB.Begin_err.spec` (the same function), its error branch's `fmtErrorOk` dropped.
-/
module

public import Spec.go_etcd_io.bbolt.DB__Begin
public import Spec.go_etcd_io.bbolt.DB__Begin_err

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.Begin.wp_proof
    (wp_Begin_err : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.Begin_err.spec (GF := GF) (hG := hG)) :
    DB.Begin.spec (GF := GF) (hG := hG) := by
  intro hos db γ w Q
  wp_start_folded as Hpre
  wp_apply wp_Begin_err db γ w Q $$ [Hpre] as %tx %err Hpost
  · iexact Hpre
  iapply HΦ
  icases Hpost with (H | ⟨%Hne, -, H⟩)
  · ileft; iexact H
  · iright; iframe; ipureintro; exact Hne.1

end proof

end bbolt
end EtcdGrove
end Perennial
