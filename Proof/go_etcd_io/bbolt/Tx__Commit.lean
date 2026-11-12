/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Commit.lean` (U10i, `notes/bbolt-proof-plan.md`): the
internal `Tx.Commit_err.spec` (the same function), its error branch's `fmtErrorOk` dropped.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Commit
public import Spec.go_etcd_io.bbolt.Tx__Commit_err

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem Tx.Commit.wp_proof
    (wp_Commit_err : ∀ [HasExt osFsExt], Tx.Commit_err.spec (GF := GF) (hG := hG)) :
    Tx.Commit.spec (GF := GF) (hG := hG) := by
  intro hos tx γ T Q
  wp_start_folded as Hpre
  wp_apply wp_Commit_err tx γ T Q _ .rfl $$ [Hpre] as %err ⟨Hdone, Hpost⟩
  · iexact Hpre
  iapply HΦ
  iframe Hdone
  icases Hpost with (H | ⟨%Hne, -, H⟩)
  · ileft; iexact H
  · iright; iframe; ipureintro; exact Hne

end proof

end bbolt
end EtcdGrove
end Perennial
