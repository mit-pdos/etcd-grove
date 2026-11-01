/- Lean-first (no Rocq counterpart). The proof of `envFailure`: the atomic add opens `envErrors`'s
invariant. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.envFailure
public import Perennial.Spec.sync.atomic.AddUint64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem envFailure.wp_proof (wp_AddUint64 : sync.atomic.AddUint64.spec (GF := GF) (hG := hG)) :
    envFailure.spec (GF := GF) (hG := hG) := by
  wp_start as #Henv
  iunfold envFacts at Henv
  icases Henv with ⟨#Hatomic, #Hinv⟩
  wp_auto
  wp_apply_core wp_AddUint64 $$ [] [-Hatomic]
  · iexact Hatomic
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%x, Hx⟩
  iexists x
  iframe Hx
  iintro Hx
  imod Hmask with -
  imod Hclose $$ [Hx] with -
  · inext; iexists (x + W64 1); iexact Hx
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end bboltfs
end EtcdGrove
end Perennial
