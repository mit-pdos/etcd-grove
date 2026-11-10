/- Lean-first (no Rocq counterpart). The proof of `normalize` (three clamps): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.normalize

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem normalize.wp_proof :
    normalize.spec (GF := GF) (hG := hG) := by
  intro cfg
  wp_start
  wp_auto
  wp_join iprop(cfg_ptr ↦ { cfg with
      Depth' := if sint.Z cfg.Depth' < 1 then W64 1 else cfg.Depth' }) with [cfg] as cfg
  · rw [if_pos (by word)]; iframe
  · rw [if_neg (by word)]; iframe
  wp_join iprop(cfg_ptr ↦ { cfg with
      Depth' := if sint.Z cfg.Depth' < 1 then W64 1 else cfg.Depth'
      MaxVal' := if sint.Z cfg.MaxVal' < 0 then W64 0 else cfg.MaxVal' }) with [cfg] as cfg
  · rw [if_pos (show sint.Z cfg.MaxVal' < 0 by word)]; iframe
  · rw [if_neg (show ¬ sint.Z cfg.MaxVal' < 0 by word)]; iframe
  wp_join iprop(cfg_ptr ↦ normalizeM cfg) with [cfg] as cfg
  · unfold normalizeM; rw [if_pos (show 511 < sint.Z cfg.Watchers' by word)]; iframe
  · unfold normalizeM; rw [if_neg (show ¬ 511 < sint.Z cfg.Watchers' by word)]; iframe
  iapply HΦ; itrivial

end proof

end mvccfull
end EtcdGrove
end Perennial
