/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/decimal.lean`: every index is in
bounds (the loop's `s[j]` at `j < len(s)`, `s[0]` under `len(s) > 1`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.decimal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

theorem decimal.wp_proof : decimal.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  try wp_auto
  -- the length checks: `len(s) == 0 || len(s) > 5 || (len(s) > 1 && s[0] == '0')`
  repeat (first
    | wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    | wp_auto)
  done

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
