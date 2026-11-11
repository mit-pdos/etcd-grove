/- Lean-first (no Rocq counterpart). The proof of `choose` (the remainder of a random number): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose

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

theorem choose.wp_proof :
    choose.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro; refine ⟨by decide, fun h => by word, fun _ => rfl⟩
  · wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %r _
    have hn : 0 < sint.Z n := by word
    rw [if_neg (show ¬ uint.Z n = 0 by intro h; word)]
    wp_auto
    iapply HΦ
    ipureintro
    have hu : (r % n).toNat < n.toNat := by
      rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (by word)
    have hn2 : n.toNat < 2 ^ 63 := by word
    have hz : sint.Z (r % n) = ((r % n).toNat : Int) := by word
    have hzn : sint.Z n = (n.toNat : Int) := by word
    refine ⟨?_, fun _ => ?_, fun h => absurd h (by omega)⟩
    · rw [hz]; omega
    · rw [hz, hzn]; omega

end proof

end mvccfull
end EtcdGrove
end Perennial
