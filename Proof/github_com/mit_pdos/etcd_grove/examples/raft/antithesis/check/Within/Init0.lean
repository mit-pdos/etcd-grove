/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the budget law of `Init0` (`init0_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem init0_within : Init0Within := by
  intro cfg s E hcfg h
  unfold init0 at h
  have b0 : bigOk 0 := by unfold bigOk; omega
  have b1 : bigOk 1 := by unfold bigOk; omega
  cases hb : cfg.bootstrapped
  · simp only [hb, Bool.not_false, ↓reduceIte, pure_ok, Except.ok.injEq] at h
    subst h
    refine State.Within.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ <;>
      simp_all [List.mem_replicate, logWithin, confWithin, termIntsWithin, Config.initConf]
  · simp only [hb, Bool.not_true] at h
    cases hv : cfg.initVoters with
    | nil => simp [hv] at h; cases h
    | cons first rest =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte, pure_ok, Except.ok.injEq] at h
      subst h
      refine State.Within.intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ <;>
        simp_all [List.mem_replicate, logWithin, confWithin, termIntsWithin, Config.initConf,
          Entry.chgSize]

end AntCheck
end EtcdGrove
end Perennial
