/- Lean-first (no Rocq counterpart).

# `etcd/dist/kvremote`: M1, `etcd_kv_safe_nocrash` (`notes/etcd-dist-plan.md` §11.3 step 6, §21)

M1 is a corollary of the full no-crash theorem `etcd_safe_nocrash` (`dist/TopLevelRobustness.lean`):
- `etcd_kv_safe_nocrash_of_full`: the full statement `etcd_robust_nocrash.spec` implies M1's
  `etcd_kv_safe_nocrash.spec`. This checks that M1 is the full statement with one premise added.
- `etcd_kv_safe_nocrash`: that implication at `etcd_safe_nocrash`.

No axiom and no `sorry` of its own.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

/-- **M1 is the full statement with one more premise**: `etcd_safe_nocrash` implies
`etcd_kv_safe_nocrash`. The proof applies the full statement to M1's arguments and drops the scope, so it
fails to compile if the two statements differ in anything but `Hscope`. -/
theorem etcd_kv_safe_nocrash_of_full (H : etcd_robust_nocrash.spec) : etcd_kv_safe_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ d _Hscope boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
  exact H d boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips

/-- **M1: `etcd_kv_safe_nocrash`** (`notes/etcd-dist-plan.md` §11.3, §21): `etcd_safe_nocrash` at M1's
scope. -/
theorem etcd_kv_safe_nocrash : etcd_kv_safe_nocrash.spec :=
  etcd_kv_safe_nocrash_of_full etcd_safe_nocrash

end etcd_dist
end EtcdGrove
end Perennial

end
