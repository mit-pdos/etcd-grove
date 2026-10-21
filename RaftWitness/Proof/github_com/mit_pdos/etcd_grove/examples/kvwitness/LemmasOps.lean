/-
Lean-first (no Rocq counterpart).

# The key-value store's operations: pure lemmas (2026-10-19)

The replica's Go map `kv` (`runOwn`, `Defs.lean`: a key it lacks has the value `[]`) after a
`Put` (`kvMap_put`) or an `Append` (`kvMap_append`): it stays the store's map, every key's value
(`kvUpd`, `Base.lean`). Used by `apply`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- After `r.kv[key] = val`. -/
theorem kvMap_put (K : GMap (List w8) (List w8)) (m : KVMap) (key val : List w8)
    (h : ∀ k, (K !! k).getD [] = m k) :
    ∀ k, ((<[key := val]> K) !! k).getD [] = kvUpd m key val k := by
  intro k
  by_cases hk : k = key
  · subst hk; rw [GMap.lookup_insert, kvUpd_same]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), kvUpd_other _ _ _ _ hk]; exact h k

/-- After `r.kv[key] = r.kv[key] + val`. -/
theorem kvMap_append (K : GMap (List w8) (List w8)) (m : KVMap) (key val : List w8)
    (h : ∀ k, (K !! k).getD [] = m k) :
    ∀ k, ((<[key := (K !! key).getD [] ++ val]> K) !! k).getD [] = kvUpd m key (m key ++ val) k := by
  intro k
  by_cases hk : k = key
  · subst hk; rw [GMap.lookup_insert, kvUpd_same, ← h k]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), kvUpd_other _ _ _ _ hk]; exact h k

end EtcdGrove
end Perennial
