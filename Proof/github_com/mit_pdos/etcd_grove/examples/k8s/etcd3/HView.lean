/-
Lean-first (no Rocq counterpart).

# The indexed history (`hview`, K9 step 3)

- `hviewOwn v hs`: the Go `hview` `v` (`export.go`) is a view of the history holding `hs`: its `h`
  holds `hs` (`histOwn`) and its `sts[i]`, read-only, holds the store at revision `lo + i`
  (`histN hs (lo + i)`). `viewFrom h lo` builds one, `v.at r` reads it, returning what `histAt h r`
  would (`hview__at.lean`: its post is `histAt`'s).
- `histN_prefix`: the last store of a prefix `l ++ [s]` of `hs` is `hs`'s at revision `l.length + 1`
  (a node of the walk back from the newest is at its own revision).
- `wp_max_u64`: the builtin `max` of two `uint64`s (moved here from `target.lean`, for the
  `*Idx` functions).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore hview)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histN_prefix (l hs : List GSt) (s : GSt) (h : l ++ [s] <+: hs) :
    histN hs (l.length + 1) = s := by
  obtain ⟨t, rfl⟩ := h
  unfold histN
  have : (l ++ [s] ++ t).take (l.length + 1) = l ++ [s] := by
    exact List.take_left' (by simp)
  rw [this]; simp

theorem histAtL_eq_histN' (hs : List GSt) (r : w64) : histAtL hs r = histN hs (uint.nat r) := rfl

/-- The Go `hview` `v` is a view of the history holding `hs` (see the file header). -/
def hviewOwn (v : hview) (hs : List GSt) : IProp GF :=
  iprop(histOwn v.h' hs ∗ ∃ ss : List mstore, v.sts' ↦*□ ss ∗
    □ (∀ (i : Nat) (s : mstore), ⌜ss[i]? = some s⌝ -∗ storeOwn s (histN hs (uint.nat v.lo' + i))))

instance hviewOwn_persistent (v : hview) (hs : List GSt) :
    Persistent (hviewOwn (GF := GF) v hs) := by
  unfold hviewOwn; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The builtin `max` of two `uint64`s. -/
theorem wp_max_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ (m : w64), RET #m; ⌜uint.nat m = max (uint.nat a) (uint.nat b)⌝ }} := by
  wp_start
  wp_if_destruct
  all_goals (iapply HΦ; ipureintro; rw [Nat.max_def]; split <;> word)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
