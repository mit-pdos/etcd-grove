/- Lean-first (no Rocq counterpart).

`cacheKey(model, linearized, state)` (checker.go): some hash of the bitset and the state (the
cache is sound for any hash, so nothing is said of it). The state value is the candidate, owned
(not yet shared, `Shared.lean`); `Hash` gives it back.
-/
module

public import Proof.github_com.anishathalye.porcupine.Cache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev cacheKey.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (lin : GoSlice) (ws : List w64) (dq : DFrac)
    (k : Nat) (st : GoInterface) (t : σ),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ isEqHash S m ∗ lin ↦*{dq} ws ∗ S.rep k st t }}
    (App (App (App (Val (@! github_com.anishathalye.porcupine.cacheKey)) (Val #m)) (Val #lin))
      (Val #st))
  {{ (h : w64), RET #h; lin ↦*{dq} ws ∗ S.rep k st t }}

end spec

end porcupine
end EtcdGrove
end Perennial
