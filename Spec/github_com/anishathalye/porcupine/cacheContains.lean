/- Lean-first (no Rocq counterpart).

`cacheContains(model, bucket, linearized, state)` (checker.go): whether the bucket has an entry
with the same bitset and a state `Equal` to `state`. Each entry satisfies `cacheEntryOk S p P`
(its state shared in the pool `p`, `Shared.lean`); a hit gives `P` of the bitset's words and of
the state (`Equal` returns `true` only on values of one state, `equalSpec`). The candidate
`state` is owned (not yet shared, so never one of the entries' invariants); each entry's state is
opened from its invariant for its `Equal`, with the pool's token, which comes back with the
candidate.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev cacheContains.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (p : NaInvPoolName) (P : List w64 → σ → Prop)
    (bk : GoSlice) (ces : List cacheEntry) (dqb : DFrac) (lin : GoSlice) (ws : List w64)
    (dq : DFrac) (k : Nat) (st : GoInterface) (t : σ),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ isEqHash S m ∗ bk ↦*{dqb} ces ∗
      ([∗list] ce ∈ ces, cacheEntryOk S p P ce) ∗ lin ↦*{dq} ws ∗ S.rep k st t ∗
      NonAtomicInvariant.own p ⊤ }}
    (App (App (App (App (Val (@! github_com.anishathalye.porcupine.cacheContains)) (Val #m))
      (Val #bk)) (Val #lin)) (Val #st))
  {{ (b : Bool), RET #b; bk ↦*{dqb} ces ∗ lin ↦*{dq} ws ∗ S.rep k st t ∗
      NonAtomicInvariant.own p ⊤ ∗ ⌜b = true → P ws t⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
