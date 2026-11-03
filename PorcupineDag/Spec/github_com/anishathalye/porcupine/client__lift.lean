/- Lean-first (no Rocq counterpart).

`(*client).lift(ctx, model, consistency, oldState, cache, serialized)` (dag.go, PR #46): try to
linearize the client's head operation `y` from the state `s` (`oldState`, a shared value of index
`k`) with the operations `B` linearized (the bitset `serialized`): the model's step (through
`RVal.Step`, the model's `StepContext`), then the cache. Three outcomes: refused (the model
refuses, or the context is done), nothing changed; a step to a configuration already cached,
nothing changed; or linearized: the head moves on, the bitset has `y`, the configuration is cached
and the new state value (shared, of index `k + 1`) is returned.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev client.lift.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (ctx : GoInterfaceOk)
    (ctxd : context.ContextDesc (IProp GF)) (cons : Consistency) (np : NaInvPoolName)
    (h : List (Theory.Op OpV)) (cp : Loc) (cv : client) (cos : List clientOperation) (dq : DFrac)
    (co : clientOperation) (y : Nat) (o : Theory.Op OpV) (B : List Nat) (k : Nat)
    (sv : GoInterface) (s : σ) (cm lin_ptr : Loc) (lsl : GoSlice) (ws : List w64)
    (cache : List ((Nat → Prop) × σ)),
  0 ≤ sint.Z cv.head' → cos[sint.nat cv.head']? = some co → sint.Z co.id' = y →
  h[y]? = some o → co.Op'.Input' = o.val.1 → co.Op'.Output' = o.val.2 →
  y ∉ B → (∀ i ∈ B, i < h.length) → y < h.length → k < 2 ^ 60 → (h.length : Int) < 2 ^ 60 →
  ws.length = bsChunks h.length → (∀ i, bsBit ws i = decide (i ∈ B)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isContext ctx ctxd ∗
      isModelFilled S m ∗ isLinearizability cons ∗ S.ioOk o.val.1 o.val.2 ∗
      cp ↦ cv ∗ cv.cltOps' ↦*{dq} cos ∗ shared S np k sv s ∗ NonAtomicInvariant.own np ⊤ ∗
      cacheOwn S np h.length cm cache ∗ lin_ptr ↦ lsl ∗ lsl ↦* ws }}
    (App (App (App (App (App (App (Val (cp @!! go.GoType.PointerType client.ty @!! go!"lift"))
      (Val #(GoInterface.ok ctx))) (Val #m)) (Val #cons)) (Val #sv)) (Val #cm)) (Val #lin_ptr))
  {{ (nsv : GoInterface) (ok : Bool), RET (PairV #nsv #ok);
      cv.cltOps' ↦*{dq} cos ∗ NonAtomicInvariant.own np ⊤ ∗ lin_ptr ↦ lsl ∗
      ((⌜ok = false⌝ ∗ cp ↦ cv ∗ cacheOwn S np h.length cm cache ∗ lsl ↦* ws ∗
          (⌜S.M.step s o.val = none⌝ ∨ □ ctxd.PDone ∨
            ⌜∃ t', S.M.step s o.val = some t' ∧
              ∃ c ∈ cache, (∀ i, c.1 i ↔ i ∈ y :: B) ∧ c.2 = t'⌝)) ∨
       (⌜ok = true⌝ ∗ ∃ (t' : σ) (ws' : List w64), ⌜S.M.step s o.val = some t'⌝ ∗
          cp ↦ { cv with head' := cv.head' + W64 1 } ∗
          cacheOwn S np h.length cm ((fun i => i ∈ y :: B, t') :: cache) ∗ lsl ↦* ws' ∗
          ⌜ws'.length = ws.length ∧ ∀ i, bsBit ws' i = decide (i ∈ y :: B)⌝ ∗
          shared S np (k + 1) nsv t')) }}

end spec

end porcupine
end EtcdGrove
end Perennial
