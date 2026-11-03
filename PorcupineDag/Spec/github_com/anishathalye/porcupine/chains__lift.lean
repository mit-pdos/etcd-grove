/- Lean-first (no Rocq counterpart).

`(*chains).lift(ctx, model, consistency, oldState, stack, cache, serialized, liftFrom)` (dag.go,
PR #46): try the frontier's candidates from position `liftFrom` down (`DagTheory`'s cursor `p`).
At the search state `(fs, s, fr, cache)` (`searchOwn`, `Struct`, and `Bad` unless the context is
done), with some operation not linearized: either none could be lifted, nothing changed, and every
candidate leads nowhere (`Bad` at cursor `-1`, unless the context is done); or the candidate at some
position `q` was lifted: a frame `⟨y, s, q, fr⟩` pushed, its configuration cached, the chains at the
new heads with the new candidate list `fr'`, the cursor at its top, and the new state value
returned.
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
abbrev chains.lift.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (ctx : GoInterfaceOk)
    (ctxd : context.ContextDesc (IProp GF)) (cons : Consistency) (np : NaInvPoolName)
    (h : List (Theory.Op OpV)) (cs : List (List Nat)) (ch stack_ptr lin_ptr cm : Loc)
    (fs : List (Theory.Frame σ)) (fr : List Nat) (cache : List ((Nat → Prop) × σ))
    (sv : GoInterface) (s : σ) (lf : w64),
  ChainsOk h cs → HistWf h → AllocOk cs.length h.length →
  Struct S.M h cs (Before h cs) fs s fr (sint.Z lf) → (∃ y, y < h.length ∧ y ∉ ids fs) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ context.isContext ctx ctxd ∗
      isModelFilled S m ∗ isLinearizability cons ∗ histIoOk S h ∗
      searchOwn S np h cs ch stack_ptr lin_ptr cm fs fr cache ∗ shared S np fs.length sv s ∗ NonAtomicInvariant.own np ⊤ ∗
      (⌜Bad S.M h (Before h cs) fs s fr (sint.Z lf) cache⌝ ∨ □ ctxd.PDone) }}
    (App (App (App (App (App (App (App (App
      (Val (ch @!! go.GoType.PointerType chains.ty @!! go!"lift"))
      (Val #(GoInterface.ok ctx))) (Val #m)) (Val #cons)) (Val #sv)) (Val #stack_ptr)) (Val #cm))
      (Val #lin_ptr)) (Val #lf))
  {{ (nsv : GoInterface) (ok : Bool), RET (PairV #nsv #ok); NonAtomicInvariant.own np ⊤ ∗
      ((⌜ok = false⌝ ∗ searchOwn S np h cs ch stack_ptr lin_ptr cm fs fr cache ∗
          (⌜Bad S.M h (Before h cs) fs s fr (-1) cache⌝ ∨ □ ctxd.PDone)) ∨
       (⌜ok = true⌝ ∗ ∃ (y q : Nat) (t' : σ) (fr' : List Nat),
          searchOwn S np h cs ch stack_ptr lin_ptr cm (⟨y, s, q, fr⟩ :: fs) fr' ((fun i => i ∈ y :: ids fs, t') :: cache) ∗
          shared S np (fs.length + 1) nsv t' ∗
          ⌜Struct S.M h cs (Before h cs) (⟨y, s, q, fr⟩ :: fs) t' fr' ((fr'.length : Int) - 1)⌝ ∗
          (⌜Bad S.M h (Before h cs) (⟨y, s, q, fr⟩ :: fs) t' fr' ((fr'.length : Int) - 1)
              ((fun i => i ∈ y :: ids fs, t') :: cache)⌝ ∨ □ ctxd.PDone))) }}

end spec

end porcupine
end EtcdGrove
end Perennial
