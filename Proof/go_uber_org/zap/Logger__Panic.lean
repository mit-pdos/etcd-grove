/-
Proof of `Spec/go_uber_org/zap/Logger__Panic.lean` over zap's code (zap-z2, 2026-11-23; until then the trust
boundary): `check(PanicLevel, msg)` on a `NewNop` logger returns a fresh entry from zapcore's `_cePool` whose
`after` hook is `WriteThenPanic`; its `Write` (no hook, no core) calls the hook, which panics with the
message (`panic(ce.Message)`).
-/
module

public import Spec.go_uber_org.zap.Logger__Panic
public import Spec.go_uber_org.zap.internal.pool.Pool__Get
public import Proof.go_uber_org.zap.CheckTerminal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.Assumptions]

theorem zap.Logger.Panic.wp_proof
    (wp_Get : zap.internal.pool.Pool.Get.spec (GF := GF) (hG := hG))
    : zap.Logger.Panic.spec (GF := GF) (hG := hG) := by
  intro l msg fields
  wp_start as #Hok
  wp_auto
  wp_apply zap.wp_check_terminal wp_Get l (W8 4) (W8 2) msg (Or.inl ⟨rfl, rfl⟩) $$ [$Hok] as %ce Hce
  unfold zap.terminalEntry
  icases Hce with ⟨%v, Hv, %hv⟩
  obtain ⟨Hnn, hdirty, hmsg, hafter, hb0, hc0⟩ := hv
  try wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  -- `ce.Write(fields...)`: not dirty, no `before` hook, no core
  wp_method_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  rw [hdirty]
  wp_auto
  have hz : sint.Z (W64 0) = 0 := rfl
  wp_for
  simp only [hb0, hz, Int.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  wp_for
  simp only [hc0, hz, Int.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  rw [hafter]
  wp_auto
  -- the hook: `CheckWriteAction.OnWrite`
  wp_method_call
  wp_call
  wp_auto
  -- `WriteThenPanic`: `panic(ce.Message)`
  wp_apply wp_panic
  iapply HΦ
  ipureintro
  rw [hmsg]

end proof

end EtcdGrove
end Perennial
