/-
Proof of `Spec/go_uber_org/zap/zapcore/CheckedEntry__Write.lean` over zap's code (zap-z2, 2026-11-23; until
then the trust boundary: zap-z1 found Goose's translation of `putCheckedEntry`'s `_cePool.Put(ce)`, zap's
generic `pool.Pool[T].Put(x)`, stuck, which Perennial's goose fixed in `6215ce3f2`): the entry is not
dirty, its `before` and `cores` slices are empty (no hook, no core write, no error), its `after` hook is
nil, and `putCheckedEntry` returns it to `_cePool` (zapcore's fact: a pool of `pooledEntry`s).
-/
module

public import Spec.go_uber_org.zap.zapcore.CheckedEntry__Write
public import Spec.go_uber_org.zap.internal.pool.Pool__Put

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
variable [package_sem : go_uber_org.zap.zapcore.Assumptions]

theorem zapcore.CheckedEntry.Write.wp_proof
    (wp_Put : zap.internal.pool.Pool.Put.spec (GF := GF) (hG := hG)) :
    zapcore.CheckedEntry.Write.spec (GF := GF) (hG := hG) := by
  intro ce fields
  wp_start as Hce
  ihave #Hzc := _root_.Perennial.go_uber_org.zap.zapcore.isInit_access $$ Hpkg
  icases Hzc with ⟨-, ⟨%pce, #Hpce, #Hpool⟩⟩
  unfold zapcore.zapEntry
  icases Hce with ⟨%v, Hv, %hv, Hb, Hc⟩
  obtain ⟨hdirty, hafter⟩ := hv
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hv
  ihave %Hblen := ownSlice_len $$ Hb
  ihave %Hclen := ownSlice_len $$ Hc
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  rw [hdirty]
  wp_auto
  have hb0 : sint.Z v.before'.len = 0 := by
    obtain ⟨h1, h2⟩ := Hblen
    have h3 : (sint.Z v.before'.len).toNat = 0 := h1.symm
    omega
  have hc0 : sint.Z v.cores'.len = 0 := by
    obtain ⟨h1, h2⟩ := Hclen
    have h3 : (sint.Z v.cores'.len).toNat = 0 := h1.symm
    omega
  wp_for
  have hz : sint.Z (W64 0) = 0 := rfl
  simp only [hb0, hz, Int.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  wp_for
  simp only [hc0, hz, Int.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  rw [hafter]
  wp_auto
  -- putCheckedEntry: `_cePool.Put(ce)`
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_Put _ pce pooledEntry ce $$ [Hv Hb Hc]
  · iframe #
    unfold pooledEntry
    iexists _
    iframe
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
