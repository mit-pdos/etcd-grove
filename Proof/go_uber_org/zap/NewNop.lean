/-
Proof of `Spec/go_uber_org/zap/NewNop.lean` over zap's code (v1.28.0, `logger.go`): `NewNop()` is
`&Logger{core: zapcore.NewNopCore(), errorOutput: zapcore.AddSync(io.Discard), addStack:
zapcore.FatalLevel + 1, clock: zapcore.DefaultClock}`, a `zap.nopLogger` once its points-to is made
persistent (prove-zap3, 2026-11-21: until then a trust-boundary axiom, `zap.loggerRaw` being opaque).
The body's steps are `zap_wp_NewNop_init` (zap's initializer runs `NewNop` too, before its own
`isPkgInit`), from io's and zapcore's package facts.
-/
module

public import Spec.go_uber_org.zap.NewNop
public import Proof.go_uber_org.zap.Init

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
variable [package_sem : _root_.Perennial.go_uber_org.zap.Assumptions]

theorem zap.NewNop.wp_proof : zap.NewNop.spec (GF := GF) (hG := hG) := by
  iintro %Φ #Hpkg HΦ
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hzc : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore $$ []
  · iPkgInit
  ihave #Hdeps : (iprop(isPkgInit (PROP := IProp GF) pkg_id.io ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore) : IProp GF) $$ []
  · isplitl []
    · iexact Hio
    · iexact Hzc
  iapply wp_fupd
  wp_apply EtcdGrove.zap_wp_NewNop_init $$ Hdeps as %l ⟨%v, Hl, %Hv⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨hc, hd, ha, hp, hf, c, hclk⟩ := Hv
  iStructNamed Hl
  ipersist core
  ipersist development
  ipersist addCaller
  ipersist onPanic
  ipersist onFatal
  ipersist name
  ipersist clock
  imodintro
  iapply HΦ
  unfold zapLoggerOk zap.nopLogger
  isplitr
  · ipureintro
    exact Hnn
  imodintro
  rw [hc, hd, ha, hp, hf, hclk] at *
  isplitl []
  · iexact core
  isplitl []
  · iexact development
  isplitl []
  · iexact addCaller
  isplitl []
  · iexact onPanic
  isplitl []
  · iexact onFatal
  isplitl []
  · iexists _
    iexact name
  iexists c
  iexact clock

end proof

end EtcdGrove
end Perennial
