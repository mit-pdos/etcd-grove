/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/logger/InitLogger.lean`, run `rabia-r1wake-1`.)

The proof of `InitLogger` (`InitLogger.spec`): `SetGlobalLevel(GetLogLevel())` (`Conf.LogLevel`
is `"warn"`: `confRO`), then `zerolog.New(nil)`.
-/
module

public import Dsverify.Proof.rabia.internal.logger.Spec
public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.logger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.logger.Assumptions]
variable [github_com.rs.zerolog.Assumptions] [github_com.rs.zerolog.Hyps GF]

theorem InitLogger.wp_proof : InitLogger.spec (GF := GF) := by
  intro cf component svrId subId loggerType
  wp_start as #HRO
  unfold confRO
  icases HRO with ⟨-, %ps, #HConf, #Hps⟩
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  iStructNamed HConf
  wp_auto
  simp only [confVal]
  wp_apply (github_com.rs.zerolog.Hyps.ParseLevel_warn (GF := GF))
  wp_apply (github_com.rs.zerolog.Hyps.SetGlobalLevel (GF := GF))
  wp_apply (github_com.rs.zerolog.Hyps.New (GF := GF)) as %lg #Hok
  iapply HΦ
  iexact Hok

end proof

end Perennial.rabia.internal.logger
