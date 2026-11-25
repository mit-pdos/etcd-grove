/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/logger/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/internal/logger`'s spec (interface, stage 1a): `InitLogger` (G4: a logger that writes
nothing, no file).
-/
module

public import Dsverify.GeneratedProof.rabia.internal.logger
public import Dsverify.Proof.rabia.internal.config.Spec
public import Dsverify.Proof.rabia.internal.logger.Base
public import Dsverify.Proof.github_com.rs.zerolog.Spec



@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.logger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode rabia.internal.config

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.logger.Assumptions]

/-- `InitLogger(component, svrId, subId, loggerType)`: a logger made by `zerolog.New(nil)`
(`loggerOk lg`) and no file (`nil`). -/
abbrev InitLogger.spec : Prop :=
  ∀ (cf : model.RCfg) (component : GoString) (svrId subId : w32) (loggerType : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.logger ∗ confRO cf }}
    (App (App (App (App (Val (@! InitLogger)) (Val #component)) (Val #svrId)) (Val #subId))
      (Val #loggerType))
  {{ (lg : github_com.rs.zerolog.Logger), RET (PairV #lg #(null : Loc));
      github_com.rs.zerolog.loggerOk lg }}

end spec

end Perennial.rabia.internal.logger
