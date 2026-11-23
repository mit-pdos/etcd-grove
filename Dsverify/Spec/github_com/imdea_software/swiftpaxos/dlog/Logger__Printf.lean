/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/dlog/Logger__Printf.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`l.Printf(...)` on a non-verbose logger: prints nothing, returns.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [dlog.Assumptions]

/-- `l.Printf(...)`: with a non-verbose logger, a no-op (any arguments). -/
abbrev dlog.Logger.Printf.spec : Prop :=
  ∀ (l : Loc) (fmt : GoString) (sl : GoSlice),
  {{ dlog.quiet (GF := GF) l }}
    (App (App (Val (l @!! go.GoType.PointerType dlog.Logger.ty @!! go!"Printf")) (Val #fmt)) (Val #sl))
  {{ RET #(); True }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
