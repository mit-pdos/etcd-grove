/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/NewClientLog.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`client.NewClientLog(server, maddr, mport, true, false, verbose, lg)` (the adapter's `connect`:
SwiftPaxos's client of the master at `maddr:mport`, fast, not leaderless, with a quiet logger).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions]

/-- A fresh client (not connected; its id the uuid model's `ID()`, which the adapter replaces:
`client.fresh_setId`). -/
abbrev client.NewClientLog.spec : Prop :=
  ∀ (server maddr : GoString) (mport : w64) (verbose : Bool) (lg : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      dlog.quiet lg }}
    (App (App (App (App (App (App (App (Val (@! client.NewClientLog)) (Val #server))
      (Val #maddr)) (Val #mport)) (Val #true)) (Val #false)) (Val #verbose)) (Val #lg))
  {{ (cl : Loc), RET #cl; ∃ cid : w32, client.fresh cl cid maddr mport }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
