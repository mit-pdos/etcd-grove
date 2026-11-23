/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/master/New.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`master.New(N, port, conf, lg)` (the adapter's `serve` on node 1, `N` the configuration's).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions]

/-- The master, created (`master.created`: with the membership's writer token). -/
abbrev master.New.spec : Prop :=
  ∀ (N port : w64) (cfgp lg : Loc) (γc γm : GName) (c : Conf) (fr : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      confIs γc c ∗ ⌜uint.nat N = c.n⌝ ∗ monoListAuthOwn (A := List GoString) γm 1 [] ∗
      config.plain cfgp fr ∗ dlog.quiet lg }}
    (App (App (App (App (Val (@! master.New)) (Val #N)) (Val #port)) (Val #cfgp)) (Val #lg))
  {{ (m : Loc), RET #m; master.created m γc γm (uint.nat N) port }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
