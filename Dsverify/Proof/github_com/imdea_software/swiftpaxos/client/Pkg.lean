/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Pkg.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client package's package-level state (L2, notes/prove-s2-e.md, decision D90 R-E1;
notes/proph-swiftpaxos.md; the run's choice for `SwiftNetPkgState.client`): the prophecy patch's
`nodeProph` (made by the package's prophecy-only initializer on every node). The node's right to
claim it once, `client.ghostFresh` (`client.prophFresh client.nodeProph`: the variable's prophecy
and its ownership), is handed by the package's first initialization to the node's boot thread
(`client.freshAt`), and the package state keeps nothing (`client.pkgSt := True`). (The lab handed
it out per node kind through an exclusive address token; `Net/` has none, see
notes/dsv-swiftpaxos.md.)
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Ghost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Pkg

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **The client package's state** (see the file header): nothing. -/
def client.pkgSt : IProp GF := iprop(True)

instance client.pkgSt_persistent : Persistent (client.pkgSt (GF := GF)) := by
  unfold client.pkgSt; infer_instance

end defs

section fresh
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- What the client package's first initialization hands to a node's boot thread: the node's
right to claim its ghost (see the file header). -/
def client.freshAt (_ip : GoString) : IProp netDistGF := client.ghostFresh

end fresh

end Perennial.github_com.imdea_software.swiftpaxos
