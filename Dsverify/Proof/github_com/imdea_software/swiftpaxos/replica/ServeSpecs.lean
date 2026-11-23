/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ServeSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.WaitForClientConnections()` (`replica/replica.go`): internal spec.

The clients accepted while waiting for the peers (`serveSt`'s pending clients) each get a
`clientListener`; then `pendingClients` is emptied and every connection accepted on the
replica's listener gets one too. The loop runs while `!r.Shutdown` (`Shutdown ↦□ false`): it
never returns.

Its proof takes `clientListener.spec` (ClientSpecs.lean) as a hypothesis.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClientSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- `r.WaitForClientConnections()` (see the file header). -/
abbrev replica.Replica.WaitForClientConnections.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (a : GoString),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.strings ∗
      replica.isReplica r γ γc γm γw N me ∗ replica.serveSt r γ γc γm a }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"WaitForClientConnections"))
      (Val #()))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
