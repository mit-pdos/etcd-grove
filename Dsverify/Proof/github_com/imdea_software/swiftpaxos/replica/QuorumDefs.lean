/-
The definitions, specs and lemmas of `Quorum.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions]

abbrev NewMajorityOf.specI : Prop :=
  ∀ (N : Nat), N < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica }}
    (App (Val (@! replica.NewMajorityOf)) (Val #(W64 N)))
  {{ RET #(W64 ((N / 2 + 1 : Nat) : Int)); True }}

abbrev NewThreeQuartersOf.specI : Prop :=
  ∀ (N : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica }}
    (App (Val (@! replica.NewThreeQuartersOf)) (Val #N))
  {{ (q : w64), RET #q; True }}

set_option goose.wp.extras true

end proof

end replica.quorum

end Perennial.github_com.imdea_software.swiftpaxos
