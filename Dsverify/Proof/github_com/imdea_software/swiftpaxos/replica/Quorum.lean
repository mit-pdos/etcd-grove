/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Quorum.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica.NewMajorityOf(N)` and `replica.NewThreeQuartersOf(N)` (replica/quorum.go), the client's
quorums (`swift.NewClient`): `N / 2 + 1`, and some size (overwritten by `NewClient`'s
`fixedMajority` step). Internal specs of the replica package, proved from its code.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
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

theorem NewMajorityOf.wp_proof : NewMajorityOf.specI (hG := hG) := by
  intro N hN
  wp_start
  wp_auto
  rw [show BitVec.sdiv (W64 (N : Int)) (W64 2) + W64 1 = W64 ((N / 2 + 1 : Nat) : Int) by
    have h1 : (W64 (N : Int)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp [W64]; omega
    rw [BitVec.sdiv_eq, h1]
    simp only [show (W64 2).msb = false from rfl]
    apply BitVec.eq_of_toNat_eq
    simp [W64, BitVec.toNat_udiv]
    omega]
  iapply HΦ; itrivial

theorem NewThreeQuartersOf.wp_proof : NewThreeQuartersOf.specI (hG := hG) := by
  intro N
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end replica.quorum

end Perennial.github_com.imdea_software.swiftpaxos
