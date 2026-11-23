/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ChecksumPath.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The checksum laws of `Spec/swift/Inv.lean`: since change log C9 proved in place
(Spec/swift/Hash.lean: `checksum_path_eq`, `checksum_deps_perm`). `checksum_deps_bounded` is kept
as an alias.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ChainHash

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-- `sp.checksum_deps`, with the dependency lists shorter than `2^32`. -/
theorem checksum_deps_bounded (Ps1 Ps2 : List (List CmdId)) (D1 D2 : List CmdId)
    (cs1 cs2 : List Hash) (hb : D1.length < 2 ^ 32 ∧ D2.length < 2 ^ 32) :
    checksum Ps1 D1 cs1 ∗ checksum Ps2 D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ⊢ ⌜D1.Perm D2⌝ :=
  checksum_deps_perm Ps1 Ps2 D1 D2 cs1 cs2 hb

end ghost

end sp

end Perennial.github_com.imdea_software.swiftpaxos
