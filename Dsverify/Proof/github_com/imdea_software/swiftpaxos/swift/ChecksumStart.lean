/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ChecksumStart.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The checksums as the code computes them since F2's fix (start-marked path hashes): since change
log C9 these are `Spec/swift/Inv.lean`'s (Spec/swift/Hash.lean) `pathHashes`/`checksum`. The
names of the proposal are kept as aliases.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ChecksumPath

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

abbrev pathHashesS (Ps : List (List CmdId)) (hs : List Hash) : IProp netDistGF := pathHashes Ps hs

abbrev checksumS (Ps : List (List CmdId)) (D : List CmdId) (cs : List Hash) : IProp netDistGF :=
  checksum Ps D cs

/-- **Equal single-path checksums are of equal paths.** -/
theorem checksumS_path (P1 P2 D1 D2 : List CmdId) (cs1 cs2 : List Hash) :
    checksumS [P1] D1 cs1 ∗ checksumS [P2] D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ⊢ ⌜P1 = P2⌝ :=
  checksum_path_eq P1 P2 D1 D2 cs1 cs2

/-- **Equal checksums have the same dependencies** (lengths < 2^32). -/
theorem checksumS_deps_bounded (Ps1 Ps2 : List (List CmdId)) (D1 D2 : List CmdId)
    (cs1 cs2 : List Hash) (hb : D1.length < 2 ^ 32 ∧ D2.length < 2 ^ 32) :
    checksumS Ps1 D1 cs1 ∗ checksumS Ps2 D2 cs2 ∗ ⌜shashesEq cs1 cs2⌝ ⊢ ⌜D1.Perm D2⌝ :=
  checksum_deps_perm Ps1 Ps2 D1 D2 cs1 cs2 hb

end ghost

end sp

end Perennial.github_com.imdea_software.swiftpaxos
