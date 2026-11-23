/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/pkg/TimeInit.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`time`'s package initialization from a package that imports `time` (Perennial 3afd77e35:
`time.wp_Now` needs `isPkgInit pkg_id.time`, kit/CHANGES.md item 2). Each lemma unfolds the
package's dependency part (`isPkgInit_unfold_deps`: `isPkgInit dep1 ∗ ... ∗ True`, in
`pkgImportedPkgs`' order) and takes `time`'s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF]

theorem client.time_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.client ⊢
      isPkgInit (PROP := IProp GF) pkg_id.time := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) _).trans ?_
  show iprop(_ ∗ _ ∗ _ ∗ _ ∗ isPkgInit (PROP := IProp GF) pkg_id.time ∗ _) ⊢ _
  iintro ⟨-, -, -, -, #H, -⟩; iexact H

theorem replica.time_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica ⊢
      isPkgInit (PROP := IProp GF) pkg_id.time := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) _).trans ?_
  show iprop(_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗
    isPkgInit (PROP := IProp GF) pkg_id.time ∗ _) ⊢ _
  iintro ⟨-, -, -, -, -, -, -, -, -, -, -, #H, -⟩; iexact H

theorem swift.time_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
      isPkgInit (PROP := IProp GF) pkg_id.time := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) _).trans ?_
  show iprop(_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗
    isPkgInit (PROP := IProp GF) pkg_id.time ∗ _) ⊢ _
  iintro ⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩; iexact H

theorem master.time_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.master ⊢
      isPkgInit (PROP := IProp GF) pkg_id.time := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) _).trans ?_
  show iprop(_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ isPkgInit (PROP := IProp GF) pkg_id.time ∗ _) ⊢ _
  iintro ⟨-, -, -, -, -, -, #H, -⟩; iexact H

end

end Perennial.github_com.imdea_software.swiftpaxos
