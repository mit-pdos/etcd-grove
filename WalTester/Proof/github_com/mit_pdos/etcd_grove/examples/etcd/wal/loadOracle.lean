/-
`loadOracle.wp_proof` (W4c U5): `durable.Read` with its update committed on the tester's invariant
(`TInv`) unchanged, learning that the file holds the program's oracle (`tOracleFile`'s `cur`); then
`decodeOracle` of its encoding, or `freshOracle` when there is no file. Lean-first (no Rocq
counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.loadOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decodeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.freshOracle
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]
variable [durable_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

theorem loadOracle.wp_proof
    (wp_dec : decodeOracle.spec (GF := GF) (hG := hG))
    (wp_fresh : freshOracle.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG)) :
    loadOracle.spec (GF := GF) (hG := hG) := by
  intro W e γ o qc hf
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Ho⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨#Hdpkg, -⟩
  wp_auto
  rw [show tOrPath e.root = e.orFile.name from (tOrPath_child e.root).symm]
  wp_apply (wp_Read γ.γd e.orFile e.R qc hf) $$ Hdpkg Hos Hsi Hdi Hh Hperm [-Hpkg]
  iauintro
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := DurFs.durAuMask) tN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o1, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tOrOwn_agree γ o o1 none oa $$ Ho Ho1
  obtain ⟨rfl, rfl⟩ := hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists s
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, none, od1; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iframe
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o1, none, od1; iframe; iframe #; ipureintro; exact hfile
    imodintro
    iintro Hh Hperm
    rcases hfile.1 with ⟨hc, hsm⟩ | ⟨hc, hfr⟩
    · rw [hc]
      simp only [DurFs.readRes, Option.getD_some, Option.isSome_some]
      wp_auto
      wp_apply (wp_dec o1 hsm) as %v Hrep
      iapply HΦ
      iframe
    · rw [hc]
      simp only [DurFs.readRes, Option.getD_none, Option.isSome_none]
      wp_auto
      wp_apply wp_fresh as %v Hrep
      iapply HΦ
      rw [hfr]
      iframe
end proof

end etcd_wal
end EtcdGrove
end Perennial
