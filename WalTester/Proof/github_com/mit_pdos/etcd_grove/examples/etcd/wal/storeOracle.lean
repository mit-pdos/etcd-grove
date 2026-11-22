/-
`storeOracle.wp_proof` (W4c U5): `encodeOracle`, then `durable.Write` with its two updates committed on
the tester's invariant (`TInv`): the rename's (`tOracleFile_write`: the file holds the new oracle, the
old one pending, both related to the unchanged WAL state), the directory sync's (`tOracleFile_sync`).
Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.encodeOracle
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.PkgInit

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

/-- The tester's invariant is in durable's updates' mask. -/
theorem tN_sub_durAu : (↑tN : CoPset) ⊆ DurFs.durAuMask := by
  have h1 : (↑tN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  have h2 : (↑tN : CoPset) ## ↑osShN := ndot_ne_disjoint nroot (by decide)
  have h3 : (↑tN : CoPset) ## ↑DurFs.durN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨LawfulSet.mem_diff.2 ⟨LawfulSet.mem_diff.2
    ⟨CoPset.mem_full, fun hn => h1 p ⟨hp, hn⟩⟩, fun hn => h2 p ⟨hp, hn⟩⟩, fun hn => h3 p ⟨hp, hn⟩⟩

theorem storeOracle.wp_proof
    (wp_enc : encodeOracle.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG)) :
    storeOracle.spec (GF := GF) (hG := hG) := by
  intro W e γ v o o' od qc hf hs
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Hrep, Ho, Hw, #Hrel⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  wp_auto
  wp_apply wp_enc $$ [$Hrep] as Hrep
  icases Hdeps with ⟨#Hdpkg, -⟩
  rw [show tOrPath e.orDir = e.orFile.name from (tOrPath_child e.orDir).symm]
  ihave Hperm := osCallPerm_congr qc (show callKey e.R e.orDir = callKey e.R e.orFile.d from rfl) $$ Hperm
  wp_apply (wp_Write γ.γd e.orFile e.R qc (tEncodeOracle o') hf
    (by unfold tOrSmall at hs; omega)) $$ Hdpkg Hos Hsi Hdi Hh Hperm
    [Ho Hw Hrep HΦ]
  · iauintro
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
      iunfold tWalOwn at Hw
      ihave %hw := ghostVar_agree γ.γw od (1 : Qp).half od1 (1 : Qp).half $$ Hw Hw1
      subst hw
      iunfold tOrOwn at Ho
      imod ghostVar_update_halves (o', some o1) γ.γo _ _ $$ Ho Ho1 with ⟨Ho, Ho1⟩
      imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
      · inext; iunfold TInvBody
        iexists ⟨some (tEncodeOracle o'), some s.cur⟩, o', some o1, od
        iframe Hs Ho1 Hwd Hw1 Hrel
        isplitr
        · ipureintro; exact tOracleFile_write hfile hs
        · iunfold tRelA; iexact Hr1
      imodintro
      -- the directory's sync: nothing pending
      iapply DurFs.durWriteSync_of_au
      iauintro
      unfold atomic_acc
      imod inv_acc (E := DurFs.durAuMask) tN_sub_durAu $$ Hinv with ⟨Hi, Hclose⟩
      imod Hi
      iunfold TInvBody at Hi
      icases Hi with ⟨%s2, %o2, %oa2, %od2, Hs, %hfile2, Ho2, Hwd, Hw2, #Hr2, #Ha2⟩
      ihave %hag2 := ghostVar_agree γ.γo (o', some o1) (1 : Qp).half (o2, oa2) (1 : Qp).half $$ Ho Ho2
      cases hag2
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑tN from LawfulSet.empty_subset)
      iintro Hclose2
      isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
      iexists s2
      iframe Hs
      isplit
      · iintro Hs
        imod Hclose2 with -
        imod Hclose $$ [Hs Ho2 Hwd Hw2] with -
        · inext; iunfold TInvBody; iexists s2, o', some o1, od2; iframe; iframe #; ipureintro; exact hfile2
        imodintro
        iframe
      · iintro Hs
        imod Hclose2 with -
        imod ghostVar_update_halves (o', (none : Option TOracle)) γ.γo _ _ $$ Ho Ho2 with ⟨Ho, Ho2⟩
        imod Hclose $$ [Hs Ho2 Hwd Hw2] with -
        · inext; iunfold TInvBody
          iexists ⟨s2.cur, none⟩, o', none, od2
          iframe Hs Ho2 Hwd Hw2 Hr2
          isplitr
          · ipureintro; exact tOracleFile_sync hfile2
          · iunfold tRelA; iempintro
        imodintro
        iintro Hh Hperm
        ihave Hperm := osCallPerm_congr qc (show callKey e.R e.orFile.d = callKey e.R e.orDir from rfl) $$ Hperm
        wp_auto
        iapply HΦ
        unfold tOrOwn tWalOwn
        iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
