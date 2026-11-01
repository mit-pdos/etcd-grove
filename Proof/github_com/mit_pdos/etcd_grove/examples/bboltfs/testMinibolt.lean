/- Lean-first (no Rocq counterpart). The proof of `testMinibolt`: `Open` lays out the absent file
(transaction 1, no value, high water mark 4), with the programs' predicate `valueOkP`; the loop
keeps the committer's token at `(v - 1, v + 2)`, so each `Commit`'s bound holds and each `Get` and
`Snapshot` (with the token) reads transaction `v` holding `v`; `Close` gives the file back (the
token's high water mark is positive, so not failed), and the second `Open` and `Get` read
transaction 40 holding 40. Every error path closes the handle and returns `envFailure()`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.testMinibolt
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Open
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Close
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.valueOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.ProgramLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem testMinibolt.wp_proof (wp_Open : Open.spec (GF := GF) (hG := hG))
    (wp_Get : DB.Get.spec (GF := GF) (hG := hG))
    (wp_Snapshot : DB.Snapshot.spec (GF := GF) (hG := hG))
    (wp_Commit : DB.Commit.spec (GF := GF) (hG := hG))
    (wp_Close : DB.Close.spec (GF := GF) (hG := hG))
    (wp_envFailure : envFailure.spec (GF := GF) (hG := hG)) :
    testMinibolt.spec (GF := GF) (hG := hG) := by
  intro dir
  wp_start as ⟨#Hpkg, #Henv, #Hos, Hm⟩
  ihave Hf := dbFile_absent (dir ++ go!"/db") $$ Hm
  wp_auto
  wp_apply wp_Open (dir ++ go!"/db") 1 none 4 valueOkP (by simp [valueOkP]) $$ [Hf]
    as %db %err (⟨%Herr, %γ, %Hvp, #Hdb, #Hpath, Hown, #Hlast, #Htx, Hrds⟩ | ⟨%Herr, -⟩)
  · iframe #; iframe
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_envFailure $$ [Henv]
    · iframe #
    (try wp_auto)
    iapply HΦ
    itrivial
  subst Herr
  (try wp_auto)
  icases reader_one γ db $$ Hrds with ⟨Hrd, Hrds⟩
  ihave Hown' : dbOwnerOpt (GF := GF) γ (some (1, 4)) $$ [Hown]
  · rw [dbOwnerOpt_some]; iexact Hown
  wp_apply wp_Get γ db 1 (some (1, 4)) $$ [Hrd Hown']
    as %txid %v %has %err ⟨Hrd, Hown, Hres⟩
  · iframe; iframe #
  rw [dbOwnerOpt_some]
  icases Hres with (⟨%Hok, -, #Htx1⟩ | %Herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    ihave Hrds := Hrds $$ Hrd
    wp_apply wp_Close γ db 1 4 $$ [Hown Hrds] as %e -
    · iframe; iframe #
    (try wp_auto)
    wp_apply wp_envFailure $$ [Henv]
    · iframe #
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, Htx1⟩ := Hok
  have htx : txid = W64 1 := w64_of_toNat txid 1 (Htx1 _ rfl)
  subst htx
  icases dbTx_vp γ _ _ $$ Htx1 with %Hvp1
  rw [Hvp] at Hvp1
  have hhas : has = false := by
    cases has
    · rfl
    · simp [valueOkP] at Hvp1
  subst hhas
  (try wp_auto)
  iclear Htx1
  ihave HI : (∃ (x : w64), "v" ∷ v_ptr ↦ x ∗ "ok" ∷ ok_ptr ↦ true ∗
      "Hown" ∷ dbOwner (GF := GF) γ (x.toNat - 1) (x.toNat + 2) ∗
      "#Hlastx" ∷ dbLast (GF := GF) γ (x.toNat - 1) ∗ "%Hx" ∷ ⌜2 ≤ x.toNat ∧ x.toNat ≤ 41⌝ : IProp GF)
    $$ [v ok Hown]
  · iexists W64 2
    rw [show (W64 2 : w64).toNat = 2 from rfl]
    iframe; unfold named; iframe Hlast; ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hx40 : x.toNat ≤ 40 := by
      have : uint.Z x ≤ uint.Z (W64 40) := by simpa using Hif
      have h' : uint.Z (W64 40) = 40 := rfl
      simp only [uint.Z] at this h'; omega
    wp_apply wp_Commit γ db (x.toNat - 1) (x.toNat + 2) x (by omega) (by omega)
        (by rw [Hvp]; exact valueOkP_next x Hx.1) $$ [Hown]
      as %e (⟨%He, Hown, #Htxc, #Hlastc⟩ | ⟨%He, -, Hown⟩)
    · iframe #; iframe
    rotate_left
    · cases e with
      | nil => exact absurd rfl He
      | ok ie =>
      (try wp_auto)
      ihave Hrds := Hrds $$ Hrd
      wp_apply wp_Close γ db _ _ $$ [Hown Hrds] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      wp_apply wp_envFailure $$ [Henv]
      · iframe #
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    subst He
    (try wp_auto)
    rw [show x.toNat - 1 + 1 = x.toNat by omega]
    ihave Hown' : dbOwnerOpt (GF := GF) γ (some (x.toNat, x.toNat + 2 + 1)) $$ [Hown]
    · rw [dbOwnerOpt_some]; iexact Hown
    wp_apply wp_Get γ db x.toNat (some (x.toNat, x.toNat + 2 + 1)) $$ [Hrd Hown']
      as %txid %got %has %err ⟨Hrd, Hown, Hres⟩
    · iframe; iframe #
    rw [dbOwnerOpt_some]
    icases Hres with (⟨%Hok, -, #Htxg⟩ | %Herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      ihave Hrds := Hrds $$ Hrd
      wp_apply wp_Close γ db _ _ $$ [Hown Hrds] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      wp_apply wp_envFailure $$ [Henv]
      · iframe #
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    obtain ⟨rfl, -, Htxi⟩ := Hok
    icases dbTx_vp γ _ _ $$ Htxg with %Hvg
    obtain ⟨h1, h2, h3⟩ := read_val γ.vp Hvp x txid got has Hx.1 (Htxi _ rfl) Hvg
    subst txid; subst has; subst got
    (try wp_auto)
    ihave Hown' : dbOwnerOpt (GF := GF) γ (some (x.toNat, x.toNat + 2 + 1)) $$ [Hown]
    · rw [dbOwnerOpt_some]; iexact Hown
    wp_apply wp_Snapshot γ db x.toNat (some (x.toNat, x.toNat + 2 + 1)) $$ [Hrd Hown']
      as %stxid %sgot %shas %err ⟨Hrd, Hown, Hres⟩
    · iframe; iframe #
    rw [dbOwnerOpt_some]
    icases Hres with (⟨%Hok, -, #Htxs⟩ | %Herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      ihave Hrds := Hrds $$ Hrd
      wp_apply wp_Close γ db _ _ $$ [Hown Hrds] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      wp_apply wp_envFailure $$ [Henv]
      · iframe #
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    obtain ⟨rfl, -, Htxi⟩ := Hok
    icases dbTx_vp γ _ _ $$ Htxs with %Hvs
    obtain ⟨h1, h2, h3⟩ := read_val γ.vp Hvp x stxid sgot shas Hx.1 (Htxi _ rfl) Hvs
    subst stxid; subst shas; subst sgot
    (try wp_auto)
    wp_for_post
    have hx1 : (x + W64 1).toNat = x.toNat + 1 := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofInt]; omega
    iframe
    iexists (x + W64 1)
    rw [hx1, show x.toNat + 1 - 1 = x.toNat by omega, show x.toNat + 1 + 2 = x.toNat + 2 + 1 by omega]
    iframe; unfold named; iframe Hlastc; ipureintro; omega
  · have hx41 : x.toNat = 41 := by
      have h1 : ¬ uint.Z x ≤ uint.Z (W64 40) := by simpa using Hif
      have h' : uint.Z (W64 40) = 40 := rfl
      have h2 : uint.Z x = (x.toNat : Int) := rfl
      rw [h', h2] at h1; omega
    rw [hx41]
    ihave Hrds := Hrds $$ Hrd
    wp_apply wp_Close γ db 40 43 $$ [Hown Hrds] as %e ⟨%p, #Hp, Hres⟩
    · iframe; iframe #
    icombine Hpath Hp gives %Hpp
    subst Hpp
    icases Hres with (⟨%He, Hcl⟩ | %He | ⟨%Hbad, -⟩)
    rotate_left
    · cases e with
      | nil => exact absurd rfl He
      | ok ie =>
      (try wp_auto)
      wp_apply wp_envFailure $$ [Henv]
      · iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    · exact Hbad.elim
    subst He
    (try wp_auto)
    icases dbClosed_reopen γ _ 40 43 $$ Hcl with ⟨%vo, #Htx40, Hst⟩
    icases dbTx_vp γ _ _ $$ Htx40 with %Hv40
    rw [Hvp] at Hv40
    have hvo : vo = some (W64 40) := by simpa [valueOkP] using Hv40
    subst hvo
    ihave Hf : dbFile (GF := GF) (dir ++ go!"/db") 40 (some (W64 40)) 43 $$ [Hst]
    · unfold dbFile; iright; iexact Hst
    wp_apply wp_Open (dir ++ go!"/db") 40 (some (W64 40)) 43 valueOkP (by simp [valueOkP]) $$ [Hf]
      as %db2 %err2 (⟨%Herr2, %γ2, %Hvp2, #Hdb2, -, Hown2, #Hlast2, -, Hrds2⟩ | ⟨%Herr2, -⟩)
    · iframe #; iframe
    rotate_left
    · obtain ⟨Herr2, rfl⟩ := Herr2
      cases err2 with
      | nil => exact absurd rfl Herr2
      | ok ie =>
      (try wp_auto)
      wp_apply wp_envFailure $$ [Henv]
      · iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    subst Herr2
    (try wp_auto)
    icases reader_one γ2 db2 $$ Hrds2 with ⟨Hrd2, Hrds2⟩
    ihave Hown2' : dbOwnerOpt (GF := GF) γ2 (some (40, 43)) $$ [Hown2]
    · rw [dbOwnerOpt_some]; iexact Hown2
    wp_apply wp_Get γ2 db2 40 (some (40, 43)) $$ [Hrd2 Hown2']
      as %txid2 %got2 %has2 %err3 ⟨Hrd2, Hown2, Hres2⟩
    · iframe; iframe #
    rw [dbOwnerOpt_some]
    (try wp_auto)
    ihave Hrds2 := Hrds2 $$ Hrd2
    wp_apply wp_Close γ2 db2 40 43 $$ [Hown2 Hrds2] as %e4 -
    · iframe; iframe #
    icases Hres2 with (⟨%Hok, -, #Htxg⟩ | %Herr3)
    rotate_left
    · cases err3 with
      | nil => exact absurd rfl Herr3
      | ok ie =>
      (try wp_auto)
      wp_apply wp_envFailure $$ [Henv]
      · iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    obtain ⟨rfl, -, Htxi⟩ := Hok
    icases dbTx_vp γ2 _ _ $$ Htxg with %Hvg
    obtain ⟨h1, h2, h3⟩ := read_val γ2.vp Hvp2 (W64 40) txid2 got2 has2 (by decide) (Htxi _ rfl) Hvg
    subst txid2; subst has2; subst got2
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end bboltfs
end EtcdGrove
end Perennial
