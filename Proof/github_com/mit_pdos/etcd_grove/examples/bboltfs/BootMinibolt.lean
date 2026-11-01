/- Lean-first (no Rocq counterpart). One generation of `BootMinibolt(dir)` (`minibolt.go`): from
the database file as the generation starts with it (`csOwn (dir ++ "/db") γc (csStart fo)`, a
`Good` file, in its crash invariant), `BootMinibolt` reaches no panic. It is proved over the
crash-aware specs of `Open`, `Get`, `Commit` and `Close` (hypotheses, as the other proofs take
their callees' specs).

`Open` opens at `freshTx`'s transaction `t` (value `vo`, high water mark `n`) with the client's
predicate `bootOk` (`CrashGood.lean`), which is `BootMinibolt`'s first check: the first `Get`, with
the committer's token, reads transaction `t` and its value, which `dbTx` says is `bootOk`. Then
`Commit(t + 1)`, and the second `Get` reads transaction `t + 1` (the token), whose value is again
`bootOk`'s, `t + 1` since `t + 1 > 1`.

**What `Commit` needs:** `t + 1 < 2 ^ 64`, and its value `t + 1` must satisfy `bootOk (t + 1)`,
which needs `1 ≤ t`. A `Good` file gives `1 ≤ t < n` (`goodImg_freshTx_tx`: `txOk`), so both. When
the high water mark reaches 1 GiB, `commit` refuses with `errMapTooLarge` (the file would pass
`maxMapSize`); `Commit` then fails the handle, and `BootMinibolt` closes it and returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.OpenCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__GetCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__CommitCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__CloseCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.ProgramLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- `bootOk`'s first check: transaction `t ≤ 1` holds no value. -/
theorem bootOk_le1 {t : Nat} {vo : Option w64} (h : bootOk t vo) (ht : t ≤ 1) : vo = none := by
  rcases h with h | h
  · exact h.2
  · omega

/-- `bootOk`'s second check: transaction `t > 1` holds `t`. -/
theorem bootOk_gt1 {t : Nat} {vo : Option w64} (h : bootOk t vo) (ht : 1 < t) :
    vo = some (W64 t) := by
  rcases h with h | h
  · omega
  · exact h.2

theorem w64_add1_toNat (x : w64) (h : x.toNat + 1 < 2 ^ 64) : (x + W64 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofInt]; omega

/-- `Commit`'s value `t + 1` at transaction `t + 1` is `bootOk`. -/
theorem bootOk_next (x : w64) (h1 : 1 ≤ x.toNat) (h : x.toNat + 1 < 2 ^ 64) :
    bootOk (x.toNat + 1) (some (x + W64 1)) := by
  refine Or.inr ⟨by omega, ?_⟩
  congr 1

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- **One generation of `BootMinibolt(dir)`** (see the file header): no panic. -/
theorem wp_BootMinibolt [ThreadBoundLe GF (2 ^ 30)]
    (wp_Open : Open.specCrash (GF := GF) (hG := hG))
    (wp_Get : DB.Get.specCrash (GF := GF) (hG := hG))
    (wp_Commit : DB.Commit.specCrash (GF := GF) (hG := hG))
    (wp_Close : DB.Close.specCrash (GF := GF) (hG := hG))
    (dir : GoString) (γc : GName) (fo : Option OsFile) (hg : Good fo) :
    {{ pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗
        csInv (GF := GF) dbCrashN (dir ++ go!"/db") γc (dbOk (dir ++ go!"/db")) ∗
        csOwn (GF := GF) (dir ++ go!"/db") γc (csStart fo) ∗ threadTok }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.BootMinibolt)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpkg, #Hos, #Hci, Hown, Htok⟩
  obtain ⟨t, vo, n, hfresh⟩ : ∃ t vo n, freshTx ((startImg fo).map (·, true)) = (t, vo, n) :=
    ⟨_, _, _, rfl⟩
  have hgi : goodImg (startImg fo) := by cases fo with
    | none => exact ⟨by simp [startImg], Or.inl ⟨by simp [startImg], fun i _ h => by simp [startImg] at h⟩⟩
    | some f => exact hg
  have hvp : bootOk t vo := by
    have := goodImg_freshTx (startImg fo) hgi
    rw [hfresh] at this; exact this
  have hb' : 1 ≤ t ∧ t + 1 < 2 ^ 64 := by
    have htx := goodImg_freshTx_tx (startImg fo) hgi
    rw [hfresh] at htx
    exact ⟨htx.1, by omega⟩
  wp_auto
  wp_apply wp_Open (dir ++ go!"/db") γc fo t vo n bootOk hg hfresh hvp (fun _ _ h => h) $$ [Hown]
    as %db %err (⟨%Herr, %γ, %Hvp, #Hdb, -, Hown, #Hlast, #Htx⟩ | ⟨%Herr, -⟩)
  · iframe; iframe #
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  subst Herr
  (try wp_auto)
  ihave Hown' : dbOwnerOpt (GF := GF) γ (some (t, n)) $$ [Hown]
  · rw [dbOwnerOpt_some]; iexact Hown
  wp_apply wp_Get γ γc db t (some (t, n)) $$ [Htok Hown']
    as %txid %v %has %err ⟨Htok, Hown, Hres⟩
  · iframe; iframe #
  rw [dbOwnerOpt_some]
  icases Hres with (⟨%Hok, -, #Htx1⟩ | %Herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close γ γc db t n $$ [Hown] as %e -
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, Htx1⟩ := Hok
  have htx : txid.toNat = t := Htx1 _ rfl
  icases dbTx_vp γ _ _ $$ Htx1 with %Hvp1
  rw [Hvp] at Hvp1
  (try wp_auto)
  have hZ : uint.Z txid = (txid.toNat : Int) := rfl
  have hZ1 : uint.Z (W64 1) = 1 := rfl
  wp_if_destruct
  · have ht1 : txid.toNat ≤ 1 := by
      have : uint.Z txid ≤ uint.Z (W64 1) := by simpa using Hif
      rw [hZ, hZ1] at this; omega
    have hn := bootOk_le1 Hvp1 ht1
    have hhas : has = false := by cases has <;> simp_all
    subst hhas
    (try wp_auto)
    wp_apply wp_Commit γ γc db t n (txid + W64 1) (by omega)
        (by rw [Hvp, ← htx]; exact bootOk_next txid (by omega) (by omega)) $$ [Hown]
      as %e (⟨%He, Hown, #Htxc, #Hlastc⟩ | ⟨%He, -, Hown⟩)
    · iframe; iframe #
    rotate_left
    · cases e with
      | nil => exact absurd rfl He
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close γ γc db _ _ $$ [Hown] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    subst He
    (try wp_auto)
    ihave Hown' : dbOwnerOpt (GF := GF) γ (some (t + 1, n + 1)) $$ [Hown]
    · rw [dbOwnerOpt_some]; iexact Hown
    wp_apply wp_Get γ γc db (t + 1) (some (t + 1, n + 1)) $$ [Htok Hown']
      as %txid2 %v2 %has2 %err2 ⟨Htok, Hown, Hres⟩
    · iframe; iframe #
    rw [dbOwnerOpt_some]
    icases Hres with (⟨%Hok, -, #Htx2⟩ | %Herr)
    rotate_left
    · cases err2 with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close γ γc db _ _ $$ [Hown] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    obtain ⟨rfl, -, Htxi⟩ := Hok
    have htx2 : txid2.toNat = t + 1 := Htxi _ rfl
    icases dbTx_vp γ _ _ $$ Htx2 with %Hvp2
    rw [Hvp, htx2] at Hvp2
    have hs2 := bootOk_gt1 Hvp2 (by omega)
    have hhas2 : has2 = true := by cases has2 <;> simp_all
    subst hhas2
    have htx2' : txid2 = txid + W64 1 :=
      BitVec.eq_of_toNat_eq (by rw [htx2, w64_add1_toNat txid (by omega), htx])
    have hv2 : v2 = txid2 := by
      simp only [ite_true, Option.some.injEq] at hs2
      exact hs2.trans (w64_of_toNat txid2 _ htx2).symm
    subst v2
    subst htx2'
    (try wp_auto)
    wp_apply wp_Close γ γc db _ _ $$ [Hown] as %e2 -
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial
  · have ht1 : 1 < txid.toNat := by
      have : ¬ uint.Z txid ≤ uint.Z (W64 1) := by simpa using Hif
      rw [hZ, hZ1] at this; omega
    have hs := bootOk_gt1 Hvp1 ht1
    have hhas : has = true := by cases has <;> simp_all
    subst hhas
    have hv : v = txid := by
      simp only [ite_true, Option.some.injEq] at hs
      rw [hs]; exact (w64_of_toNat txid _ rfl).symm
    subst v
    (try wp_auto)
    wp_apply wp_Commit γ γc db t n (txid + W64 1) (by omega)
        (by rw [Hvp, ← htx]; exact bootOk_next txid (by omega) (by omega)) $$ [Hown]
      as %e (⟨%He, Hown, #Htxc, #Hlastc⟩ | ⟨%He, -, Hown⟩)
    · iframe; iframe #
    rotate_left
    · cases e with
      | nil => exact absurd rfl He
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close γ γc db _ _ $$ [Hown] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    subst He
    (try wp_auto)
    ihave Hown' : dbOwnerOpt (GF := GF) γ (some (t + 1, n + 1)) $$ [Hown]
    · rw [dbOwnerOpt_some]; iexact Hown
    wp_apply wp_Get γ γc db (t + 1) (some (t + 1, n + 1)) $$ [Htok Hown']
      as %txid2 %v2 %has2 %err2 ⟨Htok, Hown, Hres⟩
    · iframe; iframe #
    rw [dbOwnerOpt_some]
    icases Hres with (⟨%Hok, -, #Htx2⟩ | %Herr)
    rotate_left
    · cases err2 with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close γ γc db _ _ $$ [Hown] as %e2 -
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    obtain ⟨rfl, -, Htxi⟩ := Hok
    have htx2 : txid2.toNat = t + 1 := Htxi _ rfl
    icases dbTx_vp γ _ _ $$ Htx2 with %Hvp2
    rw [Hvp, htx2] at Hvp2
    have hs2 := bootOk_gt1 Hvp2 (by omega)
    have hhas2 : has2 = true := by cases has2 <;> simp_all
    subst hhas2
    have htx2' : txid2 = txid + W64 1 :=
      BitVec.eq_of_toNat_eq (by rw [htx2, w64_add1_toNat txid (by omega), htx])
    have hv2 : v2 = txid2 := by
      simp only [ite_true, Option.some.injEq] at hs2
      exact hs2.trans (w64_of_toNat txid2 _ htx2).symm
    subst v2
    subst htx2'
    (try wp_auto)
    wp_apply wp_Close γ γc db _ _ $$ [Hown] as %e2 -
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end bboltfs
end EtcdGrove
end Perennial
