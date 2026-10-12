/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/idutil/NewGenerator.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.NewGenerator
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.lowbit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

/-- The `n` low bits of `x`, as a number. -/
private theorem mask_toNat (x : BitVec 64) (n : Nat) (h : n ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ n - 1)).toNat = x.toNat % 2 ^ n := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : 2 ^ n - 1 < 2 ^ 64 := by
    have : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]

theorem idutil_prefix_low (y : BitVec 64) : y <<< 48#64 &&& 0xffffffffffff#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := mask_toNat (y <<< 48#64) 48 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 48 - 1)) = 0xffffffffffff#64 from rfl] at this
  rw [this, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  rw [show 48 % 2 ^ 64 = 48 from rfl, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.mul_mod_left]

theorem idutil_suffix_lt (x : BitVec 64) : (x &&& 0xffffffffff#64) <<< 8#64 < 0x1000000000000#64 := by
  rw [BitVec.lt_def, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have := mask_toNat x 40 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 40 - 1)) = 0xffffffffff#64 from rfl] at this
  rw [this, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, show 8 % 2 ^ 64 = 8 from rfl]
  have : x.toNat % 2 ^ 40 < 2 ^ 40 := Nat.mod_lt _ (by omega)
  omega

theorem idutil.NewGenerator.wp_proof (hL : idutil.lowbit.spec (GF := GF) (hG := hG)) :
    idutil.NewGenerator.spec (GF := GF) (hG := hG) := by
  intro memberID now
  wp_start as -
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply time.Time.wp_UnixNano as %ns -
  wp_apply hL _ (W64 40) (by word)
  wp_alloc gp as Hgp
  ihave ⟨Hgp, %Hgpn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hgp
  iStructNamed Hgp
  ipersist prefix'
  generalize hs0 : ((ns / BitVec.sdiv (W64 1000000) (W64 1) &&& W64 (2 ^ 40 - 1)) <<< W64 8) = s0
  have Hs0 : uint.Z s0 < 2 ^ 48 := by
    have h' : s0 < 0x1000000000000#64 := by rw [← hs0]; exact idutil_suffix_lt _
    rw [BitVec.lt_def] at h'
    simp [uint.Z]; simp at h'; omega
  have Hpl : W64 (uint.Z memberID) <<< W64 48 &&& W64 (2 ^ 48 - 1) = W64 0 :=
    idutil_prefix_low _
  obtain ⟨N, hN⟩ : ∃ N : Nat, N = 2 ^ 48 - 1 := ⟨_, rfl⟩
  imod own_alloc ((● N : Auth Nat) • ◯ N)
    (Auth.auth_both_valid_discrete.mpr ⟨⟨0, (Nat.add_zero _).symm⟩, trivial⟩) with ⟨%γc, HC⟩
  icases (own_op γc _ _).1 $$ HC with ⟨HCa, HCf⟩
  subst hN
  imod (ghost_map_alloc_empty (K := w64) (V := Option (List w8))) with ⟨%γI, HI⟩
  imod (ghost_map_alloc_empty (K := w64) (V := Unit)) with ⟨%γS, HS⟩
  imod inv_alloc idN ⊤ iprop(∃ (k : Nat) (I : GMap w64 (Option (List w8))) (S : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" gp ↦
        (s0 + W64 (k : Int)) ∗
      own (⟨γc, γI, γS⟩ : IdNames).cred (● (2 ^ 48 - 1 - k) : Auth Nat) ∗ ⌜k ≤ 2 ^ 48 - 1⌝ ∗
      ghostMapAuth (⟨γc, γI, γS⟩ : IdNames).issued 1 I ∗
      ghostMapAuth (⟨γc, γI, γS⟩ : IdNames).slot 1 S ∗
      ⌜∀ id, ((I !! id).isSome ↔ idIssued (W64 (uint.Z memberID) <<< W64 48) s0 k id) ∧
        ((S !! id).isSome ↔ idIssued (W64 (uint.Z memberID) <<< W64 48) s0 k id)⌝)
    $$ [suffix HCa HI HS] with #Hinv
  · inext
    iexists 0, ∅, ∅
    rw [show s0 + W64 ((0 : Nat) : Int) = s0 by word]
    iframe suffix HI HS HCa
    ipureintro
    refine ⟨by omega, fun id => ⟨?_, ?_⟩⟩ <;>
      (simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff];
       rintro ⟨j, h1, h2, -⟩; omega)
  wp_auto
  iapply HΦ
  iexists ⟨γc, γI, γS⟩
  iunfold idCred
  iframe HCf
  iunfold idGen
  iexists (W64 (uint.Z memberID) <<< W64 48), s0
  iframe prefix' Hinv
  ipureintro
  exact ⟨Hgpn, Hs0, Hpl⟩

end proof

end EtcdGrove
end Perennial
