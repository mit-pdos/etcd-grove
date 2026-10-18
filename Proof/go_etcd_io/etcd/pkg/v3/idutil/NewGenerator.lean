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

theorem idutil_prefix_low (y : BitVec 64) : y <<< 48#64 &&& 0xffffffffffff#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := idutil_mask_toNat (y <<< 48#64) 48 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 48 - 1)) = 0xffffffffffff#64 from rfl] at this
  rw [this, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  rw [show 48 % 2 ^ 64 = 48 from rfl, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.mul_mod_left]

theorem idutil_suffix_lt (x : BitVec 64) : (x &&& 0xffffffffff#64) <<< 8#64 < 0x1000000000000#64 := by
  rw [BitVec.lt_def, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have := idutil_mask_toNat x 40 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 40 - 1)) = 0xffffffffff#64 from rfl] at this
  rw [this, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, show 8 % 2 ^ 64 = 8 from rfl]
  have : x.toNat % 2 ^ 40 < 2 ^ 40 := Nat.mod_lt _ (by omega)
  omega

theorem idutil.NewGenerator.wp_proof (hL : idutil.lowbit.spec (GF := GF) (hG := hG)) :
    idutil.NewGenerator.spec (GF := GF) (hG := hG) := by
  intro γi memberID now Φc
  wp_start as Hfresh
  iunfold idNamesFresh at Hfresh
  icases Hfresh with ⟨HI, HS⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply time.Time.wp_ptr_UnixNano now_ptr now $$ [$now] as %ns now
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
  obtain ⟨γI, γS⟩ := γi
  imod receipt_zero (GF := GF) with HCa
  imod inv_alloc idN ⊤ iprop(∃ (k : Nat) (I : GMap w64 (Option (List w8 × GName))) (S : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" gp ↦
        (s0 + W64 (k : Int)) ∗
      ⧗ k ∗
      ghostMapAuth (⟨γI, γS⟩ : IdNames).issued 1 I ∗
      ghostMapAuth (⟨γI, γS⟩ : IdNames).slot 1 S ∗
      ⌜∀ id, ((I !! id).isSome ↔ idIssued (W64 (uint.Z memberID) <<< W64 48) s0 k id) ∧
        ((S !! id).isSome ↔ idIssued (W64 (uint.Z memberID) <<< W64 48) s0 k id)⌝ ∗
      idClaimsFacts Φc I)
    $$ [suffix HCa HI HS] with #Hinv
  · inext
    iexists 0, ∅, ∅
    rw [show s0 + W64 ((0 : Nat) : Int) = s0 by word]
    iframe suffix HI HS HCa
    isplitr
    · ipureintro
      refine fun id => ⟨?_, ?_⟩ <;>
        (simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff];
         rintro ⟨j, h1, h2, -⟩; omega)
    iunfold idClaimsFacts
    iapply BigSepM.bigSepM_empty.2
    itrivial
  wp_auto
  iapply HΦ
  iunfold idGen
  iexists (W64 (uint.Z memberID) <<< W64 48), s0
  iframe prefix' Hinv
  ipureintro
  exact ⟨Hgpn, Hs0, Hpl⟩

end proof

end EtcdGrove
end Perennial
