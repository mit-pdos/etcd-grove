/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/idutil/Generator__Next.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Generator__Next
public import Spec.go_etcd_io.etcd.pkg.v3.idutil.lowbit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

/-- The `n` low bits of `x`, as a number. -/
private theorem mask_toNat (x : BitVec 64) (n : Nat) (h : n ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ n - 1)).toNat = x.toNat % 2 ^ n := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : 2 ^ n - 1 < 2 ^ 64 := by
    have : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]

/-- The 48 low bits of distinct suffixes below `2 ^ 48` apart, under a prefix with no low bits,
give distinct ids. -/
theorem idutil_id_inj (pfx s0 a b : BitVec 64) (hp : pfx &&& 0xffffffffffff#64 = 0#64)
    (_hs : s0 < 0x1000000000000#64) (ha : a < 0x1000000000000#64) (hb : b < 0x1000000000000#64)
    (h : pfx ||| ((s0 + a) &&& 0xffffffffffff#64) = pfx ||| ((s0 + b) &&& 0xffffffffffff#64)) :
    a = b := by
  have key : ∀ z : BitVec 64, (pfx ||| (z &&& 0xffffffffffff#64)) &&& 0xffffffffffff#64 =
      z &&& 0xffffffffffff#64 := by
    intro z
    rw [BitVec.and_or_distrib_right, hp, BitVec.zero_or, BitVec.and_assoc, BitVec.and_self]
  have h2 := congrArg (· &&& 0xffffffffffff#64) h
  simp only [key] at h2
  have h3 := congrArg BitVec.toNat h2
  have m := mask_toNat (s0 + a) 48 (by omega)
  have m' := mask_toNat (s0 + b) 48 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 48 - 1)) = 0xffffffffffff#64 from rfl] at m m'
  rw [m, m', BitVec.toNat_add, BitVec.toNat_add] at h3
  rw [BitVec.lt_def] at ha hb
  simp only [BitVec.toNat_ofNat] at ha hb
  apply BitVec.eq_of_toNat_eq
  omega

theorem w64_nat_lt48 (j : Nat) (h : j < 2 ^ 48) : W64 (j : Int) < 0x1000000000000#64 := by
  rw [BitVec.lt_def]
  have : (W64 (j : Int)).toNat = j := by
    unfold W64; simp only [BitVec.toNat_ofInt]; omega
  rw [this]; simp; omega

theorem w64_nat_inj (a b : Nat) (ha : a < 2 ^ 48) (hb : b < 2 ^ 48)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h' := congrArg BitVec.toNat h
  unfold W64 at h'; simp only [BitVec.toNat_ofInt] at h'; omega

/-- The id issued `k + 1`-th is none of the first `k`. -/
theorem idIssued_not_new (pfx s0 : w64) (k : Nat) (Hs0 : uint.Z s0 < 2 ^ 48)
    (Hpl : pfx &&& W64 (2 ^ 48 - 1) = W64 0) (Hk : k + 1 < 2 ^ 48) :
    ¬ idIssued pfx s0 k (pfx ||| ((s0 + W64 ((k + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1))) := by
  rintro ⟨j, hj1, hjk, heq⟩
  have hs : s0 < 0x1000000000000#64 := by
    rw [BitVec.lt_def]; simp [uint.Z] at Hs0 ⊢; omega
  have := idutil_id_inj pfx s0 _ _ Hpl hs (w64_nat_lt48 j (by omega)) (w64_nat_lt48 (k + 1) Hk)
    (by exact heq.symm)
  have := w64_nat_inj _ _ (by omega) Hk this
  omega

theorem idIssued_succ (pfx s0 : w64) (k : Nat) (id : w64) :
    idIssued pfx s0 (k + 1) id ↔
      idIssued pfx s0 k id ∨
        id = pfx ||| ((s0 + W64 ((k + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1)) := by
  constructor
  · rintro ⟨j, hj1, hjk, heq⟩
    by_cases h : j = k + 1
    · subst h; exact Or.inr heq
    · exact Or.inl ⟨j, hj1, by omega, heq⟩
  · rintro (⟨j, hj1, hjk, heq⟩ | heq)
    · exact ⟨j, hj1, by omega, heq⟩
    · exact ⟨k + 1, by omega, Nat.le_refl _, heq⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

theorem idutil.Generator.Next.wp_proof (hL : idutil.lowbit.spec (GF := GF) (hG := hG)) :
    idutil.Generator.Next.spec (GF := GF) (hG := hG) := by
  intro γi g
  wp_start as ⟨#Hg, Hc⟩
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold idGen at Hg
  icases Hg with ⟨%pfx, %s0, %Hgn, #Hpfx, %Hs0, #Hinv⟩
  obtain ⟨Hs0, Hpl⟩ := Hs0
  wp_auto
  wp_apply_core sync.atomic.wp_AddUint64 $$ [] [HΦ Hc g]
  · iexact Hat
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%k, %I, %S, Hsuf, Hcr, %Hk, HI, HS, %Hdom⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (s0 + W64 (k : Int))
  iframe Hsuf
  iintro Hsuf
  imod Hmask with -
  -- spend the credit
  iunfold idCred at Hc
  icombine Hcr Hc gives %Hv
  have Hc1 : 1 ≤ 2 ^ 48 - 1 - k := by
    obtain ⟨z, hz⟩ := (Auth.auth_both_valid_discrete.mp Hv).1
    have : 2 ^ 48 - 1 - k = 1 + z := hz
    omega
  icombine Hcr Hc as HCC
  imod own_update γi.cred _ ((● (2 ^ 48 - 1 - (k + 1)) : Auth Nat) • ◯ (0 : Nat))
    (Auth.auth_update (CommMonoidLike.leftCancelAdd_local_update
      (by show 2 ^ 48 - 1 - k + 0 = (2 ^ 48 - 1 - (k + 1)) + 1; omega)))
    $$ HCC with HCC
  icases (own_op γi.cred _ _).1 $$ HCC with ⟨Hcr, -⟩
  have Hk1 : k + 1 < 2 ^ 48 := by omega
  have Hnew := idIssued_not_new pfx s0 k Hs0 Hpl Hk1
  generalize hid : pfx ||| ((s0 + W64 ((k + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1)) = nid at Hnew
  have HIn : I !! nid = none := by
    cases h : I !! nid with
    | none => rfl
    | some _ => exact absurd ((Hdom nid).1.mp (by simp [h])) Hnew
  have HSn : S !! nid = none := by
    cases h : S !! nid with
    | none => rfl
    | some _ => exact absurd ((Hdom nid).2.mp (by simp [h])) Hnew
  imod ghost_map_insert nid (none : Option (List w8)) HIn $$ HI with ⟨HI, Hu⟩
  imod ghost_map_insert nid () HSn $$ HS with ⟨HS, Hsl⟩
  imod Hclose $$ [Hsuf Hcr HI HS] with -
  · inext
    iexists (k + 1), (I.insert nid none), (S.insert nid ())
    have hsuf : s0 + W64 (k : Int) + W64 1 = s0 + W64 ((k + 1 : Nat) : Int) := by
      push_cast; word
    rw [hsuf]
    iframe Hsuf
    rw [show 2 ^ 48 - 1 - (k + 1) = 2 ^ 48 - 1 - (k + 1) from rfl]
    iframe Hcr HI HS
    ipureintro
    refine ⟨by omega, fun id' => ⟨?_, ?_⟩⟩
    · rw [GMap.lookup_insert_is_Some, idIssued_succ, ← (Hdom id').1, hid]
      by_cases h : nid = id'
      · subst h; simp
      · constructor
        · rintro (h' | ⟨_, h'⟩)
          · exact absurd h' h
          · exact Or.inl h'
        · rintro (h' | h')
          · exact Or.inr ⟨h, h'⟩
          · exact absurd h'.symm h
    · rw [GMap.lookup_insert_is_Some, idIssued_succ, ← (Hdom id').2, hid]
      by_cases h : nid = id'
      · subst h; simp
      · constructor
        · rintro (h' | ⟨_, h'⟩)
          · exact absurd h' h
          · exact Or.inl h'
        · rintro (h' | h')
          · exact Or.inr ⟨h, h'⟩
          · exact absurd h'.symm h
  imodintro
  wp_auto
  wp_apply hL (s0 + W64 (k : Int) + W64 1) (W64 48) (by word)
  have hres : pfx ||| ((s0 + W64 (k : Int) + W64 1) &&& W64 (2 ^ 48 - 1)) = nid := by
    rw [← hid]
    congr 2
    push_cast; word
  rw [hres]
  iapply HΦ
  iunfold idFresh
  iunfold idUnclaimed
  iunfold idSlot
  iframe Hu Hsl
  iexists pfx, s0, (k + 1)
  iframe Hpfx
  ipureintro
  exact ⟨by omega, Hk1, hid.symm⟩

end proof

end EtcdGrove
end Perennial
