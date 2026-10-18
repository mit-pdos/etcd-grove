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
  have m := idutil_mask_toNat (s0 + a) 48 (by omega)
  have m' := idutil_mask_toNat (s0 + b) 48 (by omega)
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
  intro γi g Φc
  wp_start as ⟨#Hg, Hc⟩
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold idGen at Hg
  icases Hg with ⟨%pfx, %s0, %Hgn, #Hpfx, %Hs0, #Hinv⟩
  obtain ⟨Hs0, Hpl⟩ := Hs0
  -- the steps up to `atomic.AddUint64`'s resolution, one by one (`wp_auto` would take that step
  -- too, and its receipt with it)
  wp_alloc g_ptr as Hgl
  wp_pure
  wp_pure
  wp_load
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  -- the Go step resolving `atomic.AddUint64` gives one time receipt (D19b)
  wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro Hr -
  iapply wp_value'
  wp_apply_core sync.atomic.wp_AddUint64 $$ [] [HΦ Hc Hgl Hr]
  · iexact Hat
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%k, %I, %S, >Hsuf, >Hcr, >HI, >HS, >%Hdom, HF⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists (s0 + W64 (k : Int))
  iframe Hsuf
  iintro Hsuf
  imod Hmask with -
  -- count the id: its receipt and the `k` of the invariant bound `k + 1` (`receipt_add_one_lt`)
  icases receipt_add_one_lt k $$ [Hr Hcr] with ⟨%Hlt, Hcr⟩
  · iframe
  iunfold idCred at Hc
  icases Hc with %Hb
  have Hk1 : k + 1 < 2 ^ 48 := Nat.lt_of_lt_of_le Hlt Hb
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
  imod ghost_map_insert nid (none : Option (List w8 × GName)) HIn $$ HI with ⟨HI, Hu⟩
  imod ghost_map_insert nid () HSn $$ HS with ⟨HS, Hsl⟩
  imod Hclose $$ [Hsuf Hcr HI HS HF] with -
  · inext
    iexists (k + 1), (I.insert nid none), (S.insert nid ())
    have hsuf : s0 + W64 (k : Int) + W64 1 = s0 + W64 ((k + 1 : Nat) : Int) := by
      push_cast; word
    rw [hsuf]
    iframe Hsuf
    iframe Hcr HI HS
    isplitr
    · ipureintro
      refine fun id' => ⟨?_, ?_⟩
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
    iunfold idClaimsFacts at HF
    iunfold idClaimsFacts
    have HIn' : I.lookup nid = none := HIn
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := I) (Φ := idClaimFact Φc) HIn').2
    iframe HF
    iunfold idClaimFact
    itrivial
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
