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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

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
  intro γi memberID now X hX Φs x Hpfx
  wp_start as ⟨Hshare, #Hkf, #Hcl⟩
  iunfold idShare at Hshare
  icases Hshare with ⟨Hcnt, HS, HP⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iapply wp_fupd
  wp_auto
  wp_apply time.Time.wp_ptr_UnixNano now_ptr now $$ [$now] as %ns now
  wp_apply hL _ (W64 40) (by word)
  irename «$r0» => Hgp
  generalize «$r0_ptr» = gp at *
  ihave ⟨Hgp, %Hgpn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hgp
  iStructNamed Hgp
  generalize hs0 : ((ns / BitVec.sdiv (W64 1000000) (W64 1) &&& W64 (2 ^ 40 - 1)) <<< W64 8) = s0
  have Hs0 : uint.Z s0 < 2 ^ 48 := by
    have h' : s0 < 0x1000000000000#64 := by rw [← hs0]; exact idutil_suffix_lt _
    rw [BitVec.lt_def] at h'
    simp [uint.Z]; simp at h'; omega
  have Hpl : γi.pfx &&& W64 (2 ^ 48 - 1) = W64 0 := by
    rw [Hpfx]; exact idutil_prefix_low _
  -- (R2c stage 2) the generator registered as the key's: no key has it yet (it is new: its
  -- `prefix` field owned whole, every registered generator's readable), then its prefix persisted
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, %R, %Fm, >HI, >HC, >HR, >HF, >%Hok, #HFs, >#HG⟩
  icombine HC Hcnt gives %Hlk
  have Hlk' : C !! γi.key = some (([], none) : IdKeyEntry) := Hlk
  ihave %Hnew : ⌜∀ k e, C !! k = some e → e.2 ≠ some gp⌝ $$ [prefix']
  · iintro %k %e %hke %he
    rcases e with ⟨L', og⟩
    simp only at he
    subst he
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := C)
      (Φ := fun k e => idKeyGenFacts (GF := GF) k e) hke).1 $$ HG with ⟨Hk, -⟩
    iunfold idKeyGenFacts at Hk
    icases Hk with ⟨#Hpf, -⟩
    iexfalso
    iapply w64_pointsto_excl _ _ _ $$ prefix' Hpf
  imod ghost_map_update ((([] : List w64), some gp) : IdKeyEntry) $$ HC Hcnt with ⟨HC, Hcnt⟩
  ipersist prefix'
  ihave #Hpfk : structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" gp ↦□ γi.pfx $$ []
  · iExactEq prefix'; rw [Hpfx]; rfl
  imod Hclose $$ [HI HC HR HF] with -
  · inext
    iexists I, (C.insert γi.key (([] : List w64), some gp)), R, Fm
    iframe HI HC HR HF HFs
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hok
    have hsome : ∀ k', ((C.insert γi.key (([] : List w64), some gp)) !! k').isSome = (C !! k').isSome := by
      intro k'
      by_cases hk : γi.key = k'
      · subst hk; rw [GMap.lookup_insert, Hlk']; rfl
      · rw [GMap.lookup_insert_ne _ _ hk]
    isplitr
    · ipureintro
      refine ⟨fun id => ?_, fun k e hke => ?_, fun k k' e e' g hke hke' he he' => ?_,
        fun k e hke hne => ?_, fun k => by rw [hsome]; exact h5 k, fun k => by rw [hsome]; exact h6 k⟩
      · rw [h1 id]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨k, e, hke, hid⟩
          by_cases hk : γi.key = k
          · subst hk; rw [Hlk'] at hke; cases hke; simp at hid
          · exact ⟨k, e, by rw [GMap.lookup_insert_ne _ _ hk]; exact hke, hid⟩
        · rintro ⟨k, e, hke, hid⟩
          by_cases hk : γi.key = k
          · subst hk; rw [GMap.lookup_insert] at hke; cases hke; simp at hid
          · exact ⟨k, e, by rw [GMap.lookup_insert_ne _ _ hk] at hke; exact hke, hid⟩
      · by_cases hk : γi.key = k
        · subst hk; rw [GMap.lookup_insert] at hke; cases hke
          exact ⟨(h2 _ _ Hlk').1, by simp⟩
        · rw [GMap.lookup_insert_ne _ _ hk] at hke; exact h2 k e hke
      · by_cases hk : γi.key = k <;> by_cases hk' : γi.key = k'
        · rw [← hk, ← hk']
        · subst hk; rw [GMap.lookup_insert] at hke; cases hke
          rw [GMap.lookup_insert_ne _ _ hk'] at hke'
          cases he
          exact absurd he' (Hnew k' e' hke')
        · subst hk'; rw [GMap.lookup_insert] at hke'; cases hke'
          rw [GMap.lookup_insert_ne _ _ hk] at hke
          cases he'
          exact absurd he (Hnew k e hke)
        · rw [GMap.lookup_insert_ne _ _ hk] at hke
          rw [GMap.lookup_insert_ne _ _ hk'] at hke'
          exact h3 k k' e e' g hke hke' he he'
      · by_cases hk : γi.key = k
        · subst hk; rw [GMap.lookup_insert] at hke; cases hke; exact absurd rfl hne
        · rw [GMap.lookup_insert_ne _ _ hk] at hke; exact h4 k e hke hne
    ihave ⟨-, Hk⟩ := (BigSepM.bigSepM_insert_acc (PROP := IProp GF) (m := C)
      (Φ := fun k e => idKeyGenFacts (GF := GF) k e) Hlk') $$ HG
    iapply Hk
    iunfold idKeyGenFacts
    simp only
    isplitl
    · iexact Hpfk
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  imod receipt_zero (GF := GF) with HCa
  imod inv_alloc idN ⊤ iprop(∃ (k : Nat) (L : List w64) (S P : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" gp ↦
        (s0 + W64 (k : Int)) ∗
      ⧗ k ∗
      γi.key ↪[γi.cnt] ((L, some gp) : IdKeyEntry) ∗ ghostMapAuth γi.slot 1 S ∗
      ghostMapAuth γi.pend 1 P ∗
      ⌜∀ id, ((id ∈ L ∨ (P !! id).isSome) ↔ idIssued γi.pfx s0 k id) ∧
        ((S !! id).isSome ↔ idIssued γi.pfx s0 k id) ∧ (id ∈ L → P !! id = none)⌝)
    $$ [suffix HCa Hcnt HS HP] with #Hinv
  · inext
    iexists 0, [], ∅, ∅
    rw [show s0 + W64 ((0 : Nat) : Int) = s0 by word]
    iframe suffix Hcnt HS HP HCa
    ipureintro
    intro id
    have hn : ¬ idIssued γi.pfx s0 0 id := by
      rintro ⟨j, h1, h2, -⟩; omega
    refine ⟨⟨fun h => by simp [GMap.lookup_empty] at h, fun h => absurd h hn⟩,
      ⟨fun h => by simp [GMap.lookup_empty] at h, fun h => absurd h hn⟩, fun h => by simp at h⟩
  imodintro
  iapply HΦ
  iunfold idGen
  iexists s0
  rw [show W64 (uint.Z memberID) <<< W64 48 = γi.pfx from Hpfx.symm]
  iframe prefix' Hinv
  isplitr
  · ipureintro; exact Hgpn
  isplitr
  · ipureintro; exact ⟨Hs0, Hpl⟩
  iexists X, hX, Φs, x
  iframe Hkf
  isplitr
  · ipureintro; rfl
  iunfold idClusterInv
  iexact Hcl

end proof

end EtcdGrove
end Perennial
