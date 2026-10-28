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
  intro γi memberID now Φs Hpfx
  wp_start as ⟨Hshare, #Hcl⟩
  iunfold idShare at Hshare
  icases Hshare with ⟨Hcnt, HS⟩
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
  ipersist prefix'
  generalize hs0 : ((ns / BitVec.sdiv (W64 1000000) (W64 1) &&& W64 (2 ^ 40 - 1)) <<< W64 8) = s0
  have Hs0 : uint.Z s0 < 2 ^ 48 := by
    have h' : s0 < 0x1000000000000#64 := by rw [← hs0]; exact idutil_suffix_lt _
    rw [BitVec.lt_def] at h'
    simp [uint.Z]; simp at h'; omega
  have Hpl : γi.pfx &&& W64 (2 ^ 48 - 1) = W64 0 := by
    rw [Hpfx]; exact idutil_prefix_low _
  imod receipt_zero (GF := GF) with HCa
  imod inv_alloc idN ⊤ iprop(∃ (k : Nat) (L : List w64) (S : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" gp ↦
        (s0 + W64 (k : Int)) ∗
      ⧗ k ∗
      γi.pfx ↪[γi.cnt] L ∗ ghostMapAuth γi.slot 1 S ∗
      ⌜∀ id, (id ∈ L ↔ idIssued γi.pfx s0 k id) ∧ ((S !! id).isSome ↔ idIssued γi.pfx s0 k id)⌝)
    $$ [suffix HCa Hcnt HS] with #Hinv
  · inext
    iexists 0, [], ∅
    rw [show s0 + W64 ((0 : Nat) : Int) = s0 by word]
    iframe suffix Hcnt HS HCa
    ipureintro
    intro id
    have hn : ¬ idIssued γi.pfx s0 0 id := by
      rintro ⟨j, h1, h2, -⟩; omega
    simp only [List.not_mem_nil, GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true,
      false_iff]
    exact ⟨hn, hn⟩
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
  iexists Φs
  iframe Hcl
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
