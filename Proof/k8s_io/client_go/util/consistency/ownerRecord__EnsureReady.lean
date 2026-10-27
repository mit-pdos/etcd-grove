/-
Proof of `Spec/k8s_io/client_go/util/consistency/ownerRecord__EnsureReady.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.ownerRecord__EnsureReady
public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.CompareResourceVersion
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.client_go.util.consistency.InvLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency resourceversion

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- One checked version: what `readyVs` says of `gr ↦ wroteRV`. -/
abbrev readyOne (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF) (gr : GR)
    (wroteRV : GoString) : IProp GF :=
  iprop(∃ readRV : GoString, □ G gr readRV ∗
    ⌜(∃ v, S !! gr = some v ∧ v ≠ interface.nil) ∧ readRV ≠ [] ∧
      (wellFormed readRV = true → decVal wroteRV ≤ decVal readRV)⌝)

/-- The keys visited after the `i`-th one: those before it, and it. -/
theorem mem_take_next {keys : List GR} {i : Int} {key : GR} (h : keys[i.toNat]? = some key)
    {k : GR} (hk : k ∈ keys.take (i + 1).toNat) : k ∈ keys.take i.toNat ∨ k = key := by
  have hle : (i + 1).toNat ≤ i.toNat + 1 := by omega
  have hk' : k ∈ keys.take (i.toNat + 1) := List.take_subset_take_left keys hle hk
  rw [List.take_add_one, h] at hk'
  simpa using hk'

theorem ownerRecord.EnsureReady.wp_proof
    (wp_Compare : resourceversion.CompareResourceVersion.spec (GF := GF) (hG := hG))
    (wp_String : schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG)) :
    ownerRecord.EnsureReady.spec (GF := GF) (hG := hG) := by
  intro c γ T S G r s V
  iintro %Φ ⟨#Hpkg, #Hc, #Hrec, Htok⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iNamed Hc'
  ihave #Hrec' := Hrec
  iunfold isRec at Hrec'
  icases Hrec' with ⟨-, Hp⟩
  iunfold recPhys at Hp
  icases Hp with ⟨%Hnn, #Huid, #Hvm, #Hmu⟩
  let K : Bool → IProp GF := fun ok => iprop(∀ err : GoInterface,
    (⌜ok = true ↔ err = interface.nil⌝ ∗
      (if ok then ensTok γ s.owner ⟨r, V, true⟩ else T s.owner 1)) -∗ Φ #err)
  ihave HAU : auEns γ S G s.owner K $$ [HAU]
  · iunfold auEns; iexact HAU
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HI⟩
  iunfold recLockInv at HI
  icases HI with ⟨%V', Hvmap, Hg⟩
  imod ens_agree γ T false V' $$ [$Hinv $Hlc1 $Htok $Hrec $Hg] with ⟨Htok, Hg, %HV⟩
  obtain ⟨rfl, HVwf⟩ := HV
  -- the deferred `Unlock`, as a triple
  ihave ⟨%dv, defer, #Hdv⟩ : iprop(∃ dv : GoFunc, defer ↦ dv ∗
      □ (∀ Ψ : val → IProp GF, sync.ownMutex (structFieldRef ownerRecord go!"versionsLock" r) ∗
        ▷ recLockInv s -∗ ▷ Ψ #() -∗ WP (App (Val #dv) (Val #())) {{ Ψ }})) $$ [defer]
  · iexists _; iframe
    iintro !> %Ψ ⟨Hl, HI⟩ HΨ
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hl $HI]
    iexact HΨ
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GR) (i : Int) => iprop(∃ (g : GR) (w : GoString),
      "gr" ∷ gr_ptr ↦ g ∗ "wroteRV" ∷ wroteRV_ptr ↦ w ∗
      "Htok" ∷ ensTok γ s.owner ⟨r, V', false⟩ ∗ "HAU" ∷ auEns γ S G s.owner K ∗
      "Hlocked" ∷ sync.ownMutex (structFieldRef ownerRecord go!"versionsLock" r) ∗
      "Hg" ∷ ghostVar s.γv (1 : Qp).half V' ∗ "c" ∷ c_ptr ↦ c ∗
      "defer" ∷ defer ↦ dv ∗
      "#Hready" ∷ □ (∀ k wrv, ⌜k ∈ keys.take i.toNat ∧ V' !! k = some wrv⌝ -∗
        readyOne S G k wrv))) $$ Hvmap
  iintro %keys %Hkeys
  isplitl [gr wroteRV Htok HAU Hlocked Hg c defer]
  · iexists _, _; iframe
    iintro !> %k %wrv ⟨%hk, -⟩
    simp at hk
  isplitr
  · iintro !> %i %key %wrv %Hiv HP
    iNamed HP
    obtain ⟨hki, hkv⟩ := Hiv
    wp_auto_lc 2
    wp_apply wp_map_lookup2 $$ [$HS] as -
    by_cases hok : ∃ ii, S !! key = some (interface.ok ii)
    · obtain ⟨ii, hii⟩ := hok
      rw [hii]
      simp only [Option.isSome_some, Option.getD_some, _root_.decide_true, Bool.not_true]
      wp_auto
      ihave #Hgt := BigSepM.bigSepM_lookup hii $$ Hget
      iunfold getterOk at Hgt
      wp_apply Hgt as %rd #HG
      by_cases hrd : rd = []
      · simp only [hrd, _root_.decide_true]
        wp_auto
        imod ens_err_commit γ T S G K $$ [$Hinv $Hlc1 $Hlc2 $Htok $HAU] with ⟨HT, HK⟩
        wp_alloc_anon
        wp_auto
        unfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro Hvmap
        wp_auto
        wp_apply Hdv $$ [$Hlocked Hvmap Hg]
        · iunfold recLockInv; iexists _; iframe
        iapply HK
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro; simp
      · simp only [hrd, decide_false]
        wp_auto
        wp_apply wp_Compare
        have hwo : wellFormed wrv = true := HVwf key wrv hkv
        -- what this iteration checked
        have hnil : ∃ v, S !! key = some v ∧ v ≠ interface.nil := ⟨_, hii, fun h => nomatch h⟩
        cases hw : wellFormed rd
        · simp only [compareRV, hwo, hw, Bool.false_eq_true, ↓reduceIte]
          wp_auto
          unfold forMapPostcondition
          ileft
          isplitr
          · ipureintro; rfl
          iexists _, _
          iframe
          iintro !> %k %w' ⟨%hk, %hkw⟩
          rcases mem_take_next hki hk with hk | rfl
          · iapply Hready $$ %k %w' %(⟨hk, hkw⟩)
          · rw [hkv] at hkw; cases hkw
            iexists rd; iframe #
            ipureintro; exact ⟨hnil, hrd, fun h => absurd h (by simp [hw])⟩
        · simp only [compareRV, hwo, hw, ↓reduceIte]
          by_cases hlt : decVal rd < decVal wrv
          · have hc : cmpNat (decVal wrv) (decVal rd) = W64 1 := by
              simp only [cmpNat, show ¬ decVal wrv < decVal rd by omega,
                show decVal wrv ≠ decVal rd by omega, ↓reduceIte]
            rw [hc]
            wp_auto
            imod ens_err_commit γ T S G K $$ [$Hinv $Hlc1 $Hlc2 $Htok $HAU] with ⟨HT, HK⟩
            wp_alloc_anon
            wp_auto
            unfold forMapPostcondition
            iright; iright; iright
            iexists _
            isplitr
            · ipureintro; rfl
            iintro Hvmap
            wp_auto
            wp_apply Hdv $$ [$Hlocked Hvmap Hg]
            · iunfold recLockInv; iexists _; iframe
            iapply HK
            simp only [Bool.false_eq_true, ↓reduceIte]
            iframe
            ipureintro; simp
          · have hle : decVal wrv ≤ decVal rd := by omega
            have hc : sint.Z (cmpNat (decVal wrv) (decVal rd)) ≤ 0 := by
              unfold cmpNat
              by_cases h1 : decVal wrv < decVal rd
              · rw [if_pos h1]; simp
              · rw [if_neg h1, if_pos (by omega)]; simp
            wp_auto
            wp_if_destruct
            · exfalso; have : sint.Z (W64 0) = 0 := rfl; omega
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _, _
            iframe
            iintro !> %k %w' ⟨%hk, %hkw⟩
            rcases mem_take_next hki hk with hk | rfl
            · iapply Hready $$ %k %w' %(⟨hk, hkw⟩)
            · rw [hkv] at hkw; cases hkw
              iexists rd; iframe #
              ipureintro; exact ⟨hnil, hrd, fun _ => hle⟩
    · have hbad : S !! key = none ∨ S !! key = some interface.nil := by
        cases h : S !! key with
        | none => exact Or.inl rfl
        | some v =>
          cases v with
          | nil => exact Or.inr rfl
          | ok ii => exact absurd ⟨ii, h⟩ hok
      rcases hbad with h | h <;> rw [h] <;>
        simp only [Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some,
          Bool.false_eq_true, decide_false, Bool.not_false, _root_.decide_true, Bool.not_true]
      all_goals (
        wp_auto
        imod ens_err_commit γ T S G K $$ [$Hinv $Hlc1 $Hlc2 $Htok $HAU] with ⟨HT, HK⟩
        wp_apply (wp_String gr_ptr (DFrac.own 1) key) $$ [$gr] as %str gr
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        simp only [go.arrayLiteralSize, List.foldl]
        wp_auto
        wp_apply (fmt.wp_Errorf _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string str [] _root_.Perennial.fmt.ArgsWf.nil)) $$ [$Hl1] as %err #Herr
        unfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro Hvmap
        wp_auto
        wp_apply Hdv $$ [$Hlocked Hvmap Hg]
        · iunfold recLockInv; iexists _; iframe
        iapply HK
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro; simp)
  iintro HP Hvmap
  iNamed HP
  wp_auto_lc 2
  ihave #Hready' : readyVs S G V' $$ []
  · iapply (BigSepM.bigSepM_intro (P := iprop(□ (∀ k wrv, ⌜k ∈ keys.take (GMap.size V' : Int).toNat ∧
        V' !! k = some wrv⌝ -∗ readyOne S G k wrv))) ?_) $$ Hready
    intro k wrv hget
    iintro #H
    have hk : k ∈ keys.take (GMap.size V' : Int).toNat := by
      rw [Int.toNat_natCast, ← Hkeys.2.1, List.take_length]
      exact (Hkeys.1 k).2 (by simp [show V' !! k = some wrv from hget])
    iapply H $$ %k %wrv %(⟨hk, hget⟩)
  imod ens_ok_commit γ T S G K $$ [$Hinv $Hexcl $Hlc1 $Hlc2 $Htok $Hrec $Hready' $HAU] with ⟨Htok, HK⟩
  wp_apply Hdv $$ [$Hlocked Hvmap Hg]
  · iunfold recLockInv; iexists _; iframe
  iapply HK
  simp only [↓reduceIte]
  iframe


end proof

end consistency
end EtcdGrove
end Perennial
