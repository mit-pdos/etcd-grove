/-
`(*KV).ReadVersion`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.Lemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace kvp

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [store.kv.Assumptions] [store.Assumptions]

theorem wp_ReadVersion (p : Loc) (γs : GName) (k : GoString) (v : w64) :
    isKV (hG := hG) p γs ⊢
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (App (Val #(methods (go.GoType.PointerType store.kv.KV.ty) go!"ReadVersion" #p))
          (Val #k)) (Val #v)) @ ∅
      <<{ ∃∃ (r : Option GoString), storeOwn γs q S ∗
            ⌜∀ x, r = some x → ∃ c, (v, x, c) ∈ S.items k⌝ ∗ ⌜r = none → S.hasVer k v = false⌝ |
          (p : Loc) (err : GoInterface), RET (PairV #p #err);
          match r with
          | some x => ⌜err = interface.nil⌝ ∗ itemPtr p k v x
          | none => errNotFound err }>> := by
  iintro #Hkv
  unfold isKV
  icases Hkv with ⟨%mp, #Hitems, #Hmu, #Hpkg⟩
  ihave #Herr := errNotFound_of_init $$ Hpkg
  icases Herr with ⟨%errNF, #Herr⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  unfold lockInv
  icases Hi with ⟨%m, %S0, Hm, Hγ, %Hnone, Hmap⟩
  icases map_take m S0 k Hnone $$ Hmap with ⟨⟨%l0, Hk, %Hl0⟩, Hrest⟩
  unfold keyOwn
  icases Hk with ⟨Hsl0, Hcap0, Hits⟩
  wp_apply wp_lookup p mp m k (l0.map Prod.fst) (fun h => by simpa using Hl0.2.1 h)
    $$ [$Hitems $Hm $Hsl0] as ⟨Hm, Hsl0⟩
  ihave #Herr' := Herr
  iunfold errNotFound at Herr
  icases Herr with ⟨%xe, %Hxe, #HeA, #HeS, #HeM⟩
  have hr := map_restore (hG := hG) m S0 k
  cases hks : (m !! k).isSome
  · -- absent key
    have hk : m !! k = none := by
      cases h : m !! k <;> simp_all
    wp_auto
    have hl0 : l0 = [] := Hl0.2.2 hk
    subst hl0
    have hv : S0.hasVer k v = false := by rw [hasVer_eq S0 k v [] Hl0.1]; rfl
    iapply fupd_wp
    imod AU with ⟨%x', Hst, -, Hcommit⟩
    rcases x' with ⟨q, S', ⟨⟩⟩
    dsimp only [Tele.app]
    ihave %Heq := own_agree γs q S0 S' $$ Hγ Hst
    subst S'
    imod Hcommit $$ %(⟨none, ⟨⟩⟩) [Hst] with HΦ
    · dsimp only [Tele.app]
      iframe Hst
      ipureintro
      exact ⟨fun x h => by simp at h, fun _ => hv⟩
    imodintro
    ihave Hmap := hr [] ⟨Hl0.1, fun h => by simp [hk] at h⟩ $$ [Hsl0 Hcap0 Hits Hrest]
    · unfold keyOwn; iframe
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
    · inext
      iexists m, S0
      iframe
      ipureintro; exact Hnone
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iapply HΦ
    iframe #
  -- present key
  have hne : l0 ≠ [] := Hl0.2.1 hks
  obtain ⟨slk, hk⟩ : ∃ slk, m !! k = some slk := by
    cases h : m !! k <;> simp_all
  simp only [hk, Option.getD_some]
  simp only [hk, Option.getD_some, Option.isSome_some, forall_const] at hr
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl0
  simp only [List.length_map] at Hlen
  ihave HI : (∃ (i : w64) (pi : Loc),
      "i" ∷ i_ptr ↦ i ∗ "item" ∷ item_ptr ↦ pi ∗
      "%Hnot" ∷ ⌜∀ e ∈ l0.take (sint.nat i), e.2.1 ≠ v⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z slk.len⌝ : IProp GF) $$ [i item]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨?_, by word⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; simp
  wp_for HI
  wp_if_destruct
  · -- loop body
    simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
    list_elem l0 (sint.nat i) as e
    wp_apply wp_load_slice_index slk (sint.Z i) (l0.map Prod.fst) _ e.1 Hi.1 $$ [Hsl0] with Hsl0
    · iframe; ipureintro
      rw [List.getElem?_map, show (sint.Z i).toNat = sint.nat i from rfl, He_lookup]; rfl
    icases BigSepL.bigSepL_lookup_acc He_lookup |>.1 $$ Hits with ⟨He, Hits⟩
    iunfold itemOwn at He
    iunfold itemPtr at He
    icases He with ⟨%Hnn, ⟨#HK, #HV, %vsl, #HVal, #Hx⟩, HC⟩
    wp_auto
    ihave Hits := Hits $$ %e [HC]
    · unfold itemOwn itemPtr
      iframe HC HK HV
      isplitr
      · ipureintro; exact Hnn
      iexists vsl
      iframe #
    rw [list_set_lookup_self l0 _ e He_lookup]
    by_cases hv : e.2.1 = v
    · rw [decide_eq_true hv]
      have hmem : (v, e.2.2.1, e.2.2.2) ∈ S0.items k := by
        rw [Hl0.1, ← hv]
        exact List.mem_map.2 ⟨e, List.mem_of_getElem? He_lookup, rfl⟩
      iapply fupd_wp
      imod AU with ⟨%x', Hst, -, Hcommit⟩
      rcases x' with ⟨q, S', ⟨⟩⟩
      dsimp only [Tele.app]
      ihave %Heq := own_agree γs q S0 S' $$ Hγ Hst
      subst S'
      imod Hcommit $$ %(⟨some e.2.2.1, ⟨⟩⟩) [Hst] with HΦ
      · dsimp only [Tele.app]
        iframe Hst
        ipureintro
        refine ⟨fun x h => ?_, fun h => by simp at h⟩
        simp only [Option.some.injEq] at h; subst h
        exact ⟨_, hmem⟩
      imodintro
      ihave Hmap := hr l0 ⟨Hl0.1, hne⟩ $$ [Hsl0 Hcap0 Hits Hrest]
      · unfold keyOwn; iframe
      wp_auto
      wp_for_post
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
      · inext
        iexists m, S0
        iframe
        ipureintro; exact Hnone
      dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold itemPtr
      rw [← hv]
      iframe #
    · rw [decide_eq_false hv]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, e.1
      iframe
      ipureintro
      refine ⟨?_, by word⟩
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, take_succ_of_lookup l0 _ e He_lookup]
      intro e' he'
      rcases List.mem_append.1 he' with h | h
      · exact Hnot e' h
      · simp at h; subst h; exact hv
  · -- loop exit
    have hiE : sint.nat i = l0.length := by
      rw [Hlen.1]; word
    rw [hiE, List.take_length] at Hnot
    have hv : S0.hasVer k v = false := by
      rw [hasVer_eq S0 k v l0 Hl0.1]
      simp only [List.any_eq_false, decide_eq_true_eq]
      exact Hnot
    iapply fupd_wp
    imod AU with ⟨%x', Hst, -, Hcommit⟩
    rcases x' with ⟨q, S', ⟨⟩⟩
    dsimp only [Tele.app]
    ihave %Heq := own_agree γs q S0 S' $$ Hγ Hst
    subst S'
    imod Hcommit $$ %(⟨none, ⟨⟩⟩) [Hst] with HΦ
    · dsimp only [Tele.app]
      iframe Hst
      ipureintro
      exact ⟨fun x h => by simp at h, fun _ => hv⟩
    imodintro
    ihave Hmap := hr l0 ⟨Hl0.1, hne⟩ $$ [Hsl0 Hcap0 Hits Hrest]
    · unfold keyOwn; iframe
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
    · inext
      iexists m, S0
      iframe
      ipureintro; exact Hnone
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iapply HΦ
    iframe #

end proofs

end kvp

end github_com.despreston.go_craq

end Perennial
