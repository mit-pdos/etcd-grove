/-
`(*KV).AllNewerCommitted`: each key's newest committed item, if newer than the request's.
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

/-! ## The inner loop: the key's committed item of highest version -/

/-- One step of the inner loop (`local`). -/
def bestStep : Option (Loc × It) → (Loc × It) → Option (Loc × It)
  | none, e => if e.2.2.2 = true then some e else none
  | some c, e => if e.2.2.2 = true ∧ uint.Z c.2.1 < uint.Z e.2.1 then some e else some c

/-- The inner loop's result on a key's items. -/
def best (l : List (Loc × It)) : Option (Loc × It) := l.foldl bestStep none

/-- `maxCommitted`'s step. -/
def mcStep (m : w64) (e : w64 × GoString × Bool) : w64 :=
  if e.2.2 = true ∧ uint.Z m < uint.Z e.1 then e.1 else m

theorem maxCommitted_eq (S : StoreS) (k : GoString) :
    S.maxCommitted k = (S.items k).foldl mcStep (W64 0) := rfl

/-- The relation between the loop's state and `maxCommitted`'s. -/
def bestRel (l : List (Loc × It)) (cur : Option (Loc × It)) (m : w64) : Prop :=
  (cur = none ∧ m = W64 0) ∨ (∃ c, cur = some c ∧ c ∈ l ∧ c.2.2.2 = true ∧ m = c.2.1)

theorem bestRel_foldl (l0 l : List (Loc × It)) (cur : Option (Loc × It)) (m : w64)
    (hsub : ∀ e ∈ l, e ∈ l0) (h : bestRel l0 cur m) :
    bestRel l0 (l.foldl bestStep cur) ((l.map Prod.snd).foldl mcStep m) := by
  induction l generalizing cur m with
  | nil => exact h
  | cons e l ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih _ _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
    have he : e ∈ l0 := hsub e (List.mem_cons_self ..)
    rcases h with ⟨rfl, rfl⟩ | ⟨c, rfl, hc, hcc, rfl⟩
    · by_cases hcom : e.2.2.2 = true
      · right
        refine ⟨e, by simp [bestStep, hcom], he, hcom, ?_⟩
        unfold mcStep
        by_cases hz : uint.Z (W64 0) < uint.Z e.2.1
        · rw [if_pos ⟨hcom, hz⟩]
        · rw [if_neg (fun h => hz h.2)]
          have : uint.Z e.2.1 = 0 := by word
          word
      · left
        simp [bestStep, mcStep, hcom]
    · right
      by_cases hup : e.2.2.2 = true ∧ uint.Z c.2.1 < uint.Z e.2.1
      · exact ⟨e, by simp [bestStep, hup], he, hup.1, by simp [mcStep, hup]⟩
      · refine ⟨c, by simp only [bestStep, hup, ↓reduceIte], hc, hcc, ?_⟩
        simp only [mcStep]
        rw [if_neg hup]

theorem best_spec (S : StoreS) (k : GoString) (l : List (Loc × It))
    (h : S.items k = l.map Prod.snd) :
    (best l = none ∧ S.maxCommitted k = W64 0) ∨
    (∃ c, best l = some c ∧ c ∈ l ∧ c.2.2.2 = true ∧ S.maxCommitted k = c.2.1) := by
  rw [maxCommitted_eq, h]
  exact bestRel_foldl l l none (W64 0) (fun _ h => h) (Or.inl ⟨rfl, rfl⟩)

theorem best_take_succ (l : List (Loc × It)) (j : Nat) (e : Loc × It) (h : l[j]? = some e) :
    best (l.take (j + 1)) = bestStep (best (l.take j)) e := by
  rw [take_succ_of_lookup l j e h]; simp [best, List.foldl_append]

theorem foldl_bestStep_some (l : List (Loc × It)) (c : Loc × It) :
    l.foldl bestStep (some c) ≠ none := by
  induction l generalizing c with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons, bestStep]
    split
    · exact ih _
    · exact ih _

theorem best_none (l : List (Loc × It)) (h : best l = none) :
    (l.map Prod.snd).any (fun e => e.2.2) = false := by
  unfold best at h
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldl_cons, bestStep] at h
    split at h
    · exact absurd h (foldl_bestStep_some _ _)
    · rename_i hc
      simp only [List.map_cons, List.any_cons, ih h, Bool.or_false]
      simpa using hc

theorem mc_zero (l : List It) (h : l.any (fun e => e.2.2) = false) :
    l.foldl mcStep (W64 0) = W64 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.foldl_cons, mcStep, h.1, Bool.false_eq_true, false_and, ↓reduceIte]
    exact ih h.2

/-- `local`'s value. -/
def lpOf : Option (Loc × It) → Loc
  | none => null
  | some c => c.1

/-- The keys whose newest committed item the result has. -/
def sel (S : StoreS) (req : GMap GoString w64) (k : GoString) : Bool :=
  (S.items k).any (fun e => e.2.2) &&
    (match req !! k with
     | none => true
     | some h => decide (uint.Z h < uint.Z (S.maxCommitted k)))

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [store.kv.Assumptions] [store.Assumptions]

/-- What `local` points to (persistent). -/
def bestPtr (k : GoString) : Option (Loc × It) → IProp GF
  | none => iprop(True)
  | some c => iprop(⌜c.1 ≠ null⌝ ∗ itemPtr c.1 k c.2.1 c.2.2.1)

/-- The result's items, in the indexed form of `newestIn`. -/
theorem newest_idx (acc : List (Loc × (GoString × w64 × GoString))) :
    ([∗list] e ∈ acc, itemPtr (hG := hG) e.1 e.2.1 e.2.2.1 e.2.2.2) ⊢
      [∗list] i ↦ p ∈ acc.map Prod.fst, ∃ e, ⌜(acc.map Prod.snd)[i]? = some e⌝ ∗
        itemPtr (hG := hG) p e.1 e.2.1 e.2.2 := by
  induction acc with
  | nil =>
    iintro -
    simp only [List.map_nil]
    iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
  | cons a acc ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    simp only [List.map_cons]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iexists a.2
      iframe Ha
      ipureintro
      simp
    · ihave H := ih $$ H
      iapply BigSepL.bigSepL_mono ?_ $$ H
      intro k x _
      iintro ⟨%e, %he, Hp⟩
      iexists e
      iframe Hp
      ipureintro
      simpa using he

instance bestPtr_persistent (k : GoString) (o : Option (Loc × It)) :
    Persistent (bestPtr (hG := hG) k o) := by
  cases o <;> dsimp only [bestPtr] <;> (try unfold itemPtr) <;> infer_instance

theorem wp_AllNewerCommitted (p : Loc) (γs : GName) (rq : Loc) (req : GMap GoString w64)
    (dq0 : DFrac) :
    isKV (hG := hG) p γs ⊢ ownMap rq dq0 req -∗
      <<{ ∀∀ (q : Qp) (S : StoreS), storeOwn γs q S }>>
        (App (Val #(methods (go.GoType.PointerType store.kv.KV.ty) go!"AllNewerCommitted" #p))
          (Val #rq)) @ ∅
      <<{ storeOwn γs q S | (sl : GoSlice), RET (PairV #sl #interface.nil);
          ownMap rq dq0 req ∗ newestIn sl S req }>> := by
  iintro #Hkv Hrq
  unfold isKV
  icases Hkv with ⟨%mp, #Hitems, #Hmu, #Hpkg⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  unfold lockInv
  icases Hi with ⟨%m, %S0, Hm, Hγ, %Hnone, Hmap⟩
  wp_apply wp_slice_literal (l := ([] : List Loc))
  isplitr
  · ipureintro; rfl
  iintro %np ⟨Hnew, Hncap⟩
  wp_auto
  ipersist keyVersions
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun keys (i : Int) =>
    iprop(∃ (ns : GoSlice) (es : List (Loc × (GoString × w64 × GoString))) (ik : GoSlice)
        (kk : GoString),
      newer_ptr ↦ ns ∗ ns ↦* es.map Prod.fst ∗ ownSliceCap Loc ns (DFrac.own 1) ∗
      itemsForKey_ptr ↦ ik ∗ key_ptr ↦ kk ∗ ownMap rq dq0 req ∗
      ([∗map] k ↦ sl ∈ m, keyInv S0 k sl) ∗
      ([∗list] e ∈ es, itemPtr e.1 e.2.1 e.2.2.1 e.2.2.2) ∗
      ⌜0 ≤ i ∧ es.map (·.2.1) = (keys.take i.toNat).filter (sel S0 req) ∧
        ∀ e ∈ es, (e.2.2.1, e.2.2.2, true) ∈ S0.items e.2.1 ∧
          e.2.2.1 = S0.maxCommitted e.2.1⌝))) $$ Hm
  iintro %keys %hkeys
  isplitl [Hnew Hncap newer itemsForKey key Hrq Hmap]
  · iexists slice.mk np (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])), [], _, _
    simp only [List.map_nil]
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro (P := iprop(True)); itrivial
    ipureintro
    simp
  isplitl []
  · imodintro
    iintro %i %key %sl ⟨%hk1, %hk2⟩ ⟨%ns, %es, %ik, %kk, Hnewer, Hns, Hncap, Hik, Hkk, Hrq, Hmap, Hes, %Hes⟩
    wp_auto
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun k sl => keyInv (hG := hG) S0 k sl) hk2).1 $$ Hmap
      with ⟨Hk, Hmapback⟩
    unfold keyInv keyOwn
    icases Hk with ⟨%l, ⟨Hsl, Hcap, Hits⟩, %Hl⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [List.length_map] at Hlen
    ihave HJ : (∃ (j : w64) (pj : Loc), "j" ∷ i_ptr ↦ j ∗ "itm" ∷ itm_ptr ↦ pj ∗
        "loc" ∷ local_ptr ↦ lpOf (best (l.take (sint.nat j))) ∗
        "#Hb" ∷ bestPtr key (best (l.take (sint.nat j))) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i itm «local»]
    · iexists W64 0, _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, best, List.foldl_nil, lpOf,
        bestPtr]
      iframe
      ipureintro; word
    have hi0 := Hes.1
    have Hki : (keys.take (i + 1).toNat) = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]; exact take_succ_of_lookup keys _ key hk1
    wp_for HJ
    wp_if_destruct
    · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
      list_elem l (sint.nat j) as e
      wp_apply wp_load_slice_index sl (sint.Z j) (l.map Prod.fst) _ e.1 Hj.1 $$ [Hsl] with Hsl
      · iframe; ipureintro
        rw [List.getElem?_map, show (sint.Z j).toNat = sint.nat j from rfl, He_lookup]; rfl
      icases BigSepL.bigSepL_lookup_acc He_lookup |>.1 $$ Hits with ⟨He, Hits⟩
      have hbs := best_take_succ l _ e He_lookup
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      obtain ⟨ep, ev, ex, ec⟩ := e
      iunfold itemOwn at He
      iunfold itemPtr at He
      icases He with ⟨%Hnn, ⟨#HK, #HV, %vsl, #HVal, #Hx⟩, HC⟩
      wp_auto
      ihave Hits := Hits $$ %(ep, ev, ex, ec) [HC]
      · unfold itemOwn itemPtr
        iframe HC HK HV
        isplitr
        · ipureintro; exact Hnn
        iexists vsl
        iframe #
      rw [list_set_lookup_self l _ _ He_lookup]
      generalize hcur : best (List.take (sint.nat j) l) = cur at hbs ⊢
      cases ec with
      | false =>
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, ep
        rw [Hj1, hbs]
        have : bestStep cur (ep, ev, ex, false) = cur := by
          cases cur <;> simp [bestStep]
        rw [this]
        iframe
        iframe #
        ipureintro; word
      | true =>
        cases cur with
        | none =>
          simp only [lpOf]
          wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, ep
          rw [Hj1, hbs]
          simp only [bestStep, ↓reduceIte, lpOf, bestPtr]
          iframe
          isplitr
          · isplitr
            · ipureintro; exact Hnn
            unfold itemPtr
            iframe #
          ipureintro; word
        | some c =>
          simp only [lpOf, bestPtr, itemPtr]
          icases Hb with ⟨%Hcn, #HcK, #HcV, %csl, #HcVal, #Hcx⟩
          wp_auto
          rw [decide_eq_false Hcn]
          wp_auto
          by_cases hlt : uint.Z c.2.1 < uint.Z ev
          · rw [decide_eq_true hlt]
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, ep
            rw [Hj1, hbs]
            simp only [bestStep, hlt, ↓reduceIte, lpOf, bestPtr, _root_.and_self]
            iframe
            isplitr
            · isplitr
              · ipureintro; exact Hnn
              iframe #
            ipureintro; word
          · rw [decide_eq_false hlt]
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, ep
            rw [Hj1, hbs]
            simp only [bestStep, hlt, ↓reduceIte, lpOf, bestPtr, _root_.and_false]
            iframe
            isplitr
            · isplitr
              · ipureintro; exact Hcn
              iframe #
            ipureintro; word
    · -- inner loop exit
      have hjE : sint.nat j = l.length := by rw [Hlen.1]; word
      rw [hjE, List.take_length]
      ihave Hmap := Hmapback $$ [Hsl Hcap Hits]
      · iexists l; iframe; ipureintro; exact Hl
      have hbs := best_spec S0 key l Hl.2
      have hbn := best_none l
      generalize best l = b at hbs hbn ⊢
      rcases hbs with ⟨rfl, hmc⟩ | ⟨c, rfl, hcl, hcc, hmc⟩
      · -- no committed item: continue
        simp only [lpOf]
        wp_auto
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists ns, es, sl, key
        iframe
        ipureintro
        refine ⟨by omega, ?_, Hes.2.2⟩
        rw [Hki, List.filter_append, ← Hes.2.1]
        have : sel S0 req key = false := by
          simp [sel, Hl.2, hbn rfl]
        simp [this]
      · simp only [lpOf, bestPtr, itemPtr]
        icases Hb with ⟨%Hcn, #HcK, #HcV, %csl, #HcVal, #Hcx⟩
        simp only [Hcn, _root_.decide_false]
        wp_auto
        wp_apply wp_map_lookup2 $$ Hrq as Hrq
        have hany : (S0.items key).any (fun e => e.2.2) = true := by
          rw [Hl.2, List.any_eq_true]
          exact ⟨c.2, List.mem_map_of_mem hcl, hcc⟩
        have hmem : (c.2.1, c.2.2.1, true) ∈ S0.items key := by
          rw [Hl.2, ← hcc]; exact List.mem_map_of_mem hcl
        cases hr : req !! key with
        | none =>
          have HSEL : sel S0 req key = true := by simp [sel, hany, hr]
          simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false, Bool.not_false]
          wp_auto
          wp_apply wp_slice_literal (l := [c.1])
          isplitr
          · ipureintro; rfl
          iintro %kp1 ⟨Htmp, -⟩
          wp_auto
          wp_apply wp_slice_append (V := Loc) $$ [$Hns $Hncap $Htmp] as %ns' ⟨Hns, Hncap, -⟩
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists ns', es ++ [(c.1, (key, c.2.1, c.2.2.1))], sl, key
          simp only [List.map_append, List.map_cons, List.map_nil]
          iframe
          isplitr
          · iapply BigSepL.bigSepL_singleton.2
            iframe #
          ipureintro
          refine ⟨by omega, ?_, ?_⟩
          · rw [Hki, List.filter_append, ← Hes.2.1]
            simp [HSEL]
          · intro e he
            rcases List.mem_append.1 he with he | he
            · exact Hes.2.2 e he
            · simp only [List.mem_singleton] at he
              subst he
              exact ⟨hmem, hmc.symm⟩
        | some h =>
          simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
          wp_auto
          by_cases hlt : uint.Z h < uint.Z c.2.1
          · have HSEL : sel S0 req key = true := by simp [sel, hany, hr, hmc, hlt]
            rw [decide_eq_true hlt]
            wp_auto
            wp_apply wp_slice_literal (l := [c.1])
            isplitr
            · ipureintro; rfl
            iintro %kp1 ⟨Htmp, -⟩
            wp_auto
            wp_apply wp_slice_append (V := Loc) $$ [$Hns $Hncap $Htmp] as %ns' ⟨Hns, Hncap, -⟩
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists ns', es ++ [(c.1, (key, c.2.1, c.2.2.1))], sl, key
            simp only [List.map_append, List.map_cons, List.map_nil]
            iframe
            isplitr
            · iapply BigSepL.bigSepL_singleton.2
              iframe #
            ipureintro
            refine ⟨by omega, ?_, ?_⟩
            · rw [Hki, List.filter_append, ← Hes.2.1]
              simp [HSEL]
            · intro e he
              rcases List.mem_append.1 he with he | he
              · exact Hes.2.2 e he
              · simp only [List.mem_singleton] at he
                subst he
                exact ⟨hmem, hmc.symm⟩
          · have HSEL : sel S0 req key = false := by simp [sel, hany, hr, hmc, hlt]
            rw [decide_eq_false hlt]
            wp_auto
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists ns, es, sl, key
            iframe
            ipureintro
            refine ⟨by omega, ?_, Hes.2.2⟩
            rw [Hki, List.filter_append, ← Hes.2.1]
            simp [HSEL]
    done
  iintro ⟨%ns, %es, %ik, %kk, Hnewer, Hns, Hncap, Hik, Hkk, Hrq, Hmap, Hes, %Hes⟩ Hm
  wp_auto
  have hsz : (m.size : Int).toNat = keys.length := by rw [hkeys.2.1]; omega
  rw [hsz, List.take_length] at Hes
  iapply fupd_wp
  imod AU with ⟨%x', Hst, -, Hcommit⟩
  rcases x' with ⟨q, S', ⟨⟩⟩
  dsimp only [Tele.app]
  ihave %Heq := own_agree γs q S0 S' $$ Hγ Hst
  subst S'
  imod Hcommit $$ %() [Hst] with HΦ
  · iexact Hst
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
  · inext
    iexists m, S0
    iframe
    ipureintro; exact Hnone
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iapply HΦ
  iframe Hrq
  unfold newestIn
  iexists es.map Prod.fst, es.map Prod.snd
  iframe Hns
  isplitr
  · ipureintro
    refine ⟨by simp, ?_, ?_, ?_⟩
    · rw [List.map_map]
      have : (Prod.fst ∘ Prod.snd : Loc × (GoString × w64 × GoString) → GoString) =
          (fun x => x.snd.fst) := rfl
      rw [this, Hes.2.1]
      exact hkeys.2.2.filter _
    · intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact Hes.2.2 a ha
    · intro k hk
      have hmc0 : S0.maxCommitted k ≠ W64 0 := by
        intro h; rw [h] at hk; simp at hk
      have hany : (S0.items k).any (fun e => e.2.2) = true := by
        cases hc : (S0.items k).any (fun e => e.2.2)
        · exact absurd (by rw [maxCommitted_eq]; exact mc_zero _ hc) hmc0
        · rfl
      have hkm : k ∈ keys := by
        rw [hkeys.1]
        cases h : m !! k with
        | some _ => rfl
        | none => have := Hnone k h; simp [this] at hany
      have hsel : sel S0 req k = true := by
        cases hr : req !! k with
        | none => simp [sel, hany, hr]
        | some h =>
          simp only [reqVer, hr, Option.getD_some] at hk
          simp [sel, hany, hr, hk]
      have : k ∈ es.map (fun x => x.snd.fst) := by
        rw [Hes.2.1]; exact List.mem_filter.2 ⟨hkm, hsel⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 this
      exact ⟨a.2, List.mem_map_of_mem ha, rfl⟩
  iapply newest_idx $$ Hes

end proofs

end kvp

end github_com.despreston.go_craq

end Perennial
