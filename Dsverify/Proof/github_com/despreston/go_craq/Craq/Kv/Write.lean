/-
`(*KV).Write`.
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

theorem wp_Write (p : Loc) (γs : GName) (k : GoString) (sl : GoSlice) (x : GoString) (v : w64) :
    isKV (hG := hG) p γs ⊢ sl ↦*□ x -∗
      <<{ ∀∀ S, storeOwn γs 1 S }>>
        (App (App (App (Val #(methods (go.GoType.PointerType store.kv.KV.ty) go!"Write" #p))
          (Val #k)) (Val #sl)) (Val #v)) @ ∅
      <<{ storeOwn γs 1 (S.write k x v) | RET #interface.nil; True }>> := by
  iintro #Hkv #Hsl
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
  icases map_take m S0 k Hnone $$ Hmap with ⟨⟨%l0, Hk, %Hl0⟩, Hrest⟩
  unfold keyOwn
  icases Hk with ⟨Hsl0, Hcap0, Hits⟩
  wp_apply wp_map_lookup1 $$ Hm as Hm
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := Loc) $$ [$Hsl0 $Hcap0 $Htmp] as %sl' ⟨Hsl', Hcap', -⟩
  wp_apply wp_mapInsert $$ Hm as Hm
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ item
  iStructNamed item
  ipersist Key
  ipersist Version
  ipersist Value
  iapply fupd_wp
  imod AU with ⟨%x', Hst, -, Hcommit⟩
  rcases x' with ⟨S', ⟨⟩⟩
  dsimp only [Tele.app]
  ihave %Heq := own_agree γs 1 S0 S' $$ Hγ Hst
  subst S'
  imod own_update γs S0 S0 (S0.write k x v) $$ Hγ Hst with ⟨Hγ, Hst⟩
  imod Hcommit $$ %() [Hst] with HΦ
  · iexact Hst
  imodintro
  ihave Hrest := map_rest m S0 (S0.write k x v) k (fun k' h => items_write_ne S0 k k' x v h) $$ Hrest
  ihave Hmap := map_put m (S0.write k x v) k sl' $$ [Hrest Hsl' Hcap' Hits Committed]
  · iframe Hrest
    unfold keyInv keyOwn
    iexists l0 ++ [(item_ptr, (v, x, false))]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe Hsl' Hcap'
    isplitl [Hits Committed]
    · iapply (BigSepL.bigSepL_snoc).2
      iframe Hits
      unfold itemOwn itemPtr
      iframe Committed
      isplitr
      · ipureintro; exact Hnn
      iframe #
    · ipureintro
      refine ⟨by simp, ?_⟩
      rw [items_write_self, Hl0.1]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hγ Hmap]
  · inext
    iexists <[k := sl']> m, S0.write k x v
    iframe
    ipureintro
    intro k' hk'
    have hne : k' ≠ k := by
      intro e; subst e; rw [GMap.lookup_insert_eq] at hk'; cases hk'
    rw [GMap.lookup_insert_ne m sl' (Ne.symm hne)] at hk'
    rw [items_write_ne S0 k k' x v hne]
    exact Hnone k' hk'
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iapply HΦ
  itrivial

end proofs

end kvp

end github_com.despreston.go_craq

end Perennial
