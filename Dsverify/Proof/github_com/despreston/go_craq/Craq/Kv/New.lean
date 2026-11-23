/-
`kv.New`: an empty store.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.Write
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.Commit
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.ReadVersion
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.AllItems
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.AllNewerDirty
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.AllNewerCommitted

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

/-- `kv.New()` makes a store (`isKV`) with empty contents. -/
theorem wp_New_isKV :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv }}
      (App (Val (@! store.kv.New)) (Val #()))
    {{ (p : Loc), RET #p; ∃ γs : GName, isKV p γs ∗ storeOwn γs 1 ([] : StoreS) }} := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice)) as %mp Hm
  iStructNamed «$r0»
  imod ghostVar_alloc ([] : StoreS) with ⟨%γs, Hv⟩
  icases ghostVar_split γs ([] : StoreS) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod sync.init_Mutex (lockInv mp γs) ⊤ _ $$ mu [Hm Hv1] with #Hmu
  · inext
    unfold lockInv
    iexists ∅, []
    iframe
    isplitr
    · ipureintro; intro k _; rfl
    · iapply BigSepM.bigSepM_empty_intro (P := iprop(True)); itrivial
  ipersist items
  imodintro
  iapply HΦ
  iexists γs
  unfold isKV storeOwn
  iframe
  iexists mp
  iframe #

/-- A store `p` meets `isStore` (the interface's `isStore` over `storeOwn`). -/
theorem isKV_isStore (p : Loc) (γs : GName) :
    isKV (hG := hG) p γs ⊢ isStore (interface.mkOk (go.GoType.PointerType store.kv.KV.ty) #p) γs := by
  iintro #H
  unfold isStore
  iexists ⟨go.GoType.PointerType store.kv.KV.ty, #p⟩
  isplitr
  · ipureintro; rfl
  imodintro
  dsimp only
  isplit
  · iintro %k %sl %x %v #Hsl
    iapply wp_Write p γs k sl x v $$ H Hsl
  isplit
  · iintro %k %v
    iapply wp_Commit p γs k v $$ H
  isplit
  · iintro %k %v
    iapply wp_ReadVersion p γs k v $$ H
  isplit
  · iapply wp_AllCommitted p γs $$ H
  isplit
  · iapply wp_AllDirty p γs $$ H
  isplit
  · iintro %rq %req %dq0 Hrq
    iapply wp_AllNewerDirty p γs rq req dq0 $$ H Hrq
  · iintro %rq %req %dq0 Hrq
    iapply wp_AllNewerCommitted p γs rq req dq0 $$ H Hrq

/-- `kv.New()`: a store, empty (the lab's `kv.wp_New.spec`, `Specs.lean`). -/
theorem wp_New :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv }}
      (App (Val (@! store.kv.New)) (Val #()))
    {{ (p : Loc), RET #p; ∃ γs : GName,
        isStore (interface.mkOk (go.GoType.PointerType store.kv.KV.ty) #p) γs ∗
        storeOwn γs 1 ([] : StoreS) }} := by
  iintro %Φ Hpre HΦ
  iapply wp_New_isKV $$ Hpre
  inext
  iintro %p ⟨%γs, #Hkv, Hown⟩
  iapply HΦ
  iexists γs
  iframe Hown
  iapply isKV_isStore $$ Hkv

end proofs

end kvp


end github_com.despreston.go_craq

end Perennial
