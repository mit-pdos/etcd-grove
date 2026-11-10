/- Lean-first (no Rocq counterpart).

The proof of `call(s, in)`: the background context (`client.background_ctx`), a fresh `*Obj` for
the answer, then by the input's kind the store's `Create` (of `&Obj{Name, Value}`, at resource
version `0`), `Delete` (with `validateFor`'s closure, `validateD_ok`), `GuaranteedUpdate` (with
`tryUpdateFor`'s, `tryUpdateD_ok`) or `Get`, each at the store key (`storeKey`, whose etcd key is
the model's). An error of unknown outcome is `EOther` (`unkErr_errIs`); any other answer is the
store's model's (`respIs_call`): an error `errOut` places, or the object `objOut` reads.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preconditions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cachedObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.call
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.objOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.validateFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.tryUpdateFor
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Create
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Delete
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GuaranteedUpdate
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOut
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetList
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListContract
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- `call`'s end, from the answer `Hy` (see the file header): an error `errOut` places, or the
object `out` points to, `objOut`'s. -/
local macro "call_tail" : tactic => `(tactic| (
  icases Hy with ⟨%y, (⟨%Hne, Hey⟩ | ⟨%He, %p, %o, %Ho, Hp⟩), HQ⟩
  · cases err0 with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_errOut _ _ $$ [Hey]
      · iframe Hey
      iintro -
      (try wp_auto)
      iapply HΦ
      isplitl [Htt]
      · iexact Htt
      iexact HQ
  · subst He
    obtain ⟨hp, ho⟩ := Ho
    subst ho
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at hp
    cases GoGlobalContext.intoVal_inj_loc hp
    wp_auto
    wp_apply wp_objOut
    iapply HΦ
    isplitl [Htt]
    · iexact Htt
    iexact HQ))

/-- The cached object `cachedObj(in)` passes the store: the input's (`dobjOf`), at its resource
version, if it uses one. -/
private def caOf (x : Input) : Option (DObj × w64) :=
  if x.UseCached' then some (dobjOf x.Cached', x.Cached'.ResourceVersion') else none

/-- **`cachedObj(in)` is the store's cached object** (`cachedOk`) of `caOf in`, from `cachedIn`. -/
private theorem cachedOk_of (c : StoreCfg GF DObj) (hc : c.S = driverSpec) (x : Input)
    (key : GoString) (hk : c.pfx <+: key) (cx : GoInterface) :
    cachedIn c x ∗ (if x.UseCached' then
        iprop(∃ p : Loc, ⌜cx = interface.mkOk (go.GoType.PointerType objTyD) #p⌝ ∗ p ↦ x.Cached')
      else iprop(⌜cx = GoInterface.nil⌝)) ⊢ cachedOk c key cx (caOf x) := by
  unfold cachedIn caOf cachedObjOk cachedOk
  cases hu : x.UseCached'
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨-, %h⟩
    ipureintro; exact h
  · simp only [↓reduceIte]
    iintro ⟨⟨%hl, #Hv⟩, ⟨%p, %hp, Hp⟩⟩
    isplitr
    · ipureintro; exact hl.2.1
    isplitl [Hp]
    · have e : x.Cached' = (dobjOf x.Cached').toObj x.Cached'.ResourceVersion' := by
        unfold dobjOf; rw [dif_pos hl.1, DObj.ofObj_toObj_rv _ _ hl.2.2]
      rw [hp, hc, show (driverSpec (GF := GF)).objAt = objAtD from rfl,
        show (driverSpec (GF := GF)).fmtRV = rvStr from rfl]
      iapply (objAtD_pt (GF := GF) p (dobjOf x.Cached') x.Cached'.ResourceVersion')
      rw [← e]
      iexact Hp
    · iapply Hv; ipureintro; exact hk

/-- An object of a value at most `2 ^ 20` bytes fits a request when stored. -/
private theorem storedSize_small (o : DObj) (hv : o.val.length ≤ 2 ^ 20) :
    driverCodec.storedSizeOk o := by
  intro v hv'
  cases hv'
  show (encodeWith tagV1 (o.toObj 0)).length ≤ 2 ^ 28
  obtain ⟨h1, h2, h3, h4, h5⟩ := o.fits
  simp [encodeWith, putF, tagV1]; omega

/-- `updObj`'s value: the object's (a no-op, the object itself) or the input's. -/
private theorem updObj_cases (x : Input) (o : DObj) :
    updObj x o = o ∨ (updObj x o).val = x.Val' := by
  unfold updObj
  split
  · by_cases hn : x.NoOp' = true
    · left; rw [DObj.ext_iff']; simp [DObj.ofObj, updGo, hn]
    · right; simp [DObj.ofObj, updGo, hn]
  · left; rfl

/-- A list's error is not `nil`. -/
private theorem listErr_ne (c : StoreCfg GF DObj) (err : GoInterface) :
    listErr c err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  iintro #He
  iunfold listErr at He
  icases He with (#Hu | ⟨%st, #Hw, -⟩)
  · iapply unkErr_ne c err $$ Hu
  iunfold apierrors.apiErrAt at Hw
  icases Hw with ⟨%l, %hl, -⟩
  ipureintro; rw [hl]; nofun

/-- The Go items of a list answer's items are their objects at their resource versions. -/
private theorem forall2_itemRelD (l : List (DObj × Nat)) (vs : List Obj)
    (h : List.Forall₂ itemRelD (l.map fun p => (p.1, rvStr (W64 (p.2 : Int)))) vs) :
    vs = l.map fun p => p.1.toObj (W64 (p.2 : Int)) := by
  induction l generalizing vs with
  | nil => cases h; rfl
  | cons p l ih =>
    simp only [List.map_cons] at h
    cases h with
    | cons hr ht =>
      obtain ⟨n, hv, hs⟩ := hr
      rw [hv, ih _ ht, rvStr_inj hs.symm]
      rfl

/-- **`listOut` of a list answer is the driver's** (`listIs`'s items, token and remaining count,
`listOutDriver`). -/
private theorem listObjOut_eq (x : Input) (R : w64) (k : GoString)
    (hk : prepareKeyM go!"/objs" x.ListKey' x.Recursive' = some k)
    (a : ListModel.LState w8 (DObj × Nat)) (vs : List Obj)
    (hf : List.Forall₂ itemRelD (a.items.reverse.map fun p => (p.1, rvStr (W64 (p.2 : Int)))) vs) :
    listObjOutL vs R (if a.more then encL (a.last.getD [] ++ [W8 0]) (go!"/registry" ++ k) R else [])
      (if a.more ∧ predEmptyL x then some (W64 (a.total : Int) - x.Limit') else none) =
    listOutDriver x R a := by
  rw [forall2_itemRelD _ _ hf]
  unfold listOutDriver listObjOutL
  rw [hk]
  cases a.more <;> cases predEmptyL x <;> simp

set_option hygiene false in
/-- A list's too-large answer (`Htl`, at `σ` with `hlt`): `errOut`'s `ETooLarge`, `lOut`'s. -/
local macro "list_tl" : tactic => `(tactic| (
  ihave %Hp := apierrors.tooLargeErrIs_ptr err0 $$ Htl
  obtain ⟨lp, rfl⟩ := Hp
  wp_auto
  wp_apply wp_errOut _ tooLargeL $$ [Htl]
  · iunfold errIs; iright; iright; iright; ileft; iframe Htl; ipureintro; rfl
  (try iintro -)
  (try wp_auto)
  iapply HΦ
  iframe Htt
  iright
  iexists σ
  rw [if_pos h4]
  isplitr
  · iexists R'
    iframe HQ1
    ipureintro; exact Or.inl rfl
  ipureintro
  rw [callOut, if_pos h4, hout, if_pos hlt]))

set_option hygiene false in
/-- A list's answer (`Hl`, at `σ` with `hlt`, `he`): `listOut`'s, `lOut`'s. -/
local macro "list_ok" : tactic => `(tactic| (
  subst he
  iunfold listIs at Hl
  iunfold ListSpec.listAt at Hl
  icases Hl with ⟨%pl, %hpl, Hl⟩
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at hpl
  cases GoGlobalContext.intoVal_inj_loc hpl.2
  wp_auto
  wp_apply wp_listOut $$ [Hl] as %y %Hy
  · iframe #; iexact Hl
  (try wp_auto)
  iapply HΦ
  iframe Htt
  iright
  iexists σ
  rw [if_pos h4]
  isplitr
  · iexists R'
    iframe HQ1
    ipureintro; exact Or.inr (HR'.resolve_left hlt)
  ipureintro
  rw [callOut, if_pos h4, hout, if_neg hlt]
  obtain ⟨vs, hf, rfl⟩ := Hy
  rw [hc, hpre] at hf ⊢))

/-- The background context is never done (its `Done` returns `nil`). -/
private theorem background_neverDone :
    ⊢ ctxNeverDone (GF := GF) (GoInterface.ok context.backgroundCtxVal) := by
  unfold ctxNeverDone
  iexists context.backgroundCtxVal
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  wp_apply context.wp_background_Done
  iapply HΦ

theorem call.wp_proof (wp_errOut : errOut.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_splitKey : splitKey.spec (GF := GF) (hG := hG))
    (wp_preconditions : preconditions.spec (GF := GF) (hG := hG))
    (wp_validateFor : validateFor.spec (GF := GF) (hG := hG))
    (wp_cachedObj : cachedObj.spec (GF := GF) (hG := hG))
    (wp_tryUpdateFor : tryUpdateFor.spec (GF := GF) (hG := hG))
    (wp_Create : store.Create.spec (GF := GF) (hG := hG))
    (wp_Delete : store.Delete.spec (GF := GF) (hG := hG))
    (wp_Update : store.GuaranteedUpdate.spec (GF := GF) (hG := hG))
    (wp_Get : store.Get.spec (GF := GF) (hG := hG))
    (wp_listOptions : listOptions.spec (GF := GF) (hG := hG))
    (wp_listOut : listOut.spec (GF := GF) (hG := hG))
    (wp_GetList : store.GetList.spec (GF := GF) (hG := hG))
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_Empty : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG))
    (wp_GetItemsPtr : apimeta.GetItemsPtr.spec (GF := GF) (hG := hG))
    (wp_MakeSlice : reflect.MakeSlice.spec (GF := GF) (hG := hG))
    (wp_Copy : reflect.Copy.spec (GF := GF) (hG := hG))
    (wp_Append : reflect.Append.spec (GF := GF) (hG := hG))
    (wp_DecodeListItem : decoder.DecodeListItem.spec (GF := GF) (hG := hG))
    (wp_UpdateList : versioner.UpdateList.spec (GF := GF) (hG := hG)) :
    call.spec (GF := GF) (hG := hG) := by
  intro _ _ _ sp c eD eU x W _ Φu Q QL PL hc hrp hdi hvi hAs hse htb hnr hkey hpp hx hvl hD1 hQ hQL hQLP
  have hkl : (c.pathPrefix ++ storeKeyL x.Key').length ≤ 2 ^ 27 := by
    rw [hpp]; have := wkKeysL_len _ hx.1; simp [mkeyL, storeKeyL]; omega
  wp_start as ⟨#Hst, #HD, #HU, #Hca, #Hrs, Htt, Hpre⟩
  wp_auto
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, #HvD, #HvU⟩
  by_cases h4 : x.Kind' = W64 4
  · -- List
    isimp only [if_pos h4] at Hpre
    iunfold listPre at Hpre
    icases Hpre with ⟨HQm, #HPm⟩
    obtain ⟨hm, hlk, hlim, hks, hkl4⟩ := hx.2.2.2.2.2 h4
    obtain ⟨n, hn, hn63⟩ := hx.2.2.2.2.1
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hks
    rw [decide_eq_true h4]
    wp_auto
    wp_apply wp_listOptions
    (try wp_auto)
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hl0, %Hn0⟩
    iStructNamed Hl0
    have e1 : (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList).Items' = slice.nil := rfl
    have e2 : (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList).ResourceVersion' =
      (0 : w64) := rfl
    have e3 : (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList).Continue' = [] := rfl
    have e4 : (zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList).RemainingItemCount' =
      null := rfl
    isimp only [e1] at Items
    isimp only [e2] at ResourceVersion
    isimp only [e3] at Continue
    isimp only [e4] at RemainingItemCount
    ihave Hlist : (driverListSpec (GF := GF)).listAt
        (interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty)
          #«$r0_ptr») [] 0 [] none $$ [Items ResourceVersion Continue RemainingItemCount]
    · unfold ListSpec.listAt ListSpec.listAtItems driverListSpec
      iexists «$r0_ptr»
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact Hn0
      iexists slice.nil
      isplitl [Items]
      · iexact Items
      isplitr
      · iapply (itemsAtD_nil (GF := GF))
      unfold metaAtD
      dsimp only
      iframe ResourceVersion Continue
      iexists null
      iframe RemainingItemCount
      unfold remIs
      ipureintro; rfl
    ihave #Hsel := predOk_driver wp_Matches wp_Empty wp_LM wp_LE wp_FM wp_FE wp_GA x $$ Hpkg
    ihave #Hlc := driver_listContractOk wp_GetItemsPtr wp_MakeSlice wp_Copy wp_Append
      wp_DecodeListItem wp_UpdateList c hc hdi hvi $$ [Hpkg]
    · iframe Hpkg; isplitr <;> iPkgInit
    ihave #Hnd := background_neverDone (GF := GF)
    have hpre : c.pathPrefix = go!"/registry" := by
      unfold mkeyL at hpp; exact List.append_cancel_right hpp
    have hkk := prepareKeyM_eq _ _ _ _ hk
    wp_apply (wp_GetList DObj sp c driverListSpec context.backgroundCtxVal cd x.ListKey' (listOptsV x)
        _ 0 [] none k n (selD x) (predEmptyL x) QL PL hQL hQLP hnr) $$ [Hlist Htt HQm] as %err0 ⟨Htt, Hres⟩
    · rw [hc]
      iframe #
      iframe Htt Hlist HQm
      isplitr
      · ipureintro
        refine ⟨by rw [hrp]; exact hk, ?_, hn, ?_, rfl, hn63, hlim⟩
        · rw [hpre, hkk]; unfold opKeyMax; split <;> simp <;> omega
        · simp only [listOptsV, matchOptL]
          split
          · simp
          · split <;> simp
      isplitr
      · unfold listOptsV; dsimp only; iexact Hsel
      ipureintro; exact htb
    icases Hres with (⟨#Herr, -⟩ | ⟨%R', %σ, #HQ1, %HR', Hr⟩)
    · -- an error of unknown outcome
      ihave %Hne := listErr_ne c err0 $$ Herr
      ihave Hy := listErr_errIs hse c hc err0 $$ [Herr]
      · iframe #
      cases err0 with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_errOut _ _ $$ [Hy]
        · iframe Hy
        iintro -
        (try wp_auto)
        iapply HΦ
        iframe Htt
        ileft; ipureintro; rfl
    have hRn : uint.Z (listRevL (matchOptL x) x.Recursive' x.Limit' n) ≠ 0 →
        listRevL (matchOptL x) x.Recursive' x.Limit' n = n := by
      intro h
      unfold listRevL at h ⊢
      by_cases h1 : matchOptL x = go!"Exact"
      · rw [if_pos h1]
      · rw [if_neg h1] at h ⊢
        by_cases h2 : (matchOptL x = [] ∧ x.Recursive' = true ∧ 0 < sint.Z x.Limit' ∧ 0 < uint.Z n)
        · rw [if_pos h2]
        · rw [if_neg h2] at h; exact absurd (by simp) h
    have hout : lOut x σ =
        let R := listRevL (matchOptL x) x.Recursive' x.Limit' n
        if σ.rev < uint.nat n then tooLargeL
        else listOutDriver x (if uint.Z R = 0 then W64 (σ.rev : Int) else R)
          (kListL driverCodec.dec (selD x) (limN x.Limit') (go!"/registry" ++ k) x.Recursive'
            (if uint.Z R = 0 then σ.store else σ.at (uint.nat R))) := by
      unfold lOut; rw [hn, hk]
    by_cases hR0 : uint.Z (listRevL (matchOptL x) x.Recursive' x.Limit' n) = 0
    · isimp only [if_pos hR0] at Hr
      by_cases hlt : σ.rev < uint.nat n
      · isimp only [if_pos hlt] at Hr
        icases Hr with ⟨#Htl, -⟩
        list_tl
      · isimp only [if_neg hlt] at Hr
        icases Hr with ⟨%he, Hl⟩
        list_ok
        simp only [if_pos hR0]
        exact listObjOut_eq x _ k hk _ vs hf
    · isimp only [if_neg hR0] at Hr
      isimp only [hRn hR0] at Hr
      by_cases hlt : σ.rev < uint.nat n
      · isimp only [if_pos hlt] at Hr
        icases Hr with ⟨#Htl, -⟩
        list_tl
      · isimp only [if_neg hlt] at Hr
        icases Hr with ⟨%he, Hl⟩
        list_ok
        simp only [if_neg hR0]
        rw [hRn hR0]
        exact listObjOut_eq x _ k hk _ vs hf
  isimp only [if_neg h4] at Hpre
  rw [decide_eq_false h4]
  wp_auto
  have hob : ∀ (p : Loc) (o : DObj) (n : w64),
      (p ↦ o.toObj n : IProp GF) ⊢
        c.S.objAt (interface.mkOk (go.GoType.PointerType objTyD) #p) o (rvStr n) := by
    intro p o n; rw [hc]; exact objAtD_pt p o n
  have hmk : ∀ n, (mkObj x).toObj n = crObjL x n := mkObj_toObj x (inOk_crFits x hx)
  irename : («$r0_ptr» ↦ zero_val Obj : IProp GF) => Hr0
  have hz : (zero_val Obj) = dzero.toObj 0 := rfl
  by_cases h0 : x.Kind' = W64 0
  · -- Create
    rw [decide_eq_true h0]
    iunfold callPre at Hpre
    isimp only [h0, ↓reduceIte] at Hpre
    wp_auto
    wp_apply wp_splitKey
    (try wp_auto)
    wp_apply wp_storeKey
    (try wp_auto)
    wp_alloc p1 as Hp1
    (try wp_auto)
    ihave Hobj := hob p1 (mkObj x) 0 $$ [Hp1]
    · rw [hmk 0]; unfold crObjL; iexact Hp1
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · rw [← hz]; iexact Hr0
    wp_apply (wp_Create DObj sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #p1) (mkObj x) (rvStr 0)
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0) (storeKeyL x.Key')
        Φu hkey hkl
        (by
          rw [hc]; exact storedSize_small _ (by
            show ((mkObj x).toObj 0).Value'.length ≤ _
            rw [hmk 0]; exact hvl))
        (by rw [hc]; exact parseRVD_rvStr 0)) $$ [Hobj Hout Hpre] as %err0 ⟨-, Hres⟩
    · iframe #
      iframe Hobj Hout
      rw [hpp]
      iexact Hpre
    -- the answer, as an error `errOut` places or the object `out` points to
    ihave Hy : (∃ y : Output, ((⌜err0 ≠ GoInterface.nil⌝ ∗ errIs err0 y) ∨
        (⌜err0 = GoInterface.nil⌝ ∗ ∃ (p : Loc) (o : Obj),
          ⌜interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr» =
            interface.mkOk (go.GoType.PointerType objTyD) #p ∧ objOutL o = y⌝ ∗ p ↦ o)) ∗
        (⌜y = otherL⌝ ∨ ∃ σ, (if x.Kind' = W64 4 then
          iprop(∃ R : w64, □ QL R σ ∗ ⌜y = tooLargeL ∨ R = W64 (σ.rev : Int)⌝)
          else callAt x Φu Q σ) ∗ ⌜y = callOut c eD eU x σ⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, HΦ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists otherL
        isplitl [Hy]
        · ileft
          iframe Hy
          ipureintro; exact Hne
        ileft; ipureintro; rfl
      · ihave Hy := respIs_call c hc
          ((c.abs σ).create (E := Empty) (c.pathPrefix ++ storeKeyL x.Key') (mkObj x) 0).2 err0 _
          eD eU (create_noOdd _ _ _) (fun e _ _ _ => nomatch e) $$ [HD HU Hr]
        · iframe Hpkg HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [if_neg h4]
        unfold callAt
        simp only [h0, true_or, ↓reduceIte]
        iframe HΦ1
        ipureintro
        simp [callOut, h4, kStep, h0, hpp]
    call_tail
  rw [decide_eq_false h0]
  wp_auto
  by_cases h1 : x.Kind' = W64 1
  · -- Delete
    rw [decide_eq_true h1]
    iunfold callPre at Hpre
    isimp only [if_neg h0, if_pos h1] at Hpre
    icases Hpre with ⟨HW, Haus⟩
    wp_auto
    wp_apply wp_storeKey
    (try wp_auto)
    wp_apply wp_preconditions as %pp #Hpp
    (try wp_auto)
    wp_apply wp_validateFor as %vf #Hvf
    (try wp_auto)
    wp_apply wp_cachedObj as %cx Hcx
    (try wp_auto)
    have hpfx : c.pfx <+: c.pathPrefix ++ storeKeyL x.Key' := prepareKeyM_prefix _ _ _ _ _ hkey
    ihave Hco := cachedOk_of c hc x _ hpfx cx $$ [Hca Hcx]
    · iframe Hca Hcx
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · rw [← hz]; iexact Hr0
    ihave #Hval := validateD_ok c hc eD x.HasReject' x.Reject' vf $$ [HvD HD Hvf]
    · iframe #
    wp_apply (wp_Delete DObj GoInterface sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0) pp (kpreOf x)
        cx (caOf x) (zero_val _) (rejD eD x.HasReject' x.Reject') vf W Φu (storeKeyL x.Key'))
        $$ [Hout HW Haus Hco] as %err0 Hres
    · iframe #
      iframe Hout HW Hco
      isplitr
      · ipureintro; exact ⟨hkey, hkl, rfl⟩
      rw [hpp, hc, show (driverSpec (GF := GF)).preOk (kpreOf x) = preD x from rfl]
      iexact Haus
    iunfold delOut at Hres
    ihave Hy : (∃ y : Output, ((⌜err0 ≠ GoInterface.nil⌝ ∗ errIs err0 y) ∨
        (⌜err0 = GoInterface.nil⌝ ∗ ∃ (p : Loc) (o : Obj),
          ⌜interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr» =
            interface.mkOk (go.GoType.PointerType objTyD) #p ∧ objOutL o = y⌝ ∗ p ↦ o)) ∗
        (⌜y = otherL⌝ ∨ ∃ σ, (if x.Kind' = W64 4 then
          iprop(∃ R : w64, □ QL R σ ∗ ⌜y = tooLargeL ∨ R = W64 (σ.rev : Int)⌝)
          else callAt x Φu Q σ) ∗ ⌜y = callOut c eD eU x σ⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, HΦ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists otherL
        isplitl [Hy]
        · ileft
          iframe Hy
          ipureintro; exact Hne
        ileft; ipureintro; rfl
      · ihave Hy := respIs_call c hc
          ((c.abs σ).delete (c.pathPrefix ++ storeKeyL x.Key') (c.S.preOk (kpreOf x))
            (rejD eD x.HasReject' x.Reject')).2 err0 _ eD eU (delete_noOdd _ _ _ _ _ _)
          (fun e e' h he => Or.inl ((show e' = e from he).trans (delete_user _ _ _ _ _ _ _ h)))
          $$ [HD HU Hr]
        · iframe Hpkg HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [if_neg h4]
        rw [callAt, if_pos (Or.inr (Or.inl h1))]
        iframe HΦ1
        ipureintro
        simp [callOut, h4, kStep, h0, h1, hpp, hc, driverSpec]
    call_tail
  rw [decide_eq_false h1]
  wp_auto
  have hz0 : c.S.zero = dzero := by rw [hc]; rfl
  by_cases h2 : x.Kind' = W64 2
  · -- GuaranteedUpdate
    rw [decide_eq_true h2]
    iunfold callPre at Hpre
    isimp only [if_neg h0, if_neg h1, if_pos h2] at Hpre
    icases Hpre with ⟨HW, Haus⟩
    wp_auto
    wp_apply wp_storeKey
    (try wp_auto)
    wp_apply wp_preconditions as %pp #Hpp
    (try wp_auto)
    wp_apply wp_tryUpdateFor x (inOk_inFits x hx) as %uf #Huf
    (try wp_auto)
    wp_apply wp_cachedObj as %cx Hcx
    (try wp_auto)
    have hpfx : c.pfx <+: c.pathPrefix ++ storeKeyL x.Key' := prepareKeyM_prefix _ _ _ _ _ hkey
    ihave Hco := cachedOk_of c hc x _ hpfx cx $$ [Hca Hcx]
    · iframe Hca Hcx
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · rw [← hz]; iexact Hr0
    ihave #Hupd := tryUpdateD_ok c hc eU x uf $$ [HvU HU Huf]
    · iframe #
    have hsz : ∀ (w d : GoString) (stl : Bool) (o : DObj) (n : Nat) (o' : DObj),
        w.length ≤ etcdKeyMax → c.S.fromS w = some (d, stl) → c.S.decode d = some o →
        updD eU x o n = .ok o' → (stl = true ∨ c.S.encode o' ≠ d) → c.S.storedSizeOk o' := by
      intro w d stl o n o' hw hfs hdec h _
      rw [hc] at hfs hdec ⊢
      unfold updD at h
      split at h
      · cases h
      cases h
      rcases updObj_cases x o with he | he
      · -- a no-op update writes the object read, re-encoded (a `v0:` value as `v1:`): as long
        -- as the stored value, within etcd's limit
        rw [he]
        change some (w, false) = some (d, stl) at hfs
        cases hfs
        intro v hv
        cases hv
        show (encodeWith tagV1 (o.toObj 0)).length ≤ 2 ^ 28
        rw [decodeObjD_encode_length _ o 0 hdec]
        unfold etcdKeyMax at hw
        omega
      · exact storedSize_small _ (by rw [he]; exact hvl)
    have hzs : x.IgnoreNotFound' = true → ∀ o', updD eU x c.S.zero 0 = .ok o' →
        c.S.storedSizeOk o' := by
      intro _ o' h
      rw [hz0] at h
      rw [hc]
      unfold updD at h
      split at h
      · cases h
      cases h
      rcases updObj_cases x dzero with he | he
      · rw [he]; exact storedSize_small _ (by decide)
      · exact storedSize_small _ (by rw [he]; exact hvl)
    have hcs : ∀ o r o', caOf x = some (o, r) → updD eU x o (uint.nat r) = .ok o' →
        c.S.encode o' ≠ c.S.encode o → c.S.storedSizeOk o' := by
      intro o r o' _ h hne
      rw [hc] at hne ⊢
      unfold updD at h
      split at h
      · cases h
      cases h
      rcases updObj_cases x o with he | he
      · exact absurd (by rw [he]) hne
      · exact storedSize_small _ (by rw [he]; exact hvl)
    have hscope : ∀ o r, caOf x = some (o, r) →
        (kpreOf x).rv = none ∧ ∀ n, updD eU x o n = updD eU x o (uint.nat r) := by
      intro o r h
      unfold caOf at h
      split at h
      · next hu =>
        refine ⟨?_, fun _ => rfl⟩
        simp [kpreOf, hD1 hu h2]
      · cases h
    wp_apply (wp_Update DObj GoInterface sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0)
        x.IgnoreNotFound' pp (kpreOf x) cx (caOf x) (updD eU x) uf W Φu (storeKeyL x.Key'))
        $$ [Hout HW Haus Hco] as %err0 Hres
    · iframe #
      iframe Hout HW Hco
      isplitr
      · ipureintro; exact ⟨hkey, hkl, hsz, hzs, hcs, hscope⟩
      rw [hpp, hz0, hc, show (driverSpec (GF := GF)).preOk (kpreOf x) = preD x from rfl]
      iexact Haus
    iunfold updOut at Hres
    rw [hz0] at *
    ihave Hy : (∃ y : Output, ((⌜err0 ≠ GoInterface.nil⌝ ∗ errIs err0 y) ∨
        (⌜err0 = GoInterface.nil⌝ ∗ ∃ (p : Loc) (o : Obj),
          ⌜interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr» =
            interface.mkOk (go.GoType.PointerType objTyD) #p ∧ objOutL o = y⌝ ∗ p ↦ o)) ∗
        (⌜y = otherL⌝ ∨ ∃ σ, (if x.Kind' = W64 4 then
          iprop(∃ R : w64, □ QL R σ ∗ ⌜y = tooLargeL ∨ R = W64 (σ.rev : Int)⌝)
          else callAt x Φu Q σ) ∗ ⌜y = callOut c eD eU x σ⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, HΦ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists otherL
        isplitl [Hy]
        · ileft
          iframe Hy
          ipureintro; exact Hne
        ileft; ipureintro; rfl
      · ihave Hy := respIs_call c hc
          ((c.abs σ).update (c.pathPrefix ++ storeKeyL x.Key') x.IgnoreNotFound' dzero
            (c.S.preOk (kpreOf x)) (updD eU x)).2 err0 _ eD eU (update_noOdd _ _ _ _ _ _)
          (fun e e' h he => Or.inr ((show e' = e from he).trans (update_user _ _ _ _ _ _ _ h)))
          $$ [HD HU Hr]
        · iframe Hpkg HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [if_neg h4]
        rw [callAt, if_pos (Or.inr (Or.inr h2))]
        iframe HΦ1
        ipureintro
        simp [callOut, h4, kStep, h0, h1, h2, hpp, hc, driverSpec]
    call_tail
  · -- Get
    rw [decide_eq_false h2]
    iunfold callPre at Hpre
    isimp only [if_neg h0, if_neg h1, if_neg h2] at Hpre
    wp_auto
    wp_apply wp_storeKey
    (try wp_auto)
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · rw [← hz]; iexact Hr0
    have hparse : c.S.parseRV x.MinRV' = some (minOf x) := by
      rw [hc]
      obtain ⟨n, hn, -⟩ := hx.2.2.2.2.1
      show parseRVD x.MinRV' = some (minOf x)
      unfold minOf; rw [hn]; rfl
    wp_apply (wp_Get DObj sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        ⟨x.IgnoreNotFound', x.MinRV'⟩ (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr»)
        dzero (rvStr 0) (storeKeyL x.Key') (minOf x) Q hQ) $$ [Hout Hpre] as %err0 Hres
    · iframe #
      iframe Hout Hpre
      ipureintro; exact ⟨hkey, hkl, hparse⟩
    ihave Hy : (∃ y : Output, ((⌜err0 ≠ GoInterface.nil⌝ ∗ errIs err0 y) ∨
        (⌜err0 = GoInterface.nil⌝ ∗ ∃ (p : Loc) (o : Obj),
          ⌜interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr» =
            interface.mkOk (go.GoType.PointerType objTyD) #p ∧ objOutL o = y⌝ ∗ p ↦ o)) ∗
        (⌜y = otherL⌝ ∨ ∃ σ, (if x.Kind' = W64 4 then
          iprop(∃ R : w64, □ QL R σ ∗ ⌜y = tooLargeL ∨ R = W64 (σ.rev : Int)⌝)
          else callAt x Φu Q σ) ∗ ⌜y = callOut c eD eU x σ⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, #HQ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists otherL
        isplitl [Hy]
        · ileft
          iframe Hy
          ipureintro; exact Hne
        ileft; ipureintro; rfl
      · ihave Hy := respIs_call c hc
          ((c.abs σ).get (E := Empty) (c.pathPrefix ++ storeKeyL x.Key') (uint.nat (minOf x))
            x.IgnoreNotFound') err0 _
          eD eU (get_noOdd _ _ _ _) (fun e _ _ _ => nomatch e) $$ [HD HU Hr]
        · iframe Hpkg HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [if_neg h4]
        have hk : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
          rintro (h | h | h) <;> contradiction
        rw [callAt, if_neg hk, ← hpp]
        iframe HQ1
        ipureintro
        rw [callOut, if_neg h4, kStep, if_neg h0, if_neg h1, if_neg h2, hpp]
    call_tail

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
