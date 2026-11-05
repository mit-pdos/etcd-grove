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
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.validateFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.tryUpdateFor
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Create
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Delete
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GuaranteedUpdate
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Get
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
      iexact HQ
  · subst He
    obtain ⟨hp, ho⟩ := Ho
    subst ho
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at hp
    cases GoGlobalContext.intoVal_inj_loc hp
    wp_auto
    wp_apply wp_objOut
    iapply HΦ
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
    · ipureintro; exact hl.2.2
    isplitl [Hp]
    · have e : x.Cached' = github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk
          (dobjOf x.Cached').name (dobjOf x.Cached').uid (dobjOf x.Cached').val
          x.Cached'.ResourceVersion' := by
        have hd : dobjOf x.Cached' =
            (⟨(x.Cached'.Name', x.Cached'.UID', x.Cached'.Value'), ⟨hl.1, hl.2.1⟩⟩ : DObj) := by
          unfold dobjOf; exact dif_pos ⟨hl.1, hl.2.1⟩
        rw [hd]
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
  show (encodeWith tagV1 o.name o.uid o.val).length ≤ 2 ^ 28
  have h1 : o.name.length < 256 := o.2.1
  have h2 : o.uid.length < 256 := o.2.2
  simp [encodeWith]; omega

/-- `updObj`'s value: the object's (a no-op, the object itself) or the input's. -/
private theorem updObj_cases (x : Input) (o : DObj) :
    updObj x o = o ∨ (updObj x o).val = x.Val' := by
  unfold updObj
  by_cases hn : x.NoOp' = true
  · exact .inl (if_pos hn)
  · rw [if_neg hn]
    by_cases hl : (updName x o).length < 256
    · simp only [hl, ↓reduceDIte]; exact .inr trivial
    · simp only [hl, ↓reduceDIte]; exact .inr trivial

theorem call.wp_proof (wp_errOut : errOut.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_preconditions : preconditions.spec (GF := GF) (hG := hG))
    (wp_validateFor : validateFor.spec (GF := GF) (hG := hG))
    (wp_cachedObj : cachedObj.spec (GF := GF) (hG := hG))
    (wp_tryUpdateFor : tryUpdateFor.spec (GF := GF) (hG := hG))
    (wp_Create : store.Create.spec (GF := GF) (hG := hG))
    (wp_Delete : store.Delete.spec (GF := GF) (hG := hG))
    (wp_Update : store.GuaranteedUpdate.spec (GF := GF) (hG := hG))
    (wp_Get : store.Get.spec (GF := GF) (hG := hG)) :
    call.spec (GF := GF) (hG := hG) := by
  intro _ _ _ sp c eD eU x W _ Φu Q hc hAs hse hkey hpp hx hvl hD1 hQ
  have hkl : (c.pathPrefix ++ storeKeyL x.Key').length ≤ 2 ^ 27 := by
    rw [hpp]; unfold InOk at hx; simp [mkeyL, storeKeyL]; omega
  wp_start as ⟨#Hst, #HD, #HU, #Hca, Hpre⟩
  wp_auto
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  have hob : ∀ (p : Loc) (o : DObj) (n : w64),
      (p ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk o.name o.uid o.val n : IProp GF) ⊢
        c.S.objAt (interface.mkOk (go.GoType.PointerType objTyD) #p) o (rvStr n) := by
    intro p o n; rw [hc]; exact objAtD_pt p o n
  have hmk : mkObj x = ⟨(x.Key', x.UID', x.Val'), ⟨hx.1, hx.2.1⟩⟩ := dif_pos ⟨hx.1, hx.2.1⟩
  irename : («$r0_ptr» ↦ zero_val Obj : IProp GF) => Hr0
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, #HvD, #HvU⟩
  have hz : (zero_val Obj) = github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk
      dzero.name dzero.uid dzero.val 0 := rfl
  by_cases h0 : x.Kind' = W64 0
  · -- Create
    rw [decide_eq_true h0]
    iunfold callPre at Hpre
    isimp only [h0, ↓reduceIte] at Hpre
    wp_auto
    wp_apply wp_storeKey
    (try wp_auto)
    wp_alloc p1 as Hp1
    (try wp_auto)
    ihave Hobj := hob p1 (mkObj x) 0 $$ [Hp1]
    · rw [hmk]; iexact Hp1
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · have hz : (zero_val Obj) = github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk
          dzero.name dzero.uid dzero.val 0 := rfl
      rw [← hz]
      iexact Hr0
    wp_apply (wp_Create DObj sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #p1) (mkObj x) (rvStr 0)
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0) (storeKeyL x.Key')
        Φu hkey hkl
        (by
          rw [hc, hmk]; intro v hv; cases hv
          show (encodeWith tagV1 x.Key' x.UID' x.Val').length ≤ 2 ^ 28
          have := hx.1; have := hx.2.1; simp [encodeWith]; omega)
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
        (⌜y = errOutL⌝ ∨ ∃ σ, callAt x Φu Q σ ∗ ⌜y = (kStep eD eU x (c.abs σ)).2⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, HΦ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists errOutL
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
        unfold callAt
        simp only [h0, true_or, ↓reduceIte]
        iframe HΦ1
        ipureintro
        simp [kStep, h0, hpp]
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
    ihave #Hval := validateD_ok c hc eD x.Reject' vf $$ [HvD HD Hvf]
    · iframe #
    wp_apply (wp_Delete DObj GoInterface sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0) pp (kpreOf x)
        cx (caOf x) (zero_val _) (rejD eD x.Reject') vf W Φu (storeKeyL x.Key'))
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
        (⌜y = errOutL⌝ ∨ ∃ σ, callAt x Φu Q σ ∗ ⌜y = (kStep eD eU x (c.abs σ)).2⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, HΦ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists errOutL
        isplitl [Hy]
        · ileft
          iframe Hy
          ipureintro; exact Hne
        ileft; ipureintro; rfl
      · ihave Hy := respIs_call c hc
          ((c.abs σ).delete (c.pathPrefix ++ storeKeyL x.Key') (c.S.preOk (kpreOf x))
            (rejD eD x.Reject')).2 err0 _ eD eU (delete_noOdd _ _ _ _ _)
          (fun e e' h he => Or.inl ((show e' = e from he).trans (delete_user _ _ _ _ _ _ h)))
          $$ [HD HU Hr]
        · iframe Hpkg HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [callAt, if_pos (Or.inr (Or.inl h1))]
        iframe HΦ1
        ipureintro
        simp [kStep, h0, h1, hpp, hc, driverSpec]
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
    wp_apply wp_tryUpdateFor x hx.1 as %uf #Huf
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
        show (encodeWith tagV1 o.name o.uid o.val).length ≤ 2 ^ 28
        rw [decodeObjD_encode_length _ o hdec]
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
        (⌜y = errOutL⌝ ∨ ∃ σ, callAt x Φu Q σ ∗ ⌜y = (kStep eD eU x (c.abs σ)).2⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, HΦ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists errOutL
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
        rw [callAt, if_pos (Or.inr (Or.inr h2))]
        iframe HΦ1
        ipureintro
        simp [kStep, h0, h1, h2, hpp, hc, driverSpec]
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
      show parseRVD x.MinRV' = some (minOf x)
      have hs := hx.2.2
      unfold minOf
      cases h : parseRVD x.MinRV' with
      | none => rw [h] at hs; cases hs
      | some v => rfl
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
        (⌜y = errOutL⌝ ∨ ∃ σ, callAt x Φu Q σ ∗ ⌜y = (kStep eD eU x (c.abs σ)).2⌝) : IProp GF)
        $$ [Hres]
    · icases Hres with (⟨#Hu, -⟩ | ⟨%σ, #HQ1, Hr⟩)
      · ihave %Hne := unkErr_ne c err0 $$ Hu
        ihave Hy := unkErr_errIs hse c hc err0 $$ [Hu]
        · iframe #
        iexists errOutL
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
        have hk : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
          rintro (h | h | h) <;> contradiction
        rw [callAt, if_neg hk, ← hpp]
        iframe HQ1
        ipureintro
        rw [kStep, if_neg h0, if_neg h1, if_neg h2, hpp]
    call_tail

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
