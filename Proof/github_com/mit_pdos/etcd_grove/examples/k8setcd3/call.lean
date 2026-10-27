/- Lean-first (no Rocq counterpart).

The proof of `call(s, in)`: the background context (`client.background_ctx`), a fresh `*Obj` for
the answer, then by the input's kind the store's `Create` (of `&Obj{Name, Value}`, at resource
version `0`), `Delete` (with `validateFor`'s closure, `validateD_ok`), `GuaranteedUpdate` (with
`tryUpdateFor`'s, `tryUpdateD_ok`) or `Get`, each at the store key (`storeKey`, whose etcd key is
the model's). An error of unknown outcome is `EOther` (`unkErr_errIs`); any other answer is the
store's model's (`respIs_call`): an error `errOut` places, or the object `objOut` reads.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.call
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.errOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.objOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.validateFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.tryUpdateFor
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
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

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

theorem call.wp_proof (wp_errOut : errOut.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_validateFor : validateFor.spec (GF := GF) (hG := hG))
    (wp_tryUpdateFor : tryUpdateFor.spec (GF := GF) (hG := hG))
    (wp_Create : store.Create.spec (GF := GF) (hG := hG))
    (wp_Delete : store.Delete.spec (GF := GF) (hG := hG))
    (wp_Update : store.GuaranteedUpdate.spec (GF := GF) (hG := hG))
    (wp_Get : store.Get.spec (GF := GF) (hG := hG)) :
    call.spec (GF := GF) (hG := hG) := by
  intro _ _ _ sp c eD eU x W _ Φu Q hc hAs hse hkey hpp hx hQ
  wp_start as ⟨#Hst, #HD, #HU, Hpre⟩
  wp_auto
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  have hob : ∀ (p : Loc) (o : DObj) (n : w64),
      (p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk o.1.1 o.1.2 n : IProp GF) ⊢
        c.S.objAt (interface.mkOk (go.GoType.PointerType objTyD) #p) o (rvStr n) := by
    intro p o n; rw [hc]; exact objAtD_pt p o n
  have hmk : mkObj x = ⟨(x.Key', x.Val'), hx⟩ := dif_pos hx
  irename : («$r0_ptr» ↦ zero_val Obj : IProp GF) => Hr0
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, #HvD, #HvU⟩
  have hz : (zero_val Obj) = github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk
      dzero.1.1 dzero.1.2 0 := rfl
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
    · have hz : (zero_val Obj) = github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk
          dzero.1.1 dzero.1.2 0 := rfl
      rw [← hz]
      iexact Hr0
    wp_apply (wp_Create DObj sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #p1) (mkObj x) (rvStr 0)
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0) (storeKeyL x.Key')
        Φu hkey (by rw [hc]; exact parseRVD_rvStr 0)) $$ [Hobj Hout Hpre] as %err0 ⟨-, Hres⟩
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
        · iframe HD HU Hr
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
    wp_apply wp_validateFor as %vf #Hvf
    (try wp_auto)
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · rw [← hz]; iexact Hr0
    ihave #Hval := validateD_ok c hc eD x.Reject' vf $$ [HvD HD Hvf]
    · iframe #
    wp_apply (wp_Delete DObj GoInterface sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0) (zero_val _)
        (rejD eD x.Reject') vf W Φu (storeKeyL x.Key') hkey rfl) $$ [Hout HW Haus] as %err0 Hres
    · iframe #
      iframe Hout HW
      rw [hpp]
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
          ((c.abs σ).delete (c.pathPrefix ++ storeKeyL x.Key') (fun _ _ => none)
            (rejD eD x.Reject')).2 err0 _ eD eU (delete_noOdd _ _ _ _)
          (fun e e' h he => Or.inl ((show e' = e from he).trans (delete_user _ _ _ _ _ h))) $$ [HD HU Hr]
        · iframe HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [callAt, if_pos (Or.inr (Or.inl h1))]
        iframe HΦ1
        ipureintro
        simp [kStep, h0, h1, hpp]
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
    wp_apply wp_tryUpdateFor as %uf #Huf
    (try wp_auto)
    ihave Hout := hob _ dzero 0 $$ [Hr0]
    · rw [← hz]; iexact Hr0
    ihave #Hupd := tryUpdateD_ok c hc eU x uf $$ [HvU HU Huf]
    · iframe #
    wp_apply (wp_Update DObj GoInterface sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero (rvStr 0)
        (updD eU x) uf W Φu (storeKeyL x.Key') hkey) $$ [Hout HW Haus] as %err0 Hres
    · iframe #
      iframe Hout HW
      rw [hpp, hz0]
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
          ((c.abs σ).update (c.pathPrefix ++ storeKeyL x.Key') false dzero (fun _ _ => none)
            (updD eU x)).2 err0 _ eD eU (update_noOdd _ _ _ _)
          (fun e e' h he => Or.inr ((show e' = e from he).trans (update_user _ _ _ _ _ h)))
          $$ [HD HU Hr]
        · iframe HD HU Hr
        iexists _
        iframe Hy
        iright
        iexists σ
        rw [callAt, if_pos (Or.inr (Or.inr h2))]
        iframe HΦ1
        ipureintro
        simp [kStep, h0, h1, h2, hpp]
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
    wp_apply (wp_Get DObj sp c context.backgroundCtxVal cd (storeKeyL x.Key')
        ⟨x.IgnoreNotFound', []⟩ (interface.mkOk (go.GoType.PointerType objTyD) #«$r0_ptr») dzero
        (rvStr 0) (storeKeyL x.Key') Q hkey rfl hQ) $$ [Hout Hpre] as %err0 Hres
    · iframe #
      iframe Hout Hpre
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
          ((c.abs σ).get (E := Empty) (c.pathPrefix ++ storeKeyL x.Key') 0 x.IgnoreNotFound') err0 _
          eD eU (get_noOdd _ _ _) (fun e _ _ _ => nomatch e) $$ [HD HU Hr]
        · iframe HD HU Hr
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

end k8setcd3
end EtcdGrove
end Perennial
