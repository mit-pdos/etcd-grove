/-
Lean-first (no Rocq counterpart).

The proof of `(*store).conditionalDelete`. The first read's names are made first (`rwNames_alloc`),
for the closure `getCurrentState` returns; its invariant (D30n), with the caller's token `W`, only
when a read is made (`rwInv_alloc_at`): at once without a cached object, or by `refreshOnError` on a
cached state that failed a check (a cached state may reach `deleteOnce` with `W` unspent). The
invariant hands `W` at the first state with the response's pair where the model's step is the
identity; after it, the caller's result at a state with the response's answer, or `W` back
(`rwInv_after`). The loop's invariant: the state `s` (`stFrom`, at a revision), and either the
cached state with `W` and the names' ghost state, or a read of `s` at `σ` (`rdFacts`) with the
caller's result if `σ` hands, else `W`. A failed precondition or `validateDeletion` is the model's
answer (`delete_item_pre`, `delete_item_val`) at the read's state where the key is at `s`'s revision
(`stFrom_rd_item`: the current state's, or the re-read's when the key did not move; `cd_refresh`);
a missing key is `delete_none`; `deleteOnce` either answers (an error, or the write) or, on a
conflict, gives the next iteration's reading, its update handed there if the step is the identity.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__conditionalDelete
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getStateFromObject
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__deleteOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

set_option hygiene false in
/-- `conditionalDelete`'s loop after a failed check (`Preconditions.Check`'s or `validateDeletion`'s
error `ok ei`; `hmod`, the model's answer on the state's item, `Hε` its shape): `refreshOnError`,
then on a cached state its re-read through the first read's invariant. -/
local macro "cd_refresh" : tactic => `(tactic| (
  ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
  · iunfold ownState
    iexists x, m, dsl
    iframe Hstp Hobj Hdsl Hm
    ipureintro; exact Hstn
  icases (ownState_split c st s) $$ Hos with ⟨%x', Hos, -⟩
  icases Hph with (⟨%Hcur, HW, Hlc, Hc, Htok, Hp⟩ | ⟨%σ, %kv, #Hfs, %Hkv, HT⟩)
  · -- the cached state: the re-read is the first read
    imod (rwInv_alloc_at γc γt γp c key (stepHand c (delStep key (c.S.preOk pr) validate)) W Φu ⊤) $$ [HW Hc] with #Hrw
    · iframe HW Hc
    ihave Hmk := (rwInv_maker γc γt γp c key (delStep key (c.S.preOk pr) validate) (stepHand c (delStep key (c.S.preOk pr) validate))
      (handOk_del c key (c.S.preOk pr) validate) W Φu) $$ [Hp]
    · iframe Hrw Hp Hau
    wp_apply (wp_refresh Obj c st s _ f x' key false (rdQ γc γp c key (stepHand c (delStep key (c.S.preOk pr) validate)))) $$ [Hos Hmk]
      as %st' %err' Hr
    · isimp only [Hcur, Bool.false_eq_true, ↓reduceIte]
      iframe Hos Hf Hmk
    isimp only [Hcur, Bool.false_eq_true, ↓reduceIte] at Hr
    icases Hr with (#Hu | ⟨%σ, %e0, #Hrq, -, Hat, %He'⟩)
    · ihave %Hne := unkErr_ne c err' $$ Hu
      rcases err' with ei' | _
      rotate_left
      · exact absurd rfl Hne
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      ileft
      isplitr
      · iexact Hu
      iexists o0, rv0
      iexact Hout
    ihave #Hrq' := Hrq
    iunfold rdQ at Hrq'
    icases Hrq' with ⟨#Hfs, -, -⟩
    imod (rwInv_after γc γt γp c key (delStep key (c.S.preOk pr) validate) (stepHand c (delStep key (c.S.preOk pr) validate)) (handOk_del c key (c.S.preOk pr) validate) W Φu σ)
      $$ [Htok Hrq Hlc] with HT
    · iframe Hrw Htok Hrq Hlc
    unfold stAt
    rcases hf : mvcc.findKey key σ.kvs with _ | kv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hat with ⟨%Hst0, Herr⟩
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      rw [if_neg (fun h => by cases h.1)] at He'
      subst He'
      have hid := delete_none c σ key hf (c.S.preOk pr) validate
      have hh := hand_true c (delStep key (c.S.preOk pr) validate) σ (by simp [delStep, hid])
      isimp only [hh, ↓reduceIte] at HT
      icases HT with ⟨%σ1, HΦ1, %Hsame⟩
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      iright
      iexists σ1
      iframe HΦ1
      rw [delete_local key _ validate (c.abs σ1) (c.abs σ) Hsame.1 (by rw [abs_rv, abs_rv, Hsame.2]),
        hid]
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    icases Hat with ⟨%Herr, %s0, Hos', %Hs0⟩
    subst Herr
    by_cases hm : kubernetes.modAt key σ = s.rev
    · -- the key did not move: the check's error, the model's answer at the read's state
      rw [if_pos ⟨rfl, hm⟩] at He'
      subst He'
      ihave %Hit := (stFrom_rd_item c key hk s Hsr σ hm) $$ [Hfrom Hfs]
      · iframe Hfrom Hfs
      obtain ⟨b, hb⟩ := Hit
      have hid := hmod (c.abs σ) b hb
      have hh := hand_true c (delStep key (c.S.preOk pr) validate) σ (by simp [delStep, hid])
      isimp only [hh, ↓reduceIte] at HT
      icases HT with ⟨%σ1, HΦ1, %Hsame⟩
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      iright
      iexists σ1
      iframe HΦ1
      rw [delete_local key _ validate (c.abs σ1) (c.abs σ) Hsame.1 (by rw [abs_rv, abs_rv, Hsame.2]),
        hid]
      iapply Hε
      iexact Hout
    · -- the key moved: the next iteration from the read
      rw [if_neg (fun h => hm h.2)] at He'
      subst He'
      ihave Hfr := (stFrom_read c key σ kv s0 hf Hs0) $$ Hfs
      icases Hfr with ⟨#Hfrom', %Hsr'⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists st', s0, e
      iframe origState err Hos' Hout Hfrom'
      isplitr
      · ipureintro; exact Hsr'
      iright
      iexists σ, kv
      iframe Hfs HT
      ipureintro; exact ⟨hf, Hs0⟩
  · -- a read's state: current, the check's error back
    have Hcur : s.current = true := Hkv.2.2.2.2
    wp_apply (wp_refresh Obj c st s _ f x' key false (rdQ γc γp c key (stepHand c (delStep key (c.S.preOk pr) validate)))) $$ [Hos]
      as %st' %err' Hr
    · isimp only [Hcur, ↓reduceIte]
      iframe Hos
    isimp only [Hcur, ↓reduceIte] at Hr
    icases Hr with ⟨%Heq, -⟩
    obtain ⟨rfl, rfl⟩ := Heq
    have hm : kubernetes.modAt key σ = s.rev := by simp [kubernetes.modAt, Hkv.1, Hkv.2.1]
    ihave %Hit := (stFrom_rd_item c key hk s Hsr σ hm) $$ [Hfrom Hfs]
    · iframe Hfrom Hfs
    obtain ⟨b, hb⟩ := Hit
    have hid := hmod (c.abs σ) b hb
    have hh := hand_true c (delStep key (c.S.preOk pr) validate) σ (by simp [delStep, hid])
    isimp only [hh, ↓reduceIte] at HT
    icases HT with ⟨%σ1, HΦ1, %Hsame⟩
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iunfold delOut
    iright
    iexists σ1
    iframe HΦ1
    rw [delete_local key _ validate (c.abs σ1) (c.abs σ) Hsame.1 (by rw [abs_rv, abs_rv, Hsame.2]),
      hid]
    iapply Hε
    iexact Hout))

theorem store.conditionalDelete.wp_proof
    (wp_getCur : store.getCurrentState.spec (GF := GF) (hG := hG))
    (wp_getStateFromObject : store.getStateFromObject.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_deleteOnce : store.deleteOnce.spec (GF := GF) (hG := hG))
    (wp_refresh : refreshOnError.spec (GF := GF) (hG := hG)) :
    store.conditionalDelete.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c ci cd key out o0 rv0 v p pp pr cx ca validate vf W _ Φu hk hkl
  wp_start as ⟨#Hst, #Hctx, #Hce, Hout, %Hv, #Hpre, Hca, HW, #Hau, #Hval⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, #Henc, #Hver, #Htr, #Hdec, #Hzero, #Hmeta⟩
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  -- the first read's names (its invariant, with the caller's token, made at the first read)
  ihave Hnames := rwNames_alloc (GF := GF)
  imod Hnames with ⟨%γc, %γt, %γp, Hc, Htok, Hp⟩
  have hR : ∀ R0 m σ, rdQ (GF := GF) γc γp c key (stepHand c (delStep key (c.S.preOk pr) validate)) R0 m σ ⊢
      ⌜kvWf c σ⌝ := fun R0 m σ => by
    iintro #H
    iunfold rdQ at H
    icases H with ⟨#Hf, -, -⟩
    iunfold rdFacts at Hf
    icases Hf with ⟨%h, -⟩
    ipureintro; exact h.1
  wp_auto_lc 1
  wp_apply (wp_getCur Obj sp c ci cd go!"deleteGet" key v p false
      (rdQ γc γp c key (stepHand c (delStep key (c.S.preOk pr) validate))) hk hkl hR) $$ [] as %f #Hf
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  rcases ca with _ | ⟨o1, r1⟩
  focus
    -- no cached object: the first read, through the invariant
    iunfold cachedOk at Hca
    icases Hca with %Hcx
    subst Hcx
    (try wp_auto)
    imod (rwInv_alloc_at γc γt γp c key (stepHand c (delStep key (c.S.preOk pr) validate)) W Φu ⊤) $$ [HW Hc] with #Hrw
    · iframe HW Hc
    ihave Hmk := (rwInv_maker γc γt γp c key (delStep key (c.S.preOk pr) validate) (stepHand c (delStep key (c.S.preOk pr) validate))
      (handOk_del c key (c.S.preOk pr) validate) W Φu) $$ [Hp]
    · iframe Hrw Hp Hau
    ihave #Hf' := Hf
    iunfold getStateOk at Hf'
    wp_apply Hf' $$ [Hmk] as %st %err Hr
    · iexact Hmk
    icases Hr with (#Herr | ⟨%σ, #Hrq, -, Hat⟩)
    · ihave %Hne := unkErr_ne c err $$ Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        iunfold delOut
        ileft
        isplitr
        · iexact Herr
        iexists o0, rv0
        iexact Hout
    ihave #Hrq' := Hrq
    iunfold rdQ at Hrq'
    icases Hrq' with ⟨#Hfs, -, -⟩
    imod (rwInv_after γc γt γp c key (delStep key (c.S.preOk pr) validate) (stepHand c (delStep key (c.S.preOk pr) validate)) (handOk_del c key (c.S.preOk pr) validate) W Φu σ)
      $$ [Htok Hrq Hlc1] with HT
    · iframe Hrw Htok Hrq Hlc1
    unfold stAt
    rcases hf : mvcc.findKey key σ.kvs with _ | kv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hat with ⟨%Hst0, Herr⟩
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      have hid := delete_none c σ key hf (c.S.preOk pr) validate
      have hh := hand_true c (delStep key (c.S.preOk pr) validate) σ (by simp [delStep, hid])
      isimp only [hh, ↓reduceIte] at HT
      icases HT with ⟨%σ1, HΦ1, %Hsame⟩
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      iright
      iexists σ1
      iframe HΦ1
      rw [delete_local key _ validate (c.abs σ1) (c.abs σ) Hsame.1 (by rw [abs_rv, abs_rv, Hsame.2]),
        hid]
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    icases Hat with ⟨%Herr, %s0, Hos, %Hs0⟩
    subst Herr
    (try wp_auto)
    ihave Hfr := (stFrom_read c key σ kv s0 hf Hs0) $$ Hfs
    icases Hfr with ⟨#Hfrom, %Hsr⟩
    ihave HI : (∃ (st : Loc) (s : OState Obj) (e : GoInterface),
            "origState" ∷ origState_ptr ↦ st ∗ "err" ∷ err_ptr ↦ e ∗ "Hos" ∷ ownState c st s ∗
            "Hout" ∷ c.S.objAt out o0 rv0 ∗ "#Hfrom" ∷ stFrom c key s ∗ "%Hsr" ∷ ⌜s.rev ≠ W64 0⌝ ∗
            "Hph" ∷ ((⌜s.current = false⌝ ∗ W ∗ £ 1 ∗
                dghostVar γc (DFrac.own 1) (none : Option KVState) ∗ dghostVar γt (DFrac.own 1) () ∗
                dghostVar γp (DFrac.own 1) (none : Option (w64 × w64))) ∨
              (∃ (σ : KVState) (kv : EtcdKv), rdFacts c σ ∗
                ⌜mvcc.findKey key σ.kvs = some kv ∧ stOfKv c kv s⌝ ∗
                (if stepHand c (delStep key (c.S.preOk pr) validate) σ then iprop(∃ σ1, Φu σ1 ∗
                  ⌜(c.abs σ1).items key = (c.abs σ).items key ∧ σ1.rev = σ.rev⌝) else W))) : IProp GF) $$ [origState err Hos HT Hout]
    · iexists st, s0, GoInterface.nil
      iframe origState err Hos Hout Hfrom
      isplitr
      · ipureintro; exact Hsr
      iright
      iexists σ, kv
      iframe Hfs HT
      ipureintro; exact ⟨hf, Hs0⟩
    iclear Hfs Hrq Hfrom Hrw Hf'
    clear hf Hs0 Hsr σ kv s0 st
  rotate_left
  focus
    -- the cached object: its state, the token kept
    iunfold cachedOk at Hca
    icases Hca with ⟨%Hr1, Hcobj, #Hver1⟩
    ihave %Hcn := c.S.objAt_ne_nil cx o1 _ $$ Hcobj
    rcases cx with ci1 | _
    rotate_left
    · exact absurd rfl Hcn
    (try wp_auto)
    wp_apply (wp_getStateFromObject Obj sp c (GoInterface.ok ci1) o1 r1) $$ [Hcobj] as %st %err Hgs
    · iframe #
      iexact Hcobj
    icases Hgs with (⟨%He, Hos⟩ | #Herr)
    rotate_left
    · ihave %Hne := unkErr_ne c err $$ Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        iunfold delOut
        ileft
        isplitr
        · iexact Herr
        iexists o0, rv0
        iexact Hout
    subst He
    (try wp_auto)
    ihave HI : (∃ (st : Loc) (s : OState Obj) (e : GoInterface),
            "origState" ∷ origState_ptr ↦ st ∗ "err" ∷ err_ptr ↦ e ∗ "Hos" ∷ ownState c st s ∗
            "Hout" ∷ c.S.objAt out o0 rv0 ∗ "#Hfrom" ∷ stFrom c key s ∗ "%Hsr" ∷ ⌜s.rev ≠ W64 0⌝ ∗
            "Hph" ∷ ((⌜s.current = false⌝ ∗ W ∗ £ 1 ∗
                dghostVar γc (DFrac.own 1) (none : Option KVState) ∗ dghostVar γt (DFrac.own 1) () ∗
                dghostVar γp (DFrac.own 1) (none : Option (w64 × w64))) ∨
              (∃ (σ : KVState) (kv : EtcdKv), rdFacts c σ ∗
                ⌜mvcc.findKey key σ.kvs = some kv ∧ stOfKv c kv s⌝ ∗
                (if stepHand c (delStep key (c.S.preOk pr) validate) σ then iprop(∃ σ1, Φu σ1 ∗
                  ⌜(c.abs σ1).items key = (c.abs σ).items key ∧ σ1.rev = σ.rev⌝) else W))) : IProp GF) $$ [origState err Hos HW Hlc1 Hc Htok Hp Hout]
    · iexists st, ⟨o1, r1, c.S.encode o1, false, false⟩, GoInterface.nil
      iframe origState err Hos Hout
      isplitr
      · unfold stFrom
        iright
        iright
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, Hr1⟩
        iexact Hver1
      isplitr
      · ipureintro; exact Hr1
      ileft
      iframe HW Hlc1 Hc Htok Hp
      ipureintro; rfl
    iclear Hver1
    clear Hr1 Hcn st
  all_goals
    wp_for HI
    iunfold ownState at Hos
    icases Hos with ⟨%x, %m, %dsl, %Hstn, Hstp, Hobj, #Hdsl, Hm⟩
    ihave %Hpn : ⌜pp = null → (c.S.preOk pr) s.o (uint.nat s.rev) = true⌝ $$ []
    · ihave #Hpre' := Hpre
      iunfold preAt at Hpre'
      icases Hpre' with (%H | ⟨%lu, %lr, #Hpp, -⟩)
      · ipureintro
        intro _
        rw [H.2]
        rfl
      · ihave %hnn := typedPointsto_not_null _ _ _ $$ Hpp
        ipureintro
        intro h
        exact absurd h hnn
    (try wp_auto)
    wp_if_destruct
    · have hpre := Hpn rfl
      (try wp_auto)
      iunfold validateOk at Hval
      wp_apply Hval $$ [$Hobj] as %verr Hobj %Hvres
      (try wp_auto)
      rcases hvd : validate s.o (uint.nat s.rev) with _ | ue
      · rw [hvd] at Hvres
        subst Hvres
        (try wp_auto)
        ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
        · iunfold ownState
          iexists x, m, dsl
          iframe Hstp Hobj Hdsl Hm
          ipureintro; exact Hstn
        ihave HW : W $$ [Hph]
        · icases Hph with (⟨-, HW, -⟩ | ⟨%σ, %kv, #Hfs, %Hkv, HT⟩)
          · iexact HW
          · have hh := del_read_hand c σ key hk kv Hkv.1 s Hkv.2 (c.S.preOk pr) validate hpre hvd
            isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
            iexact HT
        wp_apply (wp_deleteOnce Obj E sp c ci cd key out o0 rv0 st s v p (c.S.preOk pr) validate W Φu hk hkl
            Hsr hpre hvd) $$ [Hos Hout HW] as %st' %ok %derr Hd
        · iframe #
          iframe Hos Hout HW
          ipureintro; exact Hv
        icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, Hout, %σ', #Hfs', Hat, HT'⟩)
        · -- an error
          ihave %Hne := unkErr_ne c derr $$ Hde
          rcases derr with ei | _
          rotate_left
          · exact absurd rfl Hne
          (try wp_auto)
          wp_for_post
          (try wp_auto)
          iapply HΦ
          iunfold delOut
          ileft
          iframe Hout
          iexact Hde
        · -- deleted
          obtain ⟨rfl, rfl⟩ := Hok
          (try wp_auto)
          wp_for_post
          (try wp_auto)
          iapply HΦ
          iunfold delOut
          iright
          iexists σ'
          iframe HΦu Hresp
        · -- a conflict
          subst Hok
          unfold stAt
          rcases hf : mvcc.findKey key σ'.kvs with _ | kv'
          · simp only [Bool.false_eq_true, ↓reduceIte]
            icases Hat with ⟨%Hst0, Herr⟩
            iunfold storageErrIs at Herr
            icases Herr with ⟨%ep, %Hep, #Hep⟩
            subst Hep
            have hid := delete_none c σ' key hf (c.S.preOk pr) validate
            have hh := hand_true c (delStep key (c.S.preOk pr) validate) σ' (by simp [delStep, hid])
            isimp only [hh, ↓reduceIte] at HT'
            (try wp_auto)
            wp_for_post
            (try wp_auto)
            iapply HΦ
            iunfold delOut
            iright
            iexists σ'
            iframe HT'
            rw [hid]
            simp only [respIs, storageErrIs]
            isplitl []
            · iexists ep
              iframe Hep
              ipureintro; rfl
            iexists o0, rv0
            iexact Hout
          icases Hat with ⟨%Herr, %s', Hos', %Hs'⟩
          subst Herr
          ihave Hfr := (stFrom_read c key σ' kv' s' hf Hs') $$ Hfs'
          icases Hfr with ⟨#Hfrom', %Hsr'⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists st', s', GoInterface.nil
          iframe origState err Hos' Hout Hfrom'
          isplitr
          · ipureintro; exact Hsr'
          iright
          iexists σ', kv'
          iframe Hfs'
          isplitr
          · ipureintro; exact ⟨hf, Hs'⟩
          cases hh : (stepHand c (delStep key (c.S.preOk pr) validate)) σ'
          · isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT'
            simp only [Bool.false_eq_true, ↓reduceIte]
            iexact HT'
          · isimp only [hh, ↓reduceIte] at HT'
            simp only [↓reduceIte]
            iexists σ'
            iframe HT'
            ipureintro; exact ⟨rfl, rfl⟩
      · rw [hvd] at Hvres
        rcases verr with ei | _
        rotate_left
        · exact absurd rfl Hvres.1
        have hmod := fun (st0 : KSt Obj) (b : Bool) h =>
          delete_item_val st0 key s.o (uint.nat s.rev) b h (c.S.preOk pr) validate hpre ue hvd
        ihave #Hε : □ (∀ o rv, c.S.objAt out o rv -∗
            respIs c (KResp.err (KErr.user ue) : KResp Obj E) (GoInterface.ok ei) out) $$ []
        · imodintro
          iintro %o %rv Ho
          simp only [respIs]
          isplitr
          · ipureintro; exact Hvres
          iexists o, rv
          iexact Ho
        (try wp_auto)
        cd_refresh
    · -- `Preconditions.Check` on the state's object
      ihave #Hmeta' := Hmeta
      iunfold metaOk at Hmeta'
      wp_apply (wp_Check pp pr key x (c.S.objAt x s.o (c.S.fmtRV s.rev)) (c.S.uid s.o)
          (c.S.fmtRV s.rev)) $$ [Hobj]
      · iframe # Hobj
        iapply Hmeta'
      iintro %e1 ⟨Hobj, Hck⟩
      cases hpok : pr.ok (c.S.uid s.o) (c.S.fmtRV s.rev)
      · isimp only [hpok, Bool.false_eq_true, ↓reduceIte] at Hck
        ihave #Hck0 := Hck
        ihave #Hck' := Hck0
        iunfold invalidErrIs at Hck'
        icases Hck' with ⟨%l, %e2, %Hl, -⟩
        subst Hl
        have hpf : (c.S.preOk pr) s.o (uint.nat s.rev) = false := by
          unfold ObjCodec.preOk; rw [W64_uint_nat]; exact hpok
        have hmod := fun (st0 : KSt Obj) (b : Bool) h =>
          delete_item_pre st0 key s.o (uint.nat s.rev) b h (c.S.preOk pr) validate hpf
        ihave #Hε : □ (∀ o rv, c.S.objAt out o rv -∗
            respIs c (KResp.err (KErr.invalidObj key) : KResp Obj E)
              (interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #l) out) $$ []
        · imodintro
          iintro %o %rv Ho
          simp only [respIs]
          iframe Hck0
          iexists o, rv
          iexact Ho
        (try wp_auto)
        cd_refresh
      · isimp only [hpok, ↓reduceIte] at Hck
        icases Hck with %He1
        subst He1
        have hpre : (c.S.preOk pr) s.o (uint.nat s.rev) = true := by
          unfold ObjCodec.preOk; rw [W64_uint_nat]; exact hpok
        (try wp_auto)
        iunfold validateOk at Hval
        wp_apply Hval $$ [$Hobj] as %verr Hobj %Hvres
        (try wp_auto)
        rcases hvd : validate s.o (uint.nat s.rev) with _ | ue
        · rw [hvd] at Hvres
          subst Hvres
          (try wp_auto)
          ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
          · iunfold ownState
            iexists x, m, dsl
            iframe Hstp Hobj Hdsl Hm
            ipureintro; exact Hstn
          ihave HW : W $$ [Hph]
          · icases Hph with (⟨-, HW, -⟩ | ⟨%σ, %kv, #Hfs, %Hkv, HT⟩)
            · iexact HW
            · have hh := del_read_hand c σ key hk kv Hkv.1 s Hkv.2 (c.S.preOk pr) validate hpre hvd
              isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
              iexact HT
          wp_apply (wp_deleteOnce Obj E sp c ci cd key out o0 rv0 st s v p (c.S.preOk pr) validate W Φu hk hkl
              Hsr hpre hvd) $$ [Hos Hout HW] as %st' %ok %derr Hd
          · iframe #
            iframe Hos Hout HW
            ipureintro; exact Hv
          icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, Hout, %σ', #Hfs', Hat, HT'⟩)
          · -- an error
            ihave %Hne := unkErr_ne c derr $$ Hde
            rcases derr with ei | _
            rotate_left
            · exact absurd rfl Hne
            (try wp_auto)
            wp_for_post
            (try wp_auto)
            iapply HΦ
            iunfold delOut
            ileft
            iframe Hout
            iexact Hde
          · -- deleted
            obtain ⟨rfl, rfl⟩ := Hok
            (try wp_auto)
            wp_for_post
            (try wp_auto)
            iapply HΦ
            iunfold delOut
            iright
            iexists σ'
            iframe HΦu Hresp
          · -- a conflict
            subst Hok
            unfold stAt
            rcases hf : mvcc.findKey key σ'.kvs with _ | kv'
            · simp only [Bool.false_eq_true, ↓reduceIte]
              icases Hat with ⟨%Hst0, Herr⟩
              iunfold storageErrIs at Herr
              icases Herr with ⟨%ep, %Hep, #Hep⟩
              subst Hep
              have hid := delete_none c σ' key hf (c.S.preOk pr) validate
              have hh := hand_true c (delStep key (c.S.preOk pr) validate) σ' (by simp [delStep, hid])
              isimp only [hh, ↓reduceIte] at HT'
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              iapply HΦ
              iunfold delOut
              iright
              iexists σ'
              iframe HT'
              rw [hid]
              simp only [respIs, storageErrIs]
              isplitl []
              · iexists ep
                iframe Hep
                ipureintro; rfl
              iexists o0, rv0
              iexact Hout
            icases Hat with ⟨%Herr, %s', Hos', %Hs'⟩
            subst Herr
            ihave Hfr := (stFrom_read c key σ' kv' s' hf Hs') $$ Hfs'
            icases Hfr with ⟨#Hfrom', %Hsr'⟩
            (try wp_auto)
            wp_for_post
            iframe
            iexists st', s', GoInterface.nil
            iframe origState err Hos' Hout Hfrom'
            isplitr
            · ipureintro; exact Hsr'
            iright
            iexists σ', kv'
            iframe Hfs'
            isplitr
            · ipureintro; exact ⟨hf, Hs'⟩
            cases hh : (stepHand c (delStep key (c.S.preOk pr) validate)) σ'
            · isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT'
              simp only [Bool.false_eq_true, ↓reduceIte]
              iexact HT'
            · isimp only [hh, ↓reduceIte] at HT'
              simp only [↓reduceIte]
              iexists σ'
              iframe HT'
              ipureintro; exact ⟨rfl, rfl⟩
        · rw [hvd] at Hvres
          rcases verr with ei | _
          rotate_left
          · exact absurd rfl Hvres.1
          have hmod := fun (st0 : KSt Obj) (b : Bool) h =>
            delete_item_val st0 key s.o (uint.nat s.rev) b h (c.S.preOk pr) validate hpre ue hvd
          ihave #Hε : □ (∀ o rv, c.S.objAt out o rv -∗
              respIs c (KResp.err (KErr.user ue) : KResp Obj E) (GoInterface.ok ei) out) $$ []
          · imodintro
            iintro %o %rv Ho
            simp only [respIs]
            isplitr
            · ipureintro; exact Hvres
            iexists o, rv
            iexact Ho
          (try wp_auto)
          cd_refresh

end proof

end k8s
end EtcdGrove
end Perennial
