/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedProcessor__distribute.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__distribute
public import Spec.k8s_io.client_go.tools.cache.processorListener__add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem sharedProcessor.distribute.wp_proof
    (wp_add : processorListener.add.spec (GF := GF) (hG := hG)) :
    sharedProcessor.distribute.spec (GF := GF) (hG := hG) := by
  intro p γp QP E e snc Hbound
  wp_start as ⟨#Hp, Hrd, Hsend, #HQ⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isProc at Hp
  icases Hp with ⟨%c, #Hc, #Hcond⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold procReader at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  iunfold procP at HP
  icases HP with ⟨%st, %ml, %M, Hst, Hl, Hm, Hk, %Hall⟩
  (try wp_auto)
  -- wait until the listeners are started (or there are none)
  ihave HI : (∃ (st : Bool) (ml : Loc) (M : GMap Loc Bool),
      "Hrl" ∷ sync.ownRWMutexRLocked (structFieldRef sharedProcessor go!"listenersLock" p)
        (procP p γp) ∗
      "Hst" ∷ structFieldRef sharedProcessor go!"listenersStarted" p ↦{DFrac.own sync.rfrac} st ∗
      "Hl" ∷ structFieldRef sharedProcessor go!"listeners" p ↦{DFrac.own sync.rfrac} ml ∗
      "Hm" ∷ ml ↦${DFrac.own sync.rfrac} M ∗
      "Hk" ∷ ghostVar γp.keys sync.rfrac.half (keysOf M) ∗
      "%Hall" ∷ ⌜∀ l b, M !! l = some b → b = true⌝ ∗ "p" ∷ p_ptr ↦ p : IProp GF)
    $$ [Hrl Hst Hl Hm Hk p]
  · iexists st, ml, M; iframe; ipureintro; exact Hall
  wp_for HI
  by_cases hgo : st = false ∧ GMap.size M ≠ 0
  · obtain ⟨rfl, hz⟩ := hgo
    wp_auto
    wp_apply (wp_map_len_lt ml M) $$ [$Hm] as ⟨Hm, %Hsz⟩
    have hpos : sint.Z (W64 0) < sint.Z (W64 (GMap.size M)) := by word
    simp only [hpos, _root_.decide_true]
    cleanup_bool_decide
    wp_auto
    -- wait on the condition variable (the read lock released meanwhile)
    ihave #Hlw := sync.rlocker_isLockerWith (structFieldRef sharedProcessor go!"listenersLock" p)
      (procP p γp) $$ Hsync
    wp_apply (sync.Cond.wp_Wait_with c
        (sync.rlockerOf (structFieldRef sharedProcessor go!"listenersLock" p))
        (sync.ownRWMutex (structFieldRef sharedProcessor go!"listenersLock" p) (procP p γp))
        iprop(sync.ownRWMutexRLocked (structFieldRef sharedProcessor go!"listenersLock" p)
          (procP p γp) ∗ ▷ procP p γp sync.rfrac))
      $$ [$Hcond $Hlw Hrl Hst Hl Hm Hk] as ⟨Hrl, HP⟩
    · iframe
      inext; iunfold procP; iexists false, ml, M; iframe; ipureintro; exact Hall
    iunfold procP at HP
    icases HP with ⟨%st', %ml', %M', Hst, Hl, Hm, Hk, %Hall'⟩
    wp_for_post
    iframe
    iexists st', ml', M'
    iframe
    ipureintro; exact Hall'
  · -- the loop's exit, once started or with no listener
    have hex : st = true ∨ (st = false ∧ GMap.size M = 0) := by
      cases st <;> simp_all
    rcases hex with rfl | ⟨rfl, hz⟩
    · wp_auto
      cleanup_bool_decide
      wp_auto
      -- the sender's listeners are the map's
      iunfold procSend at Hsend
      icases Hsend with ⟨%Ls, Hks, HLs⟩
      icombine Hk Hks gives %hkk
      have hkeys := hkk.2
      have hdom : ∀ l, (M !! l).isSome ↔ (Ls !! l).isSome := by
        intro l
        have := congrArg (· !! l) hkeys
        simp only [keysOf, GMap.lookup_fmap] at this
        cases h1 : M !! l <;> cases h2 : Ls !! l <;> simp_all
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (x : Loc) (y : Bool),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗
          "listener" ∷ listener_ptr ↦ x ∗ "isSyncing" ∷ isSyncing_ptr ↦ y ∗
          "obj" ∷ obj_ptr ↦ notifOf e ∗ "sync" ∷ sync_ptr ↦ snc ∗
          "HLs" ∷ [∗map] l ↦ γl ∈ Ls, isListener l γl QP ∗ spscProducer (V := GoInterface) γl.add
            ((if l ∈ keys.take i.toNat then E ++ [e] else E).map notifOf))) $$ Hm
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [listener isSyncing obj sync HLs]
      · iexists _, _
        simp only [named, Int.toNat_zero, List.take_zero, List.not_mem_nil, ↓reduceIte]
        iframe
        ipureintro; exact Int.le_refl _
      isplitr
      · imodintro
        iintro %i %l %b ⟨%Hkey, %Hb⟩ HP
        iNamed HP
        have hb : b = true := Hall l b Hb
        subst hb
        obtain ⟨γl, hγl⟩ : ∃ γl, Ls !! l = some γl :=
          Option.isSome_iff_exists.1 ((hdom l).1 (by rw [Hb]; rfl))
        have hnd : l ∉ keys.take i.toNat := by
          intro hm
          have hd : l ∈ keys.drop i.toNat := by
            rw [List.mem_iff_getElem?]
            exact ⟨0, by rw [List.getElem?_drop]; simpa using Hkey⟩
          have hnod := List.nodup_append.1 ((List.take_append_drop i.toNat keys).symm ▸ Hknodup)
          exact hnod.2.2 l hm l hd rfl
        have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [l] := by
          rw [show (i + 1).toNat = i.toNat + 1 by omega]
          rw [List.take_add_one, Hkey]; rfl
        icases (BigSepM.bigSepM_delete hγl).1 $$ HLs with ⟨⟨#Hli, Hprod⟩, HLs⟩
        simp only [hnd, ↓reduceIte]
        ihave HQ' : QP (E.map notifOf).length e $$ []
        · rw [List.length_map]; iexact HQ
        wp_auto
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
            spscProducer (V := GoInterface) γl.add ((E ++ [e]).map notifOf) ∗
            obj_ptr ↦ notifOf e ∗ sync_ptr ↦ snc ∗ listener_ptr ↦ l ∗ isSyncing_ptr ↦ true)))
          $$ [Hprod HQ' obj sync listener isSyncing]
        · cases snc
          · wp_auto
            wp_apply (wp_add l γl QP (E.map notifOf) e Hbound) $$ [$Hpkg $Hli $Hprod $HQ'] as Hprod
            iframe
            simp only [List.map_append, List.map_cons, List.map_nil]
            iframe
          · wp_auto
            wp_apply (wp_add l γl QP (E.map notifOf) e Hbound) $$ [$Hpkg $Hli $Hprod $HQ'] as Hprod
            iframe
            simp only [List.map_append, List.map_cons, List.map_nil]
            iframe
        iintro %v ⟨%hv, Hprod, obj, sync, listener, isSyncing⟩
        subst hv
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists l, true
        simp only [named]
        iframe
        isplitr
        · ipureintro; omega
        iapply (BigSepM.bigSepM_delete hγl).2
        rw [Htake]
        simp only [List.mem_append, List.mem_singleton, _root_.or_true, ↓reduceIte]
        iframe
        iframe #
        iapply (BigSepM.bigSepM_mono (fun {l' γ'} hl' => ?_)) $$ HLs
        have hne : l' ≠ l := by
          intro h
          have h2 : (GMap.delete l Ls) !! l' = some γ' := hl'
          rw [h, GMap.lookup_delete] at h2; cases h2
        simp only [hne, _root_.or_false]
        exact .rfl
      · iintro HP Hm
        iNamed HP
        have hall : keys.take (GMap.size M : Int).toNat = keys := by
          rw [Int.toNat_natCast, ← Hklen, List.take_length]
        rw [hall]
        wp_auto
        wp_apply sync.RWMutex.wp_RUnlock $$ [$Hsync $Hrl Hst Hl Hm Hk] as Hrd
        · iunfold procP; iexists _, ml, M; iframe; ipureintro; exact Hall
        (try wp_auto)
        iapply HΦ
        iunfold procReader
        iframe
        iunfold procSend
        iexists Ls
        iframe
        iapply (BigSepM.bigSepM_mono (fun {l γl} hl => ?_)) $$ HLs
        have : l ∈ keys := (Hkset l).2 ((hdom l).2 (by rw [show Ls !! l = some γl from hl]; rfl))
        simp only [this, ↓reduceIte]
        exact .rfl
    · wp_auto
      wp_apply (wp_map_len_lt ml M) $$ [$Hm] as ⟨Hm, %Hsz⟩
      have h0 : W64 (GMap.size M) = W64 0 := by rw [hz]; rfl
      rw [h0]
      cleanup_bool_decide
      try simp only [Int.lt_irrefl, decide_false]
      try simp only [Bool.false_eq_true, ↓reduceIte]
      try simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      -- the sender's listeners are the map's
      iunfold procSend at Hsend
      icases Hsend with ⟨%Ls, Hks, HLs⟩
      icombine Hk Hks gives %hkk
      have hkeys := hkk.2
      have hdom : ∀ l, (M !! l).isSome ↔ (Ls !! l).isSome := by
        intro l
        have := congrArg (· !! l) hkeys
        simp only [keysOf, GMap.lookup_fmap] at this
        cases h1 : M !! l <;> cases h2 : Ls !! l <;> simp_all
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (x : Loc) (y : Bool),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗
          "listener" ∷ listener_ptr ↦ x ∗ "isSyncing" ∷ isSyncing_ptr ↦ y ∗
          "obj" ∷ obj_ptr ↦ notifOf e ∗ "sync" ∷ sync_ptr ↦ snc ∗
          "HLs" ∷ [∗map] l ↦ γl ∈ Ls, isListener l γl QP ∗ spscProducer (V := GoInterface) γl.add
            ((if l ∈ keys.take i.toNat then E ++ [e] else E).map notifOf))) $$ Hm
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [listener isSyncing obj sync HLs]
      · iexists _, _
        simp only [named, Int.toNat_zero, List.take_zero, List.not_mem_nil, ↓reduceIte]
        iframe
        ipureintro; exact Int.le_refl _
      isplitr
      · imodintro
        iintro %i %l %b ⟨%Hkey, %Hb⟩ HP
        iNamed HP
        have hb : b = true := Hall l b Hb
        subst hb
        obtain ⟨γl, hγl⟩ : ∃ γl, Ls !! l = some γl :=
          Option.isSome_iff_exists.1 ((hdom l).1 (by rw [Hb]; rfl))
        have hnd : l ∉ keys.take i.toNat := by
          intro hm
          have hd : l ∈ keys.drop i.toNat := by
            rw [List.mem_iff_getElem?]
            exact ⟨0, by rw [List.getElem?_drop]; simpa using Hkey⟩
          have hnod := List.nodup_append.1 ((List.take_append_drop i.toNat keys).symm ▸ Hknodup)
          exact hnod.2.2 l hm l hd rfl
        have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [l] := by
          rw [show (i + 1).toNat = i.toNat + 1 by omega]
          rw [List.take_add_one, Hkey]; rfl
        icases (BigSepM.bigSepM_delete hγl).1 $$ HLs with ⟨⟨#Hli, Hprod⟩, HLs⟩
        simp only [hnd, ↓reduceIte]
        ihave HQ' : QP (E.map notifOf).length e $$ []
        · rw [List.length_map]; iexact HQ
        wp_auto
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
            spscProducer (V := GoInterface) γl.add ((E ++ [e]).map notifOf) ∗
            obj_ptr ↦ notifOf e ∗ sync_ptr ↦ snc ∗ listener_ptr ↦ l ∗ isSyncing_ptr ↦ true)))
          $$ [Hprod HQ' obj sync listener isSyncing]
        · cases snc
          · wp_auto
            wp_apply (wp_add l γl QP (E.map notifOf) e Hbound) $$ [$Hpkg $Hli $Hprod $HQ'] as Hprod
            iframe
            simp only [List.map_append, List.map_cons, List.map_nil]
            iframe
          · wp_auto
            wp_apply (wp_add l γl QP (E.map notifOf) e Hbound) $$ [$Hpkg $Hli $Hprod $HQ'] as Hprod
            iframe
            simp only [List.map_append, List.map_cons, List.map_nil]
            iframe
        iintro %v ⟨%hv, Hprod, obj, sync, listener, isSyncing⟩
        subst hv
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists l, true
        simp only [named]
        iframe
        isplitr
        · ipureintro; omega
        iapply (BigSepM.bigSepM_delete hγl).2
        rw [Htake]
        simp only [List.mem_append, List.mem_singleton, _root_.or_true, ↓reduceIte]
        iframe
        iframe #
        iapply (BigSepM.bigSepM_mono (fun {l' γ'} hl' => ?_)) $$ HLs
        have hne : l' ≠ l := by
          intro h
          have h2 : (GMap.delete l Ls) !! l' = some γ' := hl'
          rw [h, GMap.lookup_delete] at h2; cases h2
        simp only [hne, _root_.or_false]
        exact .rfl
      · iintro HP Hm
        iNamed HP
        have hall : keys.take (GMap.size M : Int).toNat = keys := by
          rw [Int.toNat_natCast, ← Hklen, List.take_length]
        rw [hall]
        wp_auto
        wp_apply sync.RWMutex.wp_RUnlock $$ [$Hsync $Hrl Hst Hl Hm Hk] as Hrd
        · iunfold procP; iexists _, ml, M; iframe; ipureintro; exact Hall
        (try wp_auto)
        iapply HΦ
        iunfold procReader
        iframe
        iunfold procSend
        iexists Ls
        iframe
        iapply (BigSepM.bigSepM_mono (fun {l γl} hl => ?_)) $$ HLs
        have : l ∈ keys := (Hkset l).2 ((hdom l).2 (by rw [show Ls !! l = some γl from hl]; rfl))
        simp only [this, ↓reduceIte]
        exact .rfl

end proof

end cache
end EtcdGrove
end Perennial
