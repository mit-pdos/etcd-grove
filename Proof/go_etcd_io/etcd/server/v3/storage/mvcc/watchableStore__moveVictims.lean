/-
Proof of `Spec/.../mvcc/watchableStore__moveVictims.lean`. Lean-first (no Rocq counterpart).

The mover takes the victims out under the lock (`body_take`: their watchers out, `Wo`, the mover
holding `outW` of each), resends each batch outside the lock, puts each watcher whose batch was
sent back under the lock (`body_readd`), and makes the failed ones victims again, in one batch
(`body_append`); see `MoveVictimsLemmas.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__moveVictims
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcher__send
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.MoveVictimsLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc

theorem mv_take_succ {α : Type} (keys : List α) (i : Nat) (key : α) (h : keys[i]? = some key) :
    keys.take (i + 1) = keys.take i ++ [key] := by
  rw [List.take_add_one, h]; rfl

/-- The send loop's pure state, one key further: `key` failed (now in `NV'` as `x`). -/
theorem mv_send_inv_fail (PB : GMap Loc (Loc × EventBatch)) (NV NV' : GMap Loc NvEnt)
    (keys : List Loc) (i : Nat) (key : Loc) (PR PS : GMap Loc (Loc × EventBatch))
    (x : NvEnt) (hkey : keys[i]? = some key) (hnot : key ∉ keys.take i)
    (hp : PB !! key = some (x.eb, x.B))
    (HPR : ∀ k, PR !! k = if k ∈ keys.take i then none else PB !! k)
    (HPSo : ∀ k, k ∉ keys.take i → PS !! k = none ∧ NV' !! k = NV !! k)
    (HPSi : ∀ k, k ∈ keys.take i → (PS !! k = PB !! k ∧ NV' !! k = none) ∨
      (PS !! k = none ∧ ∃ x, NV' !! k = some x ∧ PB !! k = some (x.eb, x.B))) :
    (∀ k, GMap.delete key PR !! k = if k ∈ keys.take (i + 1) then none else PB !! k) ∧
    (∀ k, k ∉ keys.take (i + 1) → PS !! k = none ∧ (<[key := x]> NV') !! k = NV !! k) ∧
    (∀ k, k ∈ keys.take (i + 1) → (PS !! k = PB !! k ∧ (<[key := x]> NV') !! k = none) ∨
      (PS !! k = none ∧ ∃ y, (<[key := x]> NV') !! k = some y ∧ PB !! k = some (y.eb, y.B))) := by
  rw [mv_take_succ keys i key hkey]
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · by_cases hk : k = key
    · subst hk; rw [GMap.lookup_delete]; simp
    · rw [GMap.lookup_delete_ne _ (Ne.symm hk), HPR]; simp [hk]
  · have hk' : k ≠ key := by intro e; subst e; simp at hk
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')]
    exact HPSo k (fun h => hk (List.mem_append_left _ h))
  · by_cases hk' : k = key
    · subst hk'
      right
      exact ⟨(HPSo k hnot).1, x, GMap.lookup_insert _ _ _, hp⟩
    · have hk'' : k ∈ keys.take i := (List.mem_append.1 hk).resolve_right (by simpa using hk')
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')]
      exact HPSi k hk''

/-- The send loop's pure state, one key further: `key`'s batch sent (now in `PS`). -/
theorem mv_send_inv_ok (PB : GMap Loc (Loc × EventBatch)) (NV NV' : GMap Loc NvEnt)
    (keys : List Loc) (i : Nat) (key : Loc) (PR PS : GMap Loc (Loc × EventBatch))
    (p : Loc × EventBatch) (hkey : keys[i]? = some key) (hnot : key ∉ keys.take i)
    (hp : PB !! key = some p) (hnv : NV !! key = none)
    (HPR : ∀ k, PR !! k = if k ∈ keys.take i then none else PB !! k)
    (HPSo : ∀ k, k ∉ keys.take i → PS !! k = none ∧ NV' !! k = NV !! k)
    (HPSi : ∀ k, k ∈ keys.take i → (PS !! k = PB !! k ∧ NV' !! k = none) ∨
      (PS !! k = none ∧ ∃ x, NV' !! k = some x ∧ PB !! k = some (x.eb, x.B))) :
    (∀ k, GMap.delete key PR !! k = if k ∈ keys.take (i + 1) then none else PB !! k) ∧
    (∀ k, k ∉ keys.take (i + 1) → (<[key := p]> PS) !! k = none ∧ NV' !! k = NV !! k) ∧
    (∀ k, k ∈ keys.take (i + 1) → ((<[key := p]> PS) !! k = PB !! k ∧ NV' !! k = none) ∨
      ((<[key := p]> PS) !! k = none ∧ ∃ y, NV' !! k = some y ∧ PB !! k = some (y.eb, y.B))) := by
  rw [mv_take_succ keys i key hkey]
  refine ⟨fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · by_cases hk : k = key
    · subst hk; rw [GMap.lookup_delete]; simp
    · rw [GMap.lookup_delete_ne _ (Ne.symm hk), HPR]; simp [hk]
  · have hk' : k ≠ key := by intro e; subst e; simp at hk
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')]
    exact HPSo k (fun h => hk (List.mem_append_left _ h))
  · by_cases hk' : k = key
    · subst hk'
      left
      exact ⟨by rw [GMap.lookup_insert, hp], by rw [(HPSo k hnot).2, hnv]⟩
    · have hk'' : k ∈ keys.take i := (List.mem_append.1 hk).resolve_right (by simpa using hk')
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk')]
      exact HPSi k hk''

end mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.moveVictims.wp_proof
    (hSend : mvcc.watcher.send.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherGroup.add.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.moveVictims.spec (GF := GF) (hG := hG) := by
  have hAdd := mvcc.watcherGroup.add.spec_group hAdd
  intro s st γ
  wp_start as ⟨#Hws, HR⟩
  ihave #HwsAll : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%gS, #HgS, #HgSS⟩, ⟨%gP, #HgP, #HgPS⟩, -⟩
  iunfold gaugeSpec at HgPS HgSS
  icases HgPS with ⟨-, -, #HgPA⟩
  icases HgSS with ⟨-, #HgSD, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hsr0, Hmur⟩
  iunfold mvcc.storeReader at Hsr0
  iNamedSuffix Hsr0 "R"
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  wp_auto
  -- the victims out: the lock at `takeState`, the mover's batches
  imod ghostVar_update (mvcc.takeState σ slice.nil) γ.wst σ $$ Hσ with Hσ
  ihave Hnil : (slice.nil ↦* ([] : List GoMap) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnilc : ownSliceCap (GF := GF) GoMap slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  icases mvcc.body_take s γ σ Hok slice.nil $$
    [$Hσ $Hwlog $Hcert $Hsynced $Hunsynced $Hvf $Hnil $Hnilc $Hst $Hwo $Hmeta $Hwt $Hmfix $Hmem $Hout]
    with ⟨Hbody, Hmov⟩
  ihave Hmov2 := (BigSepL.bigSepL_sep_eqv (Φ := fun _ x => mvcc.ownWatcherBatch (GF := GF) x.1 x.2)
    (Ψ := fun _ x => iprop([∗map] w ↦ b ∈ x.2, mvcc.outW (GF := GF) γ w b))
    (l := σ.vbs.zip σ.VB)).2 $$ [Hvbs Hmov]
  · iframe Hvbs Hmov
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
  · inext; iunfold mvcc.watchStoreInv; iexists _; iexact Hbody
  ihave %Hvsl := ownSlice_len $$ Hvs
  have Hone := Hok.v_one
  generalize σ.vbs = vbs0 at *
  generalize σ.VB = VB0 at *
  generalize σ.vs = vs0 at *
  ihave IH : iprop(∃ (n : w64) (nvv : GoMap) (NV : GMap Loc mvcc.NvEnt) (mv : w64) (wbv : GoMap),
      "i" ∷ i_ptr ↦ n ∗ "newVictim" ∷ newVictim_ptr ↦ nvv ∗ "moved" ∷ moved_ptr ↦ mv ∗
      "wb" ∷ wb_ptr ↦ wbv ∗
      "Hnvm" ∷ (⌜nvv = map.nil ∧ NV = ∅⌝ ∨ nvv ↦$ GMap.fmap mvcc.NvEnt.eb NV) ∗
      "Hnvb" ∷ ([∗map] w ↦ x ∈ NV, mvcc.ownEventBatch x.eb x.B) ∗
      "Hnvr" ∷ ([∗map] w ↦ x ∈ NV, mvcc.moverResG γ w x.st x.B x.evsw x.γw) ∗
      "Hrest" ∷ ([∗list] x ∈ (vbs0.zip VB0).drop (sint.nat n),
        mvcc.ownWatcherBatch x.1 x.2 ∗ [∗map] w ↦ b ∈ x.2, mvcc.outW γ w b) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ vbs0.length ∧
        (∀ w x, NV !! w = some x → x.eb ≠ null) ∧
        (∀ w, (NV !! w).isSome → ∃ j B, j < sint.nat n ∧ VB0[j]? = some B ∧ (B !! w).isSome)⌝)
      $$ [i newVictim moved wb Hmov2]
  · iexists W64 0, _, ∅, _, _
    simp only [named]
    iframe i newVictim moved wb
    isplitr
    · ileft; ipureintro; constructor <;> first | rfl | trivial
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitl [Hmov2]
    · rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]; iexact Hmov2
    ipureintro
    refine ⟨by decide, by simp, fun w x h => by simp at h, fun w h => by simp at h⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vbs0.length := by word
    obtain ⟨vb, Hvb⟩ : ∃ x, vbs0[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨B, HB⟩ : ∃ B, VB0[sint.nat n]? = some B :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hvlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vs0.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) vb vs0 (DFrac.own 1) vbs0 Hn.1 Hvb $$ Hvs
      with ⟨Hel, Hvsback⟩
    wp_auto
    ihave Hvs := Hvsback $$ %vb Hel
    rw [mvcc.set_same Hvb]
    have Hz : (vbs0.zip VB0)[sint.nat n]? = some (vb, B) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨Hvb, HB⟩
    rw [List.drop_eq_getElem_cons (by simpa [Hvlen] using Hlt), (List.getElem?_eq_some_iff.1 Hz).2]
      at *
    icases BigSepL.bigSepL_cons.1 $$ Hrest with ⟨⟨Hwbo, HoutB⟩, Hrest⟩
    iunfold mvcc.ownWatcherBatch at Hwbo
    icases Hwbo with ⟨%PB, Hvbm, %HPB, Hbs⟩
    simp only at HPB
    subst HPB
    ihave HoutB' := (mvcc.mv_bigSepM_fmap (fun w b => mvcc.outW (GF := GF) γ w b) Prod.snd PB).1 $$ HoutB
    ihave Hrem0 := (mvcc.mv_bigSepM_sep _ _ PB).2 $$ [Hbs HoutB']
    · iframe Hbs HoutB'
    have hPBnv : ∀ k, (PB !! k).isSome → NV !! k = none := by
      intro k hk
      cases hn : NV !! k with
      | none => rfl
      | some _ =>
        obtain ⟨j, B', hj, hB', hk'⟩ := Hn.2.2.2 k (by rw [hn]; rfl)
        have := Hone j (sint.nat n) B' _ k hB' HB hk' (by rw [GMap.lookup_fmap]; cases h : PB !! k <;> simp_all)
        omega
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (PR PS : GMap Loc (Loc × mvcc.EventBatch))
        (NV' : GMap Loc mvcc.NvEnt) (nvv' : GoMap) (mv' : w64) (ebv wv : Loc),
        "newVictim" ∷ newVictim_ptr ↦ nvv' ∗ "moved" ∷ moved_ptr ↦ mv' ∗ "eb" ∷ eb_ptr ↦ ebv ∗
        "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗
        "Hnvm" ∷ (⌜nvv' = map.nil ∧ NV' = ∅⌝ ∨ nvv' ↦$ GMap.fmap mvcc.NvEnt.eb NV') ∗
        "Hnvb" ∷ ([∗map] w ↦ x ∈ NV', mvcc.ownEventBatch x.eb x.B) ∗
        "Hnvr" ∷ ([∗map] w ↦ x ∈ NV', mvcc.moverResG γ w x.st x.B x.evsw x.γw) ∗
        "Hrem" ∷ ([∗map] w ↦ p ∈ PR, (⌜p.1 ≠ null⌝ ∗ mvcc.ownEventBatch p.1 p.2) ∗ mvcc.outW γ w p.2) ∗
        "Hsent" ∷ ([∗map] w ↦ p ∈ PS, mvcc.sentW γ w p) ∗
        "%Hi" ∷ ⌜0 ≤ i ∧ (∀ k x, NV' !! k = some x → x.eb ≠ null) ∧
          (∀ k, PR !! k = if k ∈ keys.take i.toNat then none else PB !! k) ∧
          (∀ k, k ∉ keys.take i.toNat → PS !! k = none ∧ NV' !! k = NV !! k) ∧
          (∀ k, k ∈ keys.take i.toNat → (PS !! k = PB !! k ∧ NV' !! k = none) ∨
            (PS !! k = none ∧ ∃ x, NV' !! k = some x ∧ PB !! k = some (x.eb, x.B)))⌝)) $$ Hvbm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [newVictim moved eb w s Hnvm Hnvb Hnvr Hrem0]
    · iexists PB, ∅, NV, nvv, mv, zero_val Loc, zero_val Loc
      simp only [named, show (0 : Int).toNat = 0 from rfl, List.take_zero]
      iframe newVictim moved eb w s Hnvm Hnvb Hnvr Hrem0
      isplitr
      · iapply BigSepM.bigSepM_empty.2; iempintro
      ipureintro
      refine ⟨Int.le_refl _, Hn.2.2.1, fun k => by simp, fun k _ => by simp, fun k hk => by simp at hk⟩
    isplitr
    · imodintro
      iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
      iNamed HP
      obtain ⟨hi0, Hnvnn, HPR, HPSo, HPSi⟩ := Hi
      rw [GMap.lookup_fmap] at Hv
      obtain ⟨b, hp⟩ : ∃ b, PB !! key = some (v, b) := by
        cases h : PB !! key with
        | none => rw [h] at Hv; cases Hv
        | some p => rw [h] at Hv; obtain ⟨p1, p2⟩ := p; simp at Hv; subst Hv; exact ⟨p2, rfl⟩
      have hnot : key ∉ keys.take i.toNat := by
        intro hm
        obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
        rw [List.getElem_take] at hjk
        have hj' : keys[j]? = some key := by
          rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
        have := list_nodup_getElem?_inj keys Hknodup j i.toNat key hj' Hkey
        simp at hj; omega
      have hPRk : PR !! key = some (v, b) := by rw [HPR, ite_eq_right hnot, hp]
      icases (BigSepM.bigSepM_delete hPRk).1 $$ Hrem with ⟨⟨⟨%Hvnn, HB⟩, Hout⟩, Hrem⟩
      iunfold mvcc.outW at Hout
      icases Hout with ⟨%stw, Hmr⟩
      icases (mvcc.moverRes_G γ key stw b).1 $$ Hmr with ⟨%evsw, %γw, Hmr⟩
      iunfold mvcc.moverResG at Hmr
      icases Hmr with ⟨%r, %fcs, #Hm, #Hf, #Hc, #Hfo, %Hp, Hown, Hev, Hl, #Hwf⟩
      iunfold mvcc.watcherOwn at Hown
      icases Hown with ⟨HminRev, Hvict, Hcomp, Hres, Hchf⟩
      iunfold mvcc.ownEventBatch at HB
      icases HB with ⟨%sl, %ps, Heb, Hsl, Hcap, %Hlen, #HevB⟩
      ihave #Hf0 := Hf
      iunfold mvcc.watcherFixed at Hf0
      icases Hf0 with ⟨%Hwnn, %ks, %es', #Hk, #Hks, #He, #Hes, #Hsr', #Hid, #Hfcs⟩
      wp_auto
      simp only at Hlen Hvnn
      obtain ⟨hsr, hlo, hmore, hevs⟩ : sint.Z r.startRev ≤ (γw.lo : Int) ∧ (γw.lo : Int) ≤ sint.Z stw.minRev ∧
          (b.moreRev ≠ W64 0 → b.moreRev = stw.minRev) ∧
          ∀ ev ∈ b.evs, (γw.lo : Int) ≤ sint.Z ev.kv.modRev ∧ sint.Z ev.kv.modRev < sint.Z stw.minRev :=
        ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2⟩
      have hrev : sint.Z (stw.minRev - W64 1) = sint.Z stw.minRev - 1 := by
        have : (0 : Int) ≤ γw.lo := by omega
        word
      icases mvcc.mv_ev_pre γ γw r evsw b.evs (sint.nat stw.minRev) $$ [$Hev $Hwf] with ⟨HevS, HevK⟩
      wp_apply (hSend γ key γw r fcs stw.ch (1 : Qp).half (1 : Qp).half evsw (sint.nat stw.minRev) _ ps
          b.evs (DFrac.own 1)) $$ [Hchf Hl HevS Hsl] as %ok ⟨Hchf, Hl, Hsl, HevS⟩
      · iframe Hm Hf Hfo Hc Hchf Hl HevS Hsl HevB
        ipureintro
        refine ⟨Hlen, rfl, fun _ => rfl, ?_, ?_⟩
        · intro ev hev; have := (hevs ev hev).2; simp only; rw [hrev]; omega
        · intro _ ev hev; have := (hevs ev hev).1; omega
      ihave Hev := mvcc.mv_ev_post γw evsw b.evs ok $$ [$HevS $HevK]
      have hi1 : (i + 1).toNat = i.toNat + 1 := by omega
      have hnvk : NV' !! key = none := by rw [(HPSo key hnot).2, hPBnv key (by rw [hp]; rfl)]
      cases ok
      · -- the channel is full: the batch goes to `newVictim`
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_join iprop(∃ nm : GoMap, newVictim_ptr ↦ nm ∗ nm ↦$ GMap.fmap mvcc.NvEnt.eb NV') with
            [newVictim Hnvm] as ⟨%nm, newVictim, Hnm⟩
        · icases Hnvm with (⟨%Hnil1, %Hnil2⟩ | Hnvm)
          · subst Hnil2
            rw [go.make1_underlying, go.is_underlying (t := watcherBatch.ty)]
            wp_apply (wp_map_make1 (K := Loc) (V := Loc)) as %nm Hnm
            (try wp_auto)
            wp_join_done
            iexists nm; iframe newVictim
            rw [GMap.fmap_empty]; iexact Hnm
          · ihave %Hnn := ownMap_not_nil $$ Hnvm
            exfalso; apply Hnn; first | exact Hif | rfl
        · iexists nvv'; iframe newVictim
          icases Hnvm with (⟨%Hnil1, -⟩ | Hnvm)
          · exact absurd Hnil1 Hif
          · iexact Hnvm
        wp_apply wp_mapInsert $$ Hnm as Hnm
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        let x : mvcc.NvEnt := ⟨v, b, stw, evsw, γw⟩
        obtain ⟨hPR', hPSo', hPSi'⟩ := mvcc.mv_send_inv_fail PB NV NV' keys i.toNat key PR PS x
          Hkey hnot hp HPR HPSo HPSi
        iexists GMap.delete key PR, PS, <[key := x]> NV', nm, mv', v, key
        simp only [named]
        rw [hi1, ← mvcc.mv_std_delete_eq]
        iframe newVictim moved eb w s Hrem Hsent
        isplitl [Hnm]
        · iright
          rw [GMap.fmap_insert]; iexact Hnm
        isplitl [Hnvb Heb Hsl Hcap]
        · iapply (BigSepM.bigSepM_insert (m := NV') hnvk).2
          iframe Hnvb
          iunfold mvcc.ownEventBatch
          iexists sl, ps
          iframe Heb Hsl Hcap HevB
          ipureintro; exact Hlen
        isplitl [Hnvr HminRev Hvict Hcomp Hres Hchf Hev Hl]
        · iapply (BigSepM.bigSepM_insert (m := NV') hnvk).2
          iframe Hnvr
          iunfold mvcc.moverResG
          iexists r, fcs
          iframe Hm Hf Hc Hfo Hev Hl Hwf
          isplitr
          · ipureintro; exact Hp
          iunfold mvcc.watcherOwn
          iframe
        ipureintro
        refine ⟨by omega, fun k y hy => ?_, hPR', hPSo', hPSi'⟩
        by_cases hk : k = key
        · subst hk; rw [GMap.lookup_insert] at hy; cases hy; exact Hvnn
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at hy; exact Hnvnn k y hy
      · simp only [↓reduceIte]
        wp_auto
        wp_apply HgPA
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        obtain ⟨hPR', hPSo', hPSi'⟩ := mvcc.mv_send_inv_ok PB NV NV' keys i.toNat key PR PS (v, b)
          Hkey hnot hp (hPBnv key (by rw [hp]; rfl)) HPR HPSo HPSi
        have hpsk : PS !! key = none := (HPSo key hnot).1
        iexists GMap.delete key PR, <[key := (v, b)]> PS, NV', nvv', mv' + W64 1, v, key
        simp only [named]
        rw [hi1, ← mvcc.mv_std_delete_eq]
        iframe newVictim moved eb w s Hrem Hnvm Hnvb Hnvr
        isplitl [Hsent Heb HminRev Hvict Hcomp Hres Hchf Hev Hl]
        · iapply (BigSepM.bigSepM_insert (m := PS) hpsk).2
          iframe Hsent
          iunfold mvcc.sentW
          isplitl [Heb]
          · iexists sl; iexact Heb
          iexists stw, evsw ++ b.evs, γw
          iunfold mvcc.moverResG
          iexists r, fcs
          simp only [List.append_nil]
          iframe Hm Hf Hc Hfo Hev Hl Hwf
          isplitr
          · ipureintro; exact ⟨hsr, hlo, hmore, fun ev hev => by simp at hev⟩
          iunfold mvcc.watcherOwn
          iframe
        ipureintro
        exact ⟨by omega, Hnvnn, hPR', hPSo', hPSi'⟩
    iintro HP Hvbm
    iNamed HP
    irename Hvs => HvsM
    irename Hvcap => HvcapM
    obtain ⟨-, Hnvnn, HPR, HPSo, HPSi⟩ := Hi
    have hall : ∀ k, (PB !! k).isSome → k ∈ keys.take (GMap.size (GMap.fmap Prod.fst PB) : Int).toNat := by
      intro k hk
      rw [show ((GMap.size (GMap.fmap Prod.fst PB) : Int)).toNat = keys.length by rw [Hklen]; simp,
        List.take_length, Hkset, GMap.lookup_fmap]
      cases h : PB !! k <;> simp_all
    -- the lock and `revMu`
    wp_auto
    wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
    wp_auto_lc 1
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
    iunfold mvcc.watchStoreInv at HP
    icases HP with ⟨%σ1, HP⟩
    wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrl, HQ⟩
    wp_auto_lc 2
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv st γ.st sync.rfrac)) $$ Hlc1 HQ with HQ
    iunfold mvcc.revMuInv at HQ
    icases HQ with ⟨%C, %ntok, %cQ, HQ⟩
    iNamedSuffix HQ "Q"
    iunfold mvcc.watchStoreBody at HP
    iNamed HP
    icases persistent_entails_right (mvcc.idxLogAuth_cert_prefix γ.st.idx _ C σ1.Lmu) $$ [$HlogQ $Hcert]
      with ⟨%HpC, ⟨HlogQ, -⟩⟩
    ihave %HCwf : ⌜C.length < 2 ^ 63⌝ $$ [HcertQ]
    · iunfold mvcc.idxCert at HcertQ
      icases HcertQ with ⟨-, -, %H, -⟩
      ipureintro; exact H.2.1
    wp_auto
    ihave Hbody : mvcc.watchStoreBody s γ 1 σ1 $$ [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt
        Hmem]
    · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys2 : List Loc) (j : Int) => iprop(∃ (σ' : mvcc.WsState)
        (PS' : GMap Loc (Loc × mvcc.EventBatch)) (ebv wv : Loc),
        "eb" ∷ eb_ptr ↦ ebv ∗ "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗ "newVictim" ∷ newVictim_ptr ↦ nvv' ∗
        "curRev" ∷ curRev_ptr ↦ (W64 ((C.length : Int) - 1) : w64) ∗
        "Hnvm" ∷ (⌜nvv' = map.nil ∧ NV' = ∅⌝ ∨ nvv' ↦$ GMap.fmap mvcc.NvEnt.eb NV') ∗
        "Hsent" ∷ ([∗map] w ↦ p ∈ PS', mvcc.sentW γ w p) ∗
        "Hbody" ∷ mvcc.watchStoreBody s γ 1 σ' ∗
        "%Hq" ∷ ⌜0 ≤ j ∧ σ'.Lmu <+: C ∧
          ∀ k, PS' !! k = if k ∈ keys2.take j.toNat then none else PS !! k⌝)) $$ Hvbm
    iintro %keys2 ⟨%Hkset2, %Hklen2, %Hknodup2⟩
    isplitl [eb w s newVictim curRev Hnvm Hsent Hbody]
    · iexists σ1, PS, zero_val Loc, zero_val Loc
      simp only [named, show (0 : Int).toNat = 0 from rfl, List.take_zero]
      iframe eb w s newVictim curRev Hnvm Hsent Hbody
      ipureintro; exact ⟨Int.le_refl _, HpC, fun k => by simp⟩
    isplitr
    · imodintro
      iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
      iNamed HP
      obtain ⟨hj0, HLC, HPS'⟩ := Hq
      rw [GMap.lookup_fmap] at Hv
      obtain ⟨b, hp⟩ : ∃ b, PB !! key = some (v, b) := by
        cases h : PB !! key with
        | none => rw [h] at Hv; cases Hv
        | some p => rw [h] at Hv; obtain ⟨p1, p2⟩ := p; simp at Hv; subst Hv; exact ⟨p2, rfl⟩
      have hnot : key ∉ keys2.take j.toNat := by
        intro hm
        obtain ⟨j', hj, hjk⟩ := List.getElem_of_mem hm
        rw [List.getElem_take] at hjk
        have hj' : keys2[j']? = some key := by
          rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
        have := list_nodup_getElem?_inj keys2 Hknodup2 j' j.toNat key hj' Hkey
        simp at hj; omega
      have hj1 : (j + 1).toNat = j.toNat + 1 := by omega
      have hall' := hall key (by rw [hp]; rfl)
      wp_auto
      wp_join (Q := fun bv => iprop(⌜bv = #(decide ((NV' !! key).isSome))⌝ ∗
          (⌜nvv' = map.nil ∧ NV' = ∅⌝ ∨ nvv' ↦$ GMap.fmap mvcc.NvEnt.eb NV') ∗ newVictim_ptr ↦ nvv' ∗
          w_ptr ↦ key))
        at (if: _ then _ else #false) with [Hnvm newVictim w] as ⟨%Hbv, Hnvm, newVictim, w⟩
      · icases Hnvm with (⟨%Hnil1, %Hnil2⟩ | Hnvm)
        · subst Hnil1 Hnil2
          wp_auto
          iframe newVictim w
          isplitl []
          · ipureintro; simp
          ileft; ipureintro; exact ⟨rfl, rfl⟩
        · ihave %Hnn := ownMap_not_nil $$ Hnvm
          rw [decide_eq_false Hnn]
          wp_auto
          wp_apply wp_map_lookup1 $$ Hnvm as Hnvm
          iframe newVictim w
          isplitl []
          · ipureintro
            congr 1
            cases hk : NV' !! key with
            | none => simp; rfl
            | some x => simp [Hnvnn key x hk]
          iright; iexact Hnvm
      subst Hbv
      cases hnk : NV' !! key with
      | some x =>
        -- failed: skipped (its batch in `newVictim`)
        simp only [Option.isSome_some, decide_true]
        wp_auto
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        have hpsk : PS !! key = none := by
          rcases HPSi key hall' with ⟨-, h⟩ | ⟨h, -⟩
          · rw [hnk] at h; cases h
          · exact h
        iexists σ', PS', v, key
        simp only [named]
        rw [hj1]
        iframe eb w s newVictim curRev Hnvm Hsent Hbody
        ipureintro
        refine ⟨by omega, HLC, fun k => ?_⟩
        rw [HPS' k, mvcc.mv_take_succ keys2 j.toNat key Hkey]
        by_cases hk : k = key
        · subst hk; simp [hpsk]
        · simp [hk]
      | none =>
        simp only [Option.isSome_none, decide_false]
        have hpsk : PS !! key = some (v, b) := by
          rcases HPSi key hall' with ⟨h, -⟩ | ⟨-, x, h, -⟩
          · rw [h, hp]
          · rw [hnk] at h; cases h
        have hps'k : PS' !! key = some (v, b) := by rw [HPS', ite_eq_right hnot, hpsk]
        icases (BigSepM.bigSepM_delete hps'k).1 $$ Hsent with ⟨Hsw, Hsent⟩
        iunfold mvcc.sentW at Hsw
        icases Hsw with ⟨⟨%sl, Heb⟩, %stw, %evsw, %γw, Hmr⟩
        iunfold mvcc.moverResG at Hmr
        icases Hmr with ⟨%r, %fcs, #Hm, #Hf, #Hc, #Hfo, %Hp, Hown, Hev, Hl, #Hwf⟩
        obtain ⟨hsr, hlo, hmore, -⟩ := Hp
        iunfold mvcc.watchStoreBody at Hbody
        iNamedSuffix Hbody "B"
        icases persistent_entails_right (mvcc.mv_wo_lookup γ σ' HokB key γw stw) $$
          [$HmetaB $Hm $HstB $HwoB $Hown] with ⟨%Hwo, ⟨HmetaB, -, HstB, HwoB, Hown⟩⟩
        icases (BigSepM.bigSepM_delete Hwo).1 $$ HwoB with ⟨Hown2, HwoB⟩
        ihave Hfull := (mvcc.mv_watcherOwn_halves key stw).2 $$ [Hown Hown2]
        · iframe Hown Hown2
        iunfold mvcc.watcherOwn at Hfull
        icases Hfull with ⟨HminRev, Hvict, Hcomp, Hres, Hchf⟩
        wp_auto
        wp_join iprop(key.[watcher, go!"minRev"] ↦ stw.minRev ∗
            v ↦ ({ evs' := sl, revs' := b.revs, moreRev' := b.moreRev } : eventBatch) ∗
            eb_ptr ↦ v ∗ w_ptr ↦ key) with [HminRev Heb eb w] as ⟨HminRev, Heb, eb, w⟩
        · rw [hmore Hif]
          iframe
        rw [mvcc.mv_std_delete_eq] at *
        ihave #Hm0 := Hm
        iunfold mvcc.watcherMeta at Hm0
        ihave %hM := ghost_map_lookup $$ HmetaB Hm0
        icases mvcc.watchBudget_bound _ _ _ $$ HwtB with ⟨HwtB, %HMb⟩
        obtain ⟨-, -, hWs0, hWu0, -, -⟩ := HokB.out Hwo
        have hCne : 1 ≤ C.length := List.length_pos_iff.2 HneQ
        have hcur : sint.Z (W64 ((C.length : Int) - 1)) = (C.length : Int) - 1 := by word
        have hLC := HLC.length_le
        have hnat : (sint.nat stw.minRev : Int) = sint.Z stw.minRev := by
          show ((sint.Z stw.minRev).toNat : Int) = _; omega
        wp_if_destruct
        · -- at or below the current revision: unsynced
          rw [hcur] at Hif
          imod ghostVar_update (mvcc.readdState σ' key r { stw with victim := false } false
            (evsw, sint.nat stw.minRev)) γ.wst σ' $$ Hσ with Hσ
          wp_apply (hAdd (mvcc.unsyncedAddr s) σ'.Wu key r fcs) $$ [$HunsyncedB $Hf] as HunsyncedB
          · ipureintro; exact ⟨hWu0, by have := HokB.wu_size; omega⟩
          (try wp_auto)
          have hd : false = true → max γw.lo σ'.Lmu.length ≤ sint.nat stw.minRev := fun h => by cases h
          ihave Hcrt : (if false = true then iprop(True) else
              ∃ Lc : mvcc.Log, mvcc.idxCert γ.st.idx Lc ∗ ⌜sint.Z stw.minRev < Lc.length⌝ : IProp GF) $$ []
          · simp only [Bool.false_eq_true, ↓reduceIte]
            iexists C; iframe HcertQ; ipureintro; omega
          simp only [Bool.false_eq_true, ↓reduceIte]

          ihave Hbody := mvcc.body_readd s γ σ' _ HokB key stw Hwo r false γw hM fcs evsw hlo hsr hd rfl $$
            [Hσ HwlogB HsyncedB HunsyncedB HvfB HvsB HvcapB HvbsB HstB HminRev Hvict Hcomp Hres Hchf HwoB
             HmetaB HwtB HmemB Hev Hl Hcrt]
          · simp only [List.append_nil, Bool.false_eq_true, ↓reduceIte]
            iframe Hσ HwlogB HsyncedB HunsyncedB HvfB HvsB HvcapB HvbsB HstB HwoB HmetaB HwtB HmemB Hev Hl Hcrt
            iframe #
            isplitr
            · ipureintro; exact HvlenB
            iunfold mvcc.watcherOwn
            iframe
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _, GMap.delete key PS', v, key
          simp only [named]
          rw [hj1, ← mvcc.mv_std_delete_eq]
          iframe eb w s newVictim curRev Hnvm Hsent Hbody
          ipureintro
          refine ⟨by omega, HLC, fun k => ?_⟩
          rw [mvcc.mv_take_succ keys2 j.toNat key Hkey]
          show GMap.delete key PS' !! k = _
          by_cases hk : k = key
          · subst hk; rw [GMap.lookup_delete]; simp
          · rw [GMap.lookup_delete_ne _ (Ne.symm hk), HPS' k]; simp [hk]
        · -- above: synced
          rw [hcur] at Hif
          imod ghostVar_update (mvcc.readdState σ' key r { stw with victim := false } true
            (evsw, sint.nat stw.minRev)) γ.wst σ' $$ Hσ with Hσ
          wp_apply HgSD
          (try wp_auto)
          wp_apply (hAdd (mvcc.syncedAddr s) σ'.Ws key r fcs) $$ [$HsyncedB $Hf] as HsyncedB
          · ipureintro; exact ⟨hWs0, by have := HokB.ws_size; omega⟩
          (try wp_auto)
          have hd : true = true → max γw.lo σ'.Lmu.length ≤ sint.nat stw.minRev := fun _ => by omega
          ihave Hcrt : (if true = true then iprop(True) else
              ∃ Lc : mvcc.Log, mvcc.idxCert γ.st.idx Lc ∗ ⌜sint.Z stw.minRev < Lc.length⌝ : IProp GF) $$ []
          · simp only [↓reduceIte]; itrivial
          simp only [↓reduceIte]

          ihave Hbody := mvcc.body_readd s γ σ' _ HokB key stw Hwo r true γw hM fcs evsw hlo hsr hd rfl $$
            [Hσ HwlogB HsyncedB HunsyncedB HvfB HvsB HvcapB HvbsB HstB HminRev Hvict Hcomp Hres Hchf HwoB
             HmetaB HwtB HmemB Hev Hl Hcrt]
          · simp only [List.append_nil, Bool.false_eq_true, ↓reduceIte]
            iframe Hσ HwlogB HsyncedB HunsyncedB HvfB HvsB HvcapB HvbsB HstB HwoB HmetaB HwtB HmemB Hev Hl Hcrt
            iframe #
            isplitr
            · ipureintro; exact HvlenB
            iunfold mvcc.watcherOwn
            iframe
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _, GMap.delete key PS', v, key
          simp only [named]
          rw [hj1, ← mvcc.mv_std_delete_eq]
          iframe eb w s newVictim curRev Hnvm Hsent Hbody
          ipureintro
          refine ⟨by omega, HLC, fun k => ?_⟩
          rw [mvcc.mv_take_succ keys2 j.toNat key Hkey]
          show GMap.delete key PS' !! k = _
          by_cases hk : k = key
          · subst hk; rw [GMap.lookup_delete]; simp
          · rw [GMap.lookup_delete_ne _ (Ne.symm hk), HPS' k]; simp [hk]
    iintro HQ Hvbm
    iNamed HQ
    obtain ⟨-, HLC, HPS'⟩ := Hq
    wp_auto
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HrevQ HclogQ HbucketQ HtoksQ HlogQ HcmpQ HcrevQ]
    · inext
      iunfold mvcc.revMuInv
      iexists C, ntok, cQ
      simp only [named]
      iframe HrevQ HclogQ HbucketQ HtoksQ HlogQ HcmpQ HcrevQ
      iframe #
      ipureintro; exact ⟨HneQ, HbudgetQ, HcQ⟩
    iintro HrevMuR
    wp_auto
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
    · inext; iunfold mvcc.watchStoreInv; iexists _; iexact Hbody
    wp_for_post
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iframe HΦ Hmur HmuR HrevMuR HtiR HrtR s HvsM HvcapM
    iexists n + W64 1, nvv', NV', mv', vb
    simp only [named]
    rw [hn1]
    iframe i newVictim moved wb Hnvm Hnvb Hnvr Hrest
    ipureintro
    refine ⟨by word, by omega, Hnvnn, fun k hk => ?_⟩
    by_cases hkin : k ∈ keys.take (GMap.size (GMap.fmap Prod.fst PB) : Int).toNat
    · rcases HPSi k hkin with ⟨-, h⟩ | ⟨-, x, -, hpk⟩
      · rw [h] at hk; cases hk
      · exact ⟨sint.nat n, GMap.fmap Prod.snd PB, by omega, HB, by rw [GMap.lookup_fmap, hpk]; rfl⟩
    · rw [(HPSo k hkin).2] at hk
      obtain ⟨j, B', hj, h1, h2⟩ := Hn.2.2.2 k hk
      exact ⟨j, B', by omega, h1, h2⟩
  · -- the failed ones: victims again, in one batch
    ihave HR : mvcc.watchReader s st γ $$ [Hmur HmuR HrevMuR HtiR HrtR]
    · iunfold mvcc.watchReader; iframe Hmur
      iunfold mvcc.storeReader; iexists ti; simp only [named]; iframe; iframe #
    icases Hnvm with (⟨%Hnil1, %Hnil2⟩ | Hnvm)
    · subst Hnil1
      wp_auto
      iapply HΦ $$ HR
    ihave %Hnvnn := ownMap_not_nil $$ Hnvm
    wp_apply wp_map_len_lt $$ Hnvm as ⟨Hnvm, %Hszlt⟩
    have hsz : (W64 ((GMap.fmap mvcc.NvEnt.eb NV).size : Int) = W64 0) ↔ (GMap.fmap mvcc.NvEnt.eb NV).size = 0 := by
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; omega
      · intro h; rw [h]; rfl
    wp_if_destruct
    · wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HP⟩
      wp_auto_lc 1
      imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
      iunfold mvcc.watchStoreInv at HP
      icases HP with ⟨%σ2, HP⟩
      iunfold mvcc.watchStoreBody at HP
      iNamed HP
      icases persistent_entails_right (mvcc.mv_nv_wo γ σ2 Hok NV) $$ [$Hmeta $Hst $Hwo $Hnvr]
        with ⟨%HNV2, ⟨Hmeta, Hst, Hwo, Hnvr⟩⟩
      (try wp_auto)
      wp_apply wp_slice_literal (l := [nvv])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, Hzcap⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hvs $Hvcap $Hz] as %vs' ⟨Hvs, Hvcap, -⟩
      (try wp_auto)
      imod ghostVar_update (mvcc.appendState σ2 NV vs' nvv) γ.wst σ2 $$ Hσ with Hσ
      ihave Hbody := mvcc.body_append s γ σ2 _ Hok NV vs' nvv HNV2 rfl $$
        [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem Hnvm Hnvb Hnvr]
      · iframe Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem Hnvm Hnvr
        iframe #
        isplitr
        · ipureintro; exact Hvlen
        iapply (BigSepM.bigSepM_mono (fun {k x} hk => ?_)) $$ Hnvb
        iintro H; iframe H; ipureintro; exact Hn.2.2.1 k x hk
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hbody]
      · inext; iunfold mvcc.watchStoreInv; iexists _; iexact Hbody
      (try wp_auto)
      iapply HΦ $$ HR
    · (try wp_auto)
      iapply HΦ $$ HR

end proof

end EtcdGrove
end Perennial
