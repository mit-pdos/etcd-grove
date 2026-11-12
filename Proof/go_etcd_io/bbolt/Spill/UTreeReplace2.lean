/-
The spill's pure tree facts (U9f, `notes/bbolt-proof-plan.md`): **the parent's branch after a
child's spill** (`uBr_replace`): entry `j`'s unspilled child `c` replaced by the pieces, finished
subtrees, the parent's facts kept (`node.spill`'s children's loop).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeReplace

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section replace
variable [GooseExts]

/-- The descriptor of a piece's entry: a finished subtree. -/
def pcUE (P : Pages) (x : Piece) : UE := ⟨none, [], pgSlots P x.S, [], treeEls P x.id.toNat⟩

theorem uEnt_N_node {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {ws : List WEntry} {cs : List Loc} {h i : Nat} {w : WEntry}
    {e : UE} (he : uEnt X bl P hwm n lo hi ws cs h i w e) :
    ∀ l ∈ e.N, ∃ r, X.node bl l = some r ∧ r.nv.spilled' = false := by
  cases he with
  | child _ _ _ _ _ _ _ _ c rc F D N E _ _ _ _ _ _ _ hut => exact uTree_N_unspilled hut
  | fin => intro l hl; simp at hl

theorem not_spilledN_of {X : WX} {bl l : Loc} {r : NRec} (hr : X.node bl l = some r)
    (hs : r.nv.spilled' = false) : ¬ spilledN X bl l := by
  rintro ⟨_, rc, hrc, _, hsp, _⟩
  rw [hr] at hrc; cases hrc; rw [hs] at hsp; cases hsp

theorem piece_spilledN {X : WX} {bl pl : Loc} {P : Pages} {hwm : Nat} {lo hi : Option (List w8)}
    {h : Nat} {ps : List Piece} (hps : piecesOK X bl pl P hwm lo hi h ps) {x : Piece}
    (hx : x ∈ ps) : spilledN X bl x.l := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨rl, hn, hl, hb, hsp, hcs, -, -, -, hne, -⟩ := hps.2.2 i x hi
  exact ⟨hl, rl, hn, hb, hsp, hcs, hne⟩

theorem splice_get {ws ws' : List WEntry} {ps : List Piece} {j : Nat}
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) (hm : 0 < ps.length) {w' : WEntry} (hw' : w' ∈ ws') :
    (∃ w ∈ ws, wDat w' = wDat w) ∨ (∃ x ∈ ps, wDat w' = pcDat x) := by
  have hlen := splice_length hd hj
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw'
  have hil : i < ws'.length := (List.getElem?_eq_some_iff.1 hi).1
  by_cases hij : i < j
  · obtain ⟨w1, w, h1, h2, hw⟩ := splice_lt hd hj hij
    rw [hi] at h1; cases h1
    exact Or.inl ⟨w, List.mem_of_getElem? h2, hw⟩
  by_cases him : i < j + ps.length
  · obtain ⟨k, rfl⟩ : ∃ k, i = j + k := ⟨i - j, by omega⟩
    obtain ⟨w1, x, h1, h2, hw⟩ := splice_mid hd hj (k := k) (by omega)
    rw [hi] at h1; cases h1
    exact Or.inr ⟨x, List.mem_of_getElem? h2, hw⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + ps.length - 1 := ⟨i + 1 - ps.length, by omega⟩
    obtain ⟨w1, w, h1, h2, hw⟩ := splice_hi hd hj (k := k) (by omega) (by omega)
    rw [hi] at h1; cases h1
    exact Or.inl ⟨w, List.mem_of_getElem? h2, hw⟩

/-- **The parent's branch after a child's spill** (see the module doc): `n`'s branch facts at
`X` (record `r`, descriptors `es`), entry `j` the unspilled child `c` (base pages `Fc`, slots
`Dc`, nodes `Nc`); `c`'s spill a step from `X` to `X'` touching `Nc`, fresh nodes and `n`, the
page map kept on the other entries' slots, its pieces `ps` (first `c`, the others fresh, keys
fitting an entry) put in `n` (record `r'`). -/
theorem uBr_replace {X X' : WX} {bl n : Loc} {P P' : Pages} {hwm hwm' : Nat} {T : List Loc}
    {r r' : NRec} {lo hi : Option (List w8)} {h : Nat} {es : List UE} {j : Nat} {c : Loc}
    {Fc Dc : List Nat} {Nc : List Loc} {Ec : List El} {ps : List Piece}
    (hb : uBr X bl P hwm n r lo hi h es) (hj : es[j]? = some ⟨some c, Fc, Dc, Nc, Ec⟩)
    (hfr : spFrame X X' bl T) (hh : hwm ≤ hwm')
    (hT : ∀ l ∈ T, l ∈ Nc ∨ X.node bl l = none ∨ l = n)
    (hP : ∀ k e, k ≠ j → es[k]? = some e → ∀ x ∈ e.D, P' !! x = P !! x)
    (hps : piecesOK X' bl n P' hwm' (childLo lo (wKey r.ws) j)
      (childHi hi (wKey r.ws) r.ws.length j) h ps)
    (hhd : ps.head?.map Piece.l = some c)
    (hr' : X'.node bl n = some r') (hpar : parentSpilled r r' j ps) (hlive : n ∈ X'.live)
    (hfresh : ∀ x ∈ ps.drop 1, x.l ∉ r.cs)
    (hkl : ∀ x ∈ ps, 0 < x.k.length ∧ x.k.length ≤ bboltEntryMax) :
    uBr X' bl P' hwm' n r' lo hi h (es.take j ++ ps.map (pcUE P') ++ es.drop (j + 1)) := by
  obtain ⟨hd, hcs', hnv, -, -, hcap, hins⟩ := hpar
  have hjes : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  have hjl : j < r.ws.length := by rw [← hb.len]; exact hjes
  have hm : 0 < ps.length := List.length_pos_iff.2 hps.1
  have hlen' := splice_length hd hjl
  have hLlen : (ps.map (pcUE P')).length = ps.length := List.length_map _
  have hwsget : ∀ k, k < r.ws.length → ∃ w, r.ws[k]? = some w :=
    fun k hk => ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨wj, hwj⟩ := hwsget j hjl
  have hentj := hb.ent j wj _ hwj hj
  obtain ⟨hcmem, hcN⟩ : c ∈ r.cs ∧
      ∀ l ∈ Nc, ∃ r, X.node bl l = some r ∧ r.nv.spilled' = false := by
    cases hentj with
    | child _ _ _ _ _ _ _ _ _ rc _ _ _ _ hc _ _ _ _ _ _ hut => exact ⟨hc, uTree_N_unspilled hut⟩
  -- the touched nodes
  have hTsp : ∀ l ∈ T, ¬ spilledN X bl l := by
    intro l hl
    rcases hT l hl with hl | hl | rfl
    · obtain ⟨r0, h0, hs0⟩ := hcN l hl; exact not_spilledN_of h0 hs0
    · rintro ⟨_, rc, hrc, _⟩; rw [hl] at hrc; cases hrc
    · exact not_spilledN_of hb.node hb.un.2.2.1
  have hNnd := List.nodup_cons.1 hb.Nnd
  have hTN : ∀ k e, k ≠ j → es[k]? = some e → ∀ l ∈ T, l ∉ e.N := by
    intro k e hk he l hl
    rcases hT l hl with hl | hl | rfl
    · exact flatMap_disj hNnd.2 hj he (Ne.symm hk) hl
    · intro hmem
      have hkl : k < r.ws.length := by rw [← hb.len]; exact (List.getElem?_eq_some_iff.1 he).1
      obtain ⟨wk, hwk⟩ := hwsget k hkl
      obtain ⟨r0, h0, -⟩ := uEnt_N_node (hb.ent k wk e hwk he) l hmem
      rw [hl] at h0; cases h0
    · intro hmem; exact hNnd.1 (List.mem_flatMap.2 ⟨e, List.mem_of_getElem? he, hmem⟩)
  -- the keys
  have hun := hb.un
  have hent0 : ∀ w ∈ r.ws, keyIn lo hi w.key ∧ 0 < w.key.length ∧
      w.key.length + w.value.length ≤ bboltEntryMax := hun.2.2.2.2.2.2.1
  have hKin : ∀ k, k < r.ws.length → keyIn lo hi (wKey r.ws k) := by
    intro k hk
    obtain ⟨w, hw⟩ := hwsget k hk
    rw [wKey_of_get hw]; exact (hent0 w (List.mem_of_getElem? hw)).1
  have hpk : ∀ k, k < ps.length → keyIn (childLo lo (wKey r.ws) j)
      (childHi hi (wKey r.ws) r.ws.length j) (pcKey ps k) := by
    intro k hk
    have hx : ps[k]? = some ps[k] := List.getElem?_eq_getElem hk
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hkey, _⟩ := hps.2.2 k _ hx
    rw [pcKey_of_get hx]; exact hkey
  have hlo : 0 < j → ¬ go.GoStringLt (pcKey ps 0) (wKey r.ws j) := by
    intro hj0
    exact (hpk 0 hm).1 _ (by unfold childLo; rw [if_neg (by omega)])
  have hhi : j + 1 < r.ws.length → ∀ k < ps.length,
      go.GoStringLt (pcKey ps k) (wKey r.ws (j + 1)) := by
    intro hj1 k hk
    exact (hpk k hk).2 _ (by unfold childHi; rw [if_pos hj1])
  have hbnd : bndIn (childLo lo (wKey r.ws) j, childHi hi (wKey r.ws) r.ws.length j) (lo, hi) := by
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simp only at hy ⊢
      unfold childLo
      by_cases hj0 : j = 0
      · rw [if_pos hj0]; exact ⟨y, hy, rk_le_refl y⟩
      · rw [if_neg hj0]; exact ⟨_, rfl, (hKin j hjl).1 y hy⟩
    · simp only at hy ⊢
      unfold childHi
      by_cases hj1 : j + 1 < r.ws.length
      · rw [if_pos hj1]; exact ⟨_, rfl, rk_le_of_lt ((hKin _ hj1).2 y hy)⟩
      · rw [if_neg hj1]; exact ⟨y, hy, rk_le_refl y⟩
  have hsorted := splice_sorted hd hjl hm hun.2.2.2.2.2.1 (pieces_sorted hps) hlo hhi
  -- the struct
  have hpg : r'.nv.pgid' = r.nv.pgid' := by rw [hnv]
  have hcsub : ∀ c ∈ r.cs, c ∈ r'.cs := fun c hc => by
    rw [hcs']; exact List.mem_append_left _ hc
  have hun' : uNode X' bl n r' lo hi := by
    refine ⟨hlive, by rw [hnv]; exact hun.2.1, by rw [hnv]; exact hun.2.2.1,
      by rw [hcap]; exact hun.2.2.2.1, hins, hsorted, fun w' hw' => ?_, ?_⟩
    · rcases splice_get hd hjl hm hw' with ⟨w, hw, he⟩ | ⟨x, hx, he⟩
      · rw [wDat_key he, wDat_value he]; exact hent0 w hw
      · have hk : w'.key = x.k := congrArg (fun d => d.2.2.1) he
        have hv : w'.value = [] := congrArg (fun d => d.2.2.2) he
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
        have hil : i < ps.length := (List.getElem?_eq_some_iff.1 hi).1
        have hki := hpk i hil
        rw [pcKey_of_get hi] at hki
        rw [hk, hv]
        exact ⟨keyIn_bndIn hbnd _ hki, (hkl x hx).1, by simp; exact (hkl x hx).2⟩
    · unfold ownPg; rw [hpg, hfr.2.2.2.2.1]; exact hun.2.2.2.2.2.2.2
  refine ⟨hr', hun', by rw [hnv]; exact hb.leaf, by have := hb.two; omega,
    by rw [esp_length hjes, hLlen, hb.len, hlen'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the entries
    intro i w' e hw' he
    have hil : i < r'.ws.length := (List.getElem?_eq_some_iff.1 hw').1
    by_cases hij : i < j
    · rw [esp_lt hjes hij] at he
      obtain ⟨w1, w, h1, h2, hw⟩ := splice_lt hd hjl hij
      rw [hw'] at h1; cases h1
      refine uEnt_move hfr hh (hb.ent i w e h2 he) (hP i e (by omega) he)
        (fun l hl => ⟨hTN i e (by omega) he l hl, hTsp l hl⟩) hw hcsub ?_
      have e1 : childLo lo (wKey r'.ws) i = childLo lo (wKey r.ws) i := by
        unfold childLo; split
        · rfl
        · rw [splice_key_lt hd hjl hij]
      rw [e1]
      refine ⟨fun y hy => ⟨y, hy, rk_le_refl y⟩, fun y hy => ?_⟩
      simp only at hy ⊢
      unfold childHi at hy ⊢
      rw [if_pos (by omega)] at hy ⊢
      by_cases hij1 : i + 1 < j
      · rw [splice_key_lt hd hjl hij1] at hy
        exact ⟨y, hy, rk_le_refl y⟩
      · have ej : i + 1 = j := by omega
        have hkm := splice_key_mid hd hjl hm
        simp only [Nat.add_zero] at hkm
        rw [ej, hkm] at hy
        rw [ej]
        cases hy
        exact ⟨_, rfl, hlo (by omega)⟩
    by_cases him : i < j + ps.length
    · obtain ⟨k, rfl⟩ : ∃ k, i = j + k := ⟨i - j, by omega⟩
      have hk : k < ps.length := by omega
      rw [esp_mid hjes (by rw [hLlen]; exact hk), List.getElem?_map,
        List.getElem?_eq_getElem hk] at he
      cases he
      obtain ⟨w1, x, h1, h2, hw⟩ := splice_mid hd hjl hk
      rw [hw'] at h1; cases h1
      rw [List.getElem?_eq_getElem hk] at h2; cases h2
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩ := hps.2.2 k _ (List.getElem?_eq_getElem hk)
      have hpgid : w'.pgid = ps[k].id := congrArg (fun d => d.2.1) hw
      have hkey : w'.key = ps[k].k := congrArg (fun d => d.2.2.1) hw
      refine uEnt.fin n lo hi r'.ws r'.cs h (j + k) w' ps[k].S _ ?_
      rw [hpgid, hkey]
      have e2 : childHi hi (wKey r'.ws) r'.ws.length (j + k) =
          childHi (childHi hi (wKey r.ws) r.ws.length j) (pcKey ps) ps.length k := by
        unfold childHi
        by_cases hk1 : k + 1 < ps.length
        · rw [if_pos (by omega), if_pos hk1, show j + k + 1 = j + (k + 1) by omega,
            splice_key_mid hd hjl hk1]
        · rw [if_neg hk1]
          by_cases hj1 : j + 1 < r.ws.length
          · rw [if_pos (by omega), if_pos hj1,
              show j + k + 1 = (j + 1) + ps.length - 1 by omega,
              splice_key_hi hd hjl (by omega) hj1]
          · rw [if_neg (by omega), if_neg hj1]
      rw [e2]; exact hf
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + ps.length - 1 := ⟨i + 1 - ps.length, by omega⟩
      have hjk : j < k := by omega
      have hk : k < r.ws.length := by omega
      rw [show k + ps.length - 1 = k + (ps.map (pcUE P')).length - 1 by rw [hLlen],
        esp_hi hjes hjk (by rw [hLlen]; exact hm)] at he
      obtain ⟨w1, w, h1, h2, hw⟩ := splice_hi hd hjl hjk hk
      rw [hw'] at h1; cases h1
      refine uEnt_move hfr hh (hb.ent k w e h2 he) (hP k e (by omega) he)
        (fun l hl => ⟨hTN k e (by omega) he l hl, hTsp l hl⟩) hw hcsub ?_
      have e1 : childLo lo (wKey r'.ws) (k + ps.length - 1) = childLo lo (wKey r.ws) k := by
        unfold childLo
        rw [if_neg (by omega), if_neg (by omega), splice_key_hi hd hjl hjk hk]
      have e2 : childHi hi (wKey r'.ws) r'.ws.length (k + ps.length - 1) =
          childHi hi (wKey r.ws) r.ws.length k := by
        unfold childHi
        by_cases hk1 : k + 1 < r.ws.length
        · rw [if_pos (by omega), if_pos hk1, show k + ps.length - 1 + 1 = (k + 1) + ps.length - 1
            by omega, splice_key_hi hd hjl (by omega) hk1]
        · rw [if_neg (by omega), if_neg hk1]
      rw [e1, e2]; exact bndIn_refl _
  · -- the children of the entries
    refine hb.chnd.sublist (esp_filterMap_sub UE.ch hjes ?_)
    simp [pcUE]
  · -- the children
    intro c' hc'
    rw [hcs'] at hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · rcases hb.cs c' hc' with ⟨e, he, hec⟩ | hsp
      · by_cases hcc : c' = c
        · subst hcc
          right
          obtain ⟨x0, rest, hps0⟩ : ∃ x0 rest, ps = x0 :: rest := by
            cases ps with
            | nil => exact absurd rfl hps.1
            | cons x0 rest => exact ⟨x0, rest, rfl⟩
          subst hps0
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
          rw [← hhd]; exact piece_spilledN hps List.mem_cons_self
        · left
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
          have hkj : k ≠ j := by
            rintro rfl; rw [hj] at hk; cases hk; simp at hec; exact hcc hec.symm
          refine ⟨e, ?_, hec⟩
          rcases Nat.lt_or_gt_of_ne hkj with hlt | hgt
          · exact List.mem_of_getElem? (by rw [esp_lt hjes hlt]; exact hk)
          · exact List.mem_of_getElem? (esp_hi (L := ps.map (pcUE P')) hjes hgt
              (by rw [hLlen]; exact hm) ▸ hk)
      · exact Or.inr (spilledN_frame hfr hsp fun hcT => hTsp c' hcT hsp)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc'
      exact Or.inr (piece_spilledN hps (List.mem_of_mem_drop hx))
  · -- the children are distinct
    rw [hcs']
    refine List.nodup_append.2 ⟨hb.csnd, ?_, ?_⟩
    · rw [List.map_drop]; exact hps.2.1.sublist (List.drop_sublist _ _)
    · intro a ha b hbm hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hbm
      exact hfresh x hx (hab ▸ ha)
  · -- the nodes are distinct
    refine hb.Nnd.sublist (List.Sublist.cons₂ n (esp_flatMap_sub UE.N hjes ?_))
    simp [pcUE]
  · -- a node without a page has no unspilled child
    intro h0
    exfalso
    have := hb.pg0 (by rw [← hpg]; exact h0) _ (List.mem_of_getElem? hj)
    simp at this

end replace

end Spill

end bbolt
end EtcdGrove
end Perennial
