/-
`node.spill` after its children's loop (U9w, `notes/bbolt-proof-plan.md`; pure): **a piece's
premises at iteration `i`** (`pcInv_pre'`, `pieceOne_wp`'s): from the piece's record (the split's
modulo sources, `pcLoop.todo`), the spill's global state (`pcLoop.step`), the slots
(`pcLoop.slot`), the entries' subtrees (`pcEnts`) and, for piece `0`'s page, the state at the
split (`pcLoop.start`) and the children's loop's `spFree`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitPre
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitSize

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pcpre
variable [GooseExts] [GoGlobalContext]

theorem splitRec_nv (rN : NRec) (x : Loc × node × List Inode) (ws : List WEntry) (f o : Bool) :
    (splitRec rN x ws f o).nv = x.2.1 := by unfold splitRec; split <;> rfl

theorem splitRec_ws (rN : NRec) (x : Loc × node × List Inode) (ws : List WEntry) (f o : Bool) :
    (splitRec rN x ws f o).ws = ws := by unfold splitRec; split <;> rfl

theorem splitRec_ins (rN : NRec) (x : Loc × node × List Inode) (ws : List WEntry) (f o : Bool) :
    (splitRec rN x ws f o).ins = x.2.2 := by unfold splitRec; split <;> rfl

private theorem setNode_mv (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.mv = X.t.mv := by
  unfold WX.setNode; split <;> rfl

theorem nilCh_pm' (X : WX) (bl n : Loc) (r : NRec) : (X.nilCh bl n r).t.pm = X.t.pm := by
  unfold WX.nilCh WX.killL WX.setNode; split <;> rfl

theorem nodup_len_le {L : List w64} {B : Nat} (hn : L.Nodup) (hb : ∀ x ∈ L, x.toNat < B) :
    L.length ≤ B := by
  have h1 : (L.map BitVec.toNat).Nodup :=
    List.Pairwise.map BitVec.toNat (fun a b hab e => hab (BitVec.eq_of_toNat_eq e)) hn
  have h2 : (L.map BitVec.toNat) ⊆ List.range B := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact List.mem_range.2 (hb x hx)
  have := (List.subperm_of_subset h1 h2).length_le
  simpa using this

/-- An allocation's id is below the new mark (the free ids below the mark). -/
theorem allocRes_id_lt_free {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} (h : allocRes X X' fl fl' txid count p id)
    (hfree : ∀ x ∈ fl.free, x.toNat < X.t.mv.pgid'.toNat) :
    id.toNat < X'.t.mv.pgid'.toNat := by
  obtain ⟨hc, -, Xr, -, hX'⟩ := h
  rcases hX' with ⟨⟨-, hrun⟩, -, rfl⟩ | ⟨rfl, -, hlt, rfl⟩
  · rw [addPage_pgid]
    exact hfree id (hrun id ⟨Nat.le_refl _, by omega⟩)
  · rw [addPage_pgid]
    have : (X.t.mv.pgid' + W64 (count : Int)).toNat = X.t.mv.pgid'.toNat + count := by word
    rw [this]; omega

/-- An allocation never returns a slot below the mark that is no free id. -/
theorem allocRes_ne_slot {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} (h : allocRes X X' fl fl' txid count p id) {s : Nat}
    (hlt : s < X.t.mv.pgid'.toNat) (h62 : s < 2 ^ 62) (hnot : W64 (s : Int) ∉ fl.free) :
    id.toNat ≠ s := by
  obtain ⟨hc, -, Xr, -, hX'⟩ := h
  rcases hX' with ⟨⟨-, hrun⟩, -, -⟩ | ⟨rfl, -, -, -⟩
  · intro e
    have hm := hrun id ⟨Nat.le_refl _, by omega⟩
    apply hnot
    have : W64 (s : Int) = id := by
      apply BitVec.eq_of_toNat_eq; rw [← e]; simp <;> omega
    rw [this]; exact hm
  · omega

/-- **The children's loop's `spFree` of `n`'s own page.** -/
theorem spEnd_free0 {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    spFree X' w'.fl w.wtxid (ownF r'.nv.pgid') := by
  obtain ⟨hn, -, hc⟩ := hpre
  rcases hc with ⟨hs, -⟩ | ⟨hut, -, -, hfr, -⟩
  · rw [hsp] at hs; cases hs
  rcases hend with ⟨hleaf, rfl, rfl, rfl, -, -⟩ | ⟨-, h', es, i, -, hl, -⟩
  · cases hut with
    | leaf _ r'' _ _ _ hr' => rw [hn] at hr'; cases hr'; exact hfr
    | branch _ r'' _ _ _ _ hr' _ hlf => rw [hn] at hr'; cases hr'; rw [hleaf] at hlf; cases hlf
  · exact fun id hid => hl.free id (List.mem_append_left _ hid)

/-- **A piece's premises at iteration `i`** (`pieceOne_wp`'s; see the module doc). -/
theorem pcInv_pre' {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX) (wi : WDb)
    (st : List FLStep) (x : Loc × node × List Inode)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st) (hx : xs[i]? = some x) :
    ∃ rl, Xi.node bl x.1 = some rl ∧ x.1 ∈ Xi.live ∧ wsLive rl.ws ∧
      (insLens rl.ins rl.ws → pcPre Xi wi bl x.1 rl) := by
  obtain ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, Es, Ds, ps, stl, hend, hlens, -, hsr, hfit, -, -,
    hents, -, -, hL⟩ := hI
  have hil : i < xs.length := (List.getElem?_eq_some_iff.1 hx).1
  obtain ⟨ws, hws⟩ : ∃ ws, wss[i]? = some ws :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact hil)⟩
  obtain ⟨rk, hrk, hlv, hsim⟩ := hL.todo i x ws (Nat.le_refl _) hx hws
  obtain ⟨-, -, hbk, hleaf, -, hpg, hpar, -, -⟩ := hsr.prec i x ws hx hws
  obtain ⟨hC, -, -, hG, -, -, -, -⟩ := hL.step
  have hwid : wi.wtxid = w'.wtxid := wtxid_of_C hC
  have hGi : spG Xi wi.wtxid (mapLen wi.ms) wi.fl := by rw [hwid]; exact hG
  obtain ⟨B, hB, hr⟩ := node_bsQ hrk
  have hfr := hG.2.2.2.1 bl B x.1 rk hB hr hlv
  have hdp := hG.2.2.1.1 bl B x.1 rk hB hr hlv
  have hnv : rk.nv.bucket' = x.2.1.bucket' ∧ rk.nv.pgid' = x.2.1.pgid' ∧
      rk.nv.parent' = x.2.1.parent' ∧ rk.nv.isLeaf' = x.2.1.isLeaf' := by
    rw [hsim.1, splitRec_nv]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hwsd : rk.ws.map wDat = ws.map wDat := by rw [hsim.2.2.1, splitRec_ws]
  have hlen : rk.ws.length = ws.length := by simpa using congrArg List.length hwsd
  have hinsl : rk.ins.length = x.2.2.length := by rw [hsim.2.2.2.1, splitRec_ins]
  obtain ⟨hpl1, hpl2⟩ := hsr.plen i x ws hx hws
  obtain ⟨hn', hlv', hun', -⟩ := spEnd_rec hpre hsp hend
  refine ⟨rk, hrk, hlv, hfr.1, fun hlr => ?_⟩
  -- the sizes: the piece's inodes are `x.2.2`, cut from `n`'s at the entries' lengths
  have hxl : insLens x.2.2 ws := by
    refine insLens_cut (xs.map (·.2.2)) wss (by simp [hsr.len]) ?_ ?_ i x.2.2 ws
      (by simp [hx]) hws
    · intro k a w' ha hw'
      obtain ⟨y, hy, rfl⟩ : ∃ y, xs[k]? = some y ∧ y.2.2 = a := by
        rw [List.getElem?_map] at ha
        cases e : xs[k]? with
        | none => rw [e] at ha; cases ha
        | some y => rw [e] at ha; exact ⟨y, rfl, Option.some.inj ha⟩
      exact (hsr.plen k y w' hy hw').1.symm
    · rw [hsr.ins, hsr.ws]; exact hlens
  have hsz : insSize rk.ins = insSize x.2.2 := by
    rw [insSize_ws rk.ins rk.ws hlr (by rw [hinsl, hlen, hpl1]),
      insSize_ws x.2.2 ws hxl hpl1.symm, sum_wSz_congr hwsd]
  have hbody : 16 + (pageBody true (wsMs rk.ws)).length = insSize rk.ins := by
    rw [body_ws, insSize_ws rk.ins rk.ws hlr (by rw [hinsl, hlen, hpl1])]
  have hE : ∀ it ∈ x.2.2, it.key'.len.toNat + it.value'.len.toNat ≤ bboltEntryMax := by
    intro it hit
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hit
    have hmw : m < ws.length := by rw [hpl1]; exact (List.getElem?_eq_some_iff.1 hm).1
    have hwm : ws[m]? = some ws[m] := List.getElem?_eq_getElem hmw
    obtain ⟨h1, h2⟩ := hxl m it _ hm hwm
    have hmem : ws[m] ∈ r'.ws := by
      have : ws ⊆ wss.flatten := fun a ha => List.mem_flatten.2 ⟨ws, List.mem_of_getElem? hws, ha⟩
      rw [hsr.ws] at this; exact this (List.getElem_mem hmw)
    have := (hun'.2.2.2.2.2.2.1 _ hmem).2.2
    omega
  obtain ⟨hb1, hb2⟩ := pieceFits_bounds 4096 x.2.2 (by omega) hE
    (hfit x (List.mem_of_getElem? hx)).1
  have hcnt : insSize rk.ins ≤ pcCount (insSize rk.ins) * 4096 := by unfold pcCount; omega
  refine ⟨hlv, hnv.1.trans hbk, ?_, spG_pcFreed hrk hlv hGi, ?_, ?_, by omega, ?_,
    by omega, by omega, ?_, ?_, by omega⟩
  · -- piece `0`'s page
    intro h0
    have hi0 : i = 0 := by
      cases e : decide (i = 0) with
      | true => exact of_decide_eq_true e
      | false =>
        rw [hnv.2.1, hpg, if_neg (of_decide_eq_false e)] at h0; exact absurd rfl h0
    subst hi0
    obtain ⟨rfl, rfl, -⟩ := hL.start rfl
    have hpg0 : rk.nv.pgid' = r'.nv.pgid' := by rw [hnv.2.1, hpg, if_pos rfl]; rfl
    rw [hpg0] at h0 ⊢
    have hv : Xi.v = X'.v := by rw [hsr.same.2.2.2, nilCh_v]
    have hpm : Xi.t.pm = X'.t.pm := by rw [hsr.same.2.2.1, nilCh_pm']
    have hfr0 := spEnd_free0 hpre hsp hend r'.nv.pgid'.toNat (by unfold ownF; rw [if_neg h0]; exact List.mem_singleton_self _)
    obtain ⟨pg, hpgv, h16, hid, hfl, h2, h62⟩ := hun'.2.2.2.2.2.2.2 h0
    have hwtx : wi.wtxid = w.wtxid := wtxid_of_C (spEnd_db hend).1
    refine ⟨by rw [hpm]; simpa using hfr0.1, by rw [hwid] at hGi; exact hGi.1, pg,
      by rw [hv]; exact hpgv, h16, hid, hfl, ?_⟩
    -- `canFree`: the page's slots owned (no free or pending id), not allocated by the writer
    have hsl := hL.slot
    simp only [pcOwn, List.drop_zero] at hsl
    have hown : ∀ s, r'.nv.pgid'.toNat ≤ s → s < r'.nv.pgid'.toNat + (1 + pageOverflow pg) →
        W64 (s : Int) ∉ wi.fl.allIds := by
      intro s h1 h2
      have hm : s ∈ ownSl X'.v r'.nv.pgid' := by
        unfold ownSl pgSlots; rw [if_neg h0]; simp [hpgv]; omega
      exact (hsl.2.1 s (List.mem_append_right _ (List.mem_append_left _
        (List.mem_append_left _ hm)))).2.2
    refine ⟨h2, by omega, ?_, ?_, ?_⟩
    · intro y hy hya
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
      have hk' := List.mem_range.1 hk
      apply hown (r'.nv.pgid'.toNat + k) (by omega) (by omega)
      have : W64 ((r'.nv.pgid'.toNat + k : Nat) : Int) = r'.nv.pgid' + W64 (k : Int) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofInt]
        omega
      rw [this]; exact hya
    · rw [hwtx]; simpa using hfr0.2
    · have := nodup_len_le hsl.2.2.1 hsl.2.2.2
      have := hGi.2.2.2.2.2.2.1
      omega
  · -- not empty (with a parent)
    intro hpn0
    rw [hlen]
    by_cases h2 : 2 ≤ xs.length
    · exact hpl2 h2
    · -- unsplit: the piece is `n`, its entries `r'`'s
      have hw1 : wss.length = 1 := by rw [hsr.len]; omega
      have hwf : ws = r'.ws := by
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hw1
        have e := hsr.ws
        rw [ha] at e hws
        have hi0 : i = 0 := by
          cases i with
          | zero => rfl
          | succ k => simp at hws
        subst hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hws
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at e
        rw [← hws, e]; rfl
      rcases hend with ⟨-, -, -, hr, -, -⟩ | ⟨-, h', es, i', -, hl, -⟩
      · -- an unsplit leaf with a parent: a child, not empty (`spCtx`)
        have hpl0 : pl ≠ null := by rw [hnv.2.2.1, hpar] at hpn0; exact hpn0
        have hrp : rn.nv.parent' ≠ null := by
          rcases hsr.par with ⟨-, -, e⟩ | ⟨-, h2', -⟩ | ⟨e, -⟩
          · exact absurd e hpl0
          · exact absurd h2' h2
          · rw [← hr]; exact e
        obtain ⟨-, -, hc⟩ := hpre
        rcases hc with ⟨hs, -⟩ | ⟨-, hctx, -⟩
        · rw [hsp] at hs; cases hs
        cases cs with
        | top => exact absurd hctx.1 hrp
        | child pl' rp j' plo phi => rw [hwf, hr]; exact hctx.2.2.2.2.2.2.2.2.2.2.2.2.2
      · rw [hwf]; have := hl.br.two; omega
  · rw [hinsl, hlen, hpl1]
  · -- `pageFits`
    refine ⟨by simp [wsMs]; omega, by omega, ?_⟩
    intro m hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    have := hdp.2.1 e he
    intro h; simp at h; rw [h] at this; simp at this
  · -- the allocated id: below the new mark, no entry's child page
    intro X1 w1 st1 X3 fl2 p id hf ha
    have hX1 : X1.t.mv = Xi.t.mv ∧ w1.fl.free = wi.fl.free := by
      rcases hf with ⟨-, rfl, rfl, -⟩ | ⟨pg, -, -, rfl, rfl, -⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨setNode_mv _ _ _ _, rfl⟩
    have hsl := hL.slot
    unfold pcOwn at hsl
    refine ⟨allocRes_id_lt_free ha (fun y hy => by
      rw [hX1.1]; rw [hX1.2] at hy; exact hsl.2.2.2 y (List.mem_append_left _ hy)), ?_⟩
    intro hlf e he
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 he
    have hmw : m < ws.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hm).1
    have hdat : wDat e = wDat ws[m] := by
      have := congrArg (fun l => l[m]?) hwsd
      simp only [List.getElem?_map, hm, List.getElem?_eq_getElem hmw, Option.map_some,
        Option.some.injEq] at this
      exact this
    have hpe : e.pgid = ws[m].pgid := congrArg (fun d => d.2.1) hdat
    obtain ⟨Sb, Eb, hD, -, hent⟩ := hents i ws hws
    have hleaf' : r'.nv.isLeaf' = false := by
      rw [← hlf, hnv.2.2.2, hleaf]; rfl
    have hft := (hent m ws[m] (List.getElem?_eq_getElem hmw)).2 hleaf'
    have hsD : ws[m].pgid.toNat ∈ Ds.getD i [] := by
      rw [hD]
      exact List.mem_flatMap.2 ⟨m, List.mem_range.2 hmw, fTree_root_slot hft⟩
    have hsDi : ws[m].pgid.toNat ∈ (Ds.drop i).flatten := by
      have hi' : i < Ds.length := by rw [hL.Dlen]; exact hil
      rw [List.drop_eq_getElem_cons hi', List.flatten_cons]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] at hsD
      exact List.mem_append_left _ hsD
    obtain ⟨hlt, h62, hnot⟩ := hsl.2.1 _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ hsDi)))
    have hne := allocRes_ne_slot ha (by rw [hX1.1]; exact hlt) h62
      (by rw [hX1.2]; exact fun hm => hnot (List.mem_append_left _ hm))
    intro hei
    apply hne
    rw [← hei, hpe]
  · -- the parent
    intro hpn
    rw [hnv.2.2.1, hpar] at hpn ⊢
    obtain ⟨rpi, hrpi, hplv, hpnot, hcap, hsort, -, -⟩ := hL.par hpn
    refine ⟨rpi, hrpi, hplv, fun he => hpnot ?_, hcap, hsort⟩
    rw [he]; exact List.mem_map.2 ⟨x, List.mem_of_getElem? hx, rfl⟩

end pcpre

end Spill

end bbolt
end EtcdGrove
end Perennial
