/-
`derefStep` keeps `wOK`, the node and bucket parts (U9b, `notes/bbolt-proof-plan.md`; pure): a
step changes a node's entries only by their sources (to persistent heap bytes) and its key
slice only by value, so every clause about data, keys, page ids, children and lookups' domains
is kept (`nodeClean_step`, `bktClean_step`, `bktKeys_step`, `nodePg_step`, `entryIn_step`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefRel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wok1
variable [GooseExts]

/-! ## Entries by data -/

theorem wDat_eq {a b : WEntry} (h : wDat a = wDat b) :
    a.flags = b.flags ∧ a.pgid = b.pgid ∧ a.key = b.key ∧ a.value = b.value := by
  simpa [wDat] using h

theorem mem_wDat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) {w' : WEntry}
    (hw : w' ∈ ws') : ∃ w ∈ ws, wDat w = wDat w' := by
  have : wDat w' ∈ ws.map wDat := h ▸ List.mem_map_of_mem hw
  exact List.mem_map.1 this

theorem getElem?_wDat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) {i : Nat}
    {w' : WEntry} (hw : ws'[i]? = some w') : ∃ w, ws[i]? = some w ∧ wDat w = wDat w' := by
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, hw, Option.map_some] at e
  cases hi : ws[i]? with
  | none => rw [hi] at e; simp at e
  | some w => rw [hi] at e; simp only [Option.map_some, Option.some.injEq] at e; exact ⟨w, rfl, e.symm⟩

/-! ## A node's step -/

theorem nodeStep_nvf {r r' : NRec} (h : nodeStep r r') :
    r'.nv.bucket' = r.nv.bucket' ∧ r'.nv.isLeaf' = r.nv.isLeaf' ∧
      r'.nv.unbalanced' = r.nv.unbalanced' ∧ r'.nv.spilled' = r.nv.spilled' ∧
      r'.nv.pgid' = r.nv.pgid' ∧ r'.nv.parent' = r.nv.parent' := by
  have e := (nodeStep_nv h).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [e]

theorem nodeStep_ins {r r' : NRec} (h : nodeStep r r') : r'.ins.length = r.ins.length := by
  rcases h with rfl | ⟨-, -, -, -, e, -⟩
  · rfl
  · exact e

theorem nodeStep_ksrc {r r' : NRec} (h : nodeStep r r') : r'.ksrc = r.ksrc ∨ r'.ksrc = Src.heap := by
  rcases h with rfl | ⟨-, -, -, -, -, -, -, -, e⟩
  · exact Or.inl rfl
  · exact Or.inr e

/-- An entry of the stepped node: an entry of the node by data, its sources kept or heap. -/
theorem nodeStep_mem {r r' : NRec} (h : nodeStep r r') {w' : WEntry} (hw : w' ∈ r'.ws) :
    ∃ w ∈ r.ws, wDat w = wDat w' ∧ (w'.ks = w.ks ∨ w'.ks = Src.heap) ∧
      (w'.vs = w.vs ∨ w'.vs = Src.heap) := by
  rcases h with rfl | hd
  · exact ⟨w', hw, rfl, Or.inl rfl, Or.inl rfl⟩
  · obtain ⟨w, hw0, e⟩ := mem_wDat hd.2.2.1 hw
    exact ⟨w, hw0, e, Or.inr (hd.2.2.2.1 w' hw).1, Or.inr (hd.2.2.2.1 w' hw).2⟩

theorem nodeStep_mem' {r r' : NRec} (h : nodeStep r r') {w : WEntry} (hw : w ∈ r.ws) :
    ∃ w' ∈ r'.ws, wDat w' = wDat w :=
  mem_wDat (nodeStep_nv h).2.2.2.2.2.symm hw

theorem nodeStep_get {r r' : NRec} (h : nodeStep r r') {i : Nat} {w' : WEntry}
    (hw : r'.ws[i]? = some w') : ∃ w, r.ws[i]? = some w ∧ wDat w = wDat w' :=
  getElem?_wDat (nodeStep_nv h).2.2.2.2.2 hw

theorem nodeStep_get' {r r' : NRec} (h : nodeStep r r') {i : Nat} {w : WEntry}
    (hw : r.ws[i]? = some w) : ∃ w', r'.ws[i]? = some w' ∧ wDat w' = wDat w :=
  getElem?_wDat (nodeStep_nv h).2.2.2.2.2.symm hw

theorem nodeStep_pgids {r r' : NRec} (h : nodeStep r r') :
    r'.ws.map WEntry.pgid = r.ws.map WEntry.pgid := by
  have h' := congrArg (List.map fun d : w32 × w64 × List w8 × List w8 => d.2.1)
    (nodeStep_nv h).2.2.2.2.2
  simpa [List.map_map, wDat, Function.comp_def] using h'

theorem wKey_eq {ws ws' : List WEntry} (h : ws'.map WEntry.key = ws.map WEntry.key) (i : Nat) :
    wKey ws' i = wKey ws i := by
  unfold wKey
  rw [← List.getElem?_map, ← List.getElem?_map, h]

theorem nodeStep_wKey {r r' : NRec} (h : nodeStep r r') (i : Nat) : wKey r'.ws i = wKey r.ws i :=
  wKey_eq (nodeStep_keys h) i

theorem nodeStep_wsSorted {r r' : NRec} (h : nodeStep r r') (hs : wsSorted r.ws) :
    wsSorted r'.ws := by
  intro i j hij hj
  rw [nodeStep_wKey h, nodeStep_wKey h]
  exact hs i j hij (by rw [nodeStep_key_len h] at hj; exact hj)

theorem nodeStep_wsLive {r r' : NRec} (h : nodeStep r r') (hs : wsLive r.ws) : wsLive r'.ws := by
  intro w' hw'
  obtain ⟨w, hw, -, hk, hv⟩ := nodeStep_mem h hw'
  obtain ⟨h1, h2⟩ := hs w hw
  refine ⟨?_, ?_⟩
  · rcases hk with e | e <;> rw [e]
    · exact h1
    · simp
  · rcases hv with e | e <;> rw [e]
    · exact h2
    · simp

theorem wEntryBnd_step {r r' : NRec} (h : nodeStep r r') (b : Option (List w8) × Option (List w8))
    (i : Nat) : wEntryBnd b r'.ws i = wEntryBnd b r.ws i := by
  unfold wEntryBnd; rw [nodeStep_keys h]

/-! ## A bucket's step -/

theorem bktStep_fwd {B B' : BRec} (h : bktStep B B') {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) : ∃ r', B'.ns !! l = some r' ∧ nodeStep r r' :=
  optRel_some_l (hr ▸ h.2 l)

theorem bktStep_bwd {B B' : BRec} (h : bktStep B B') {l : Loc} {r' : NRec}
    (hr : B'.ns !! l = some r') : ∃ r, B.ns !! l = some r ∧ nodeStep r r' :=
  optRel_some_r (hr ▸ h.2 l)

theorem bktStep_ns_empty {B B' : BRec} (h : bktStep B B') (he : B.ns = ∅) : B'.ns = ∅ := by
  apply GMap.map_eq
  intro l
  have := h.2 l
  rw [he, GMap.lookup_empty] at this
  rw [optRel_none_l this, GMap.lookup_empty]

theorem pagePosAt_step {B B' : BRec} (h : bktStep B B') : pagePosAt B' = pagePosAt B := by
  have hnm := (bktStep_fields h).2.2.1
  funext l i c
  apply propext
  unfold pagePosAt
  rw [hnm]
  constructor
  · rintro ⟨r', w', hr', hl, hw', hp, hn⟩
    obtain ⟨r, hr, hs⟩ := bktStep_bwd h hr'
    obtain ⟨w, hw, e⟩ := nodeStep_get hs hw'
    refine ⟨r, w, hr, by rw [← (nodeStep_nvf hs).2.1]; exact hl, hw, ?_, hn⟩
    rw [(wDat_eq e).2.1]; exact hp
  · rintro ⟨r, w, hr, hl, hw, hp, hn⟩
    obtain ⟨r', hr', hs⟩ := bktStep_fwd h hr
    obtain ⟨w', hw', e⟩ := nodeStep_get' hs hw
    refine ⟨r', w', hr', by rw [(nodeStep_nvf hs).2.1]; exact hl, hw', ?_, hn⟩
    rw [(wDat_eq e).2.1]; exact hp

theorem posDisjoint_step {B B' : BRec} (h : bktStep B B') (v : View) :
    posDisjoint v B' = posDisjoint v B := by
  unfold posDisjoint; rw [pagePosAt_step h]

theorem posNodeFree_step {B B' : BRec} (h : bktStep B B') (v : View) :
    posNodeFree v B' = posNodeFree v B := by
  unfold posNodeFree; rw [pagePosAt_step h, (bktStep_fields h).2.2.1]

theorem posRoot_step {B B' : BRec} (h : bktStep B B') : posRoot B' = posRoot B := by
  funext c
  unfold posRoot; rw [pagePosAt_step h, (bktStep_fields h).1, (bktStep_fields h).2.1]

/-! ## The clean invariant -/

theorem nodeClean_step {v : View} {hwm : Nat} {bl : Loc} {B B' : BRec} {l : Loc} {r r' : NRec}
    (h : bktStep B B') (hs : nodeStep r r') (hc : nodeClean v hwm bl B l r) :
    nodeClean v hwm bl B' l r' := by
  obtain ⟨hbv, hib, hnm, hbm, -, -, -⟩ := bktStep_fields h
  obtain ⟨fb, fl, -, fsp, fpg, fpa⟩ := nodeStep_nvf hs
  obtain ⟨-, hcs, hkey, hcap, hnil, -⟩ := nodeStep_nv hs
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hc
  unfold nodeClean
  rw [hbv, hib, hnm, hbm, fb, fl, fsp, fpg, fpa, hcs, hkey, hcap, nodeStep_ins hs,
    nodeStep_key_len hs]
  refine ⟨c1, c2, c3, nodeStep_wsSorted hs c4, ?_, nodeStep_wsLive hs c6, c7, c8, c9, c10, ?_,
    ?_, ?_, c14, ?_, c16, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, e, -⟩ := nodeStep_mem hs hw'
    rw [← (wDat_eq e).2.2.1]; exact c5 w hw
  · rw [hnil]
    rcases c11 with e | ⟨h1, h2⟩
    · exact Or.inl e
    · refine Or.inr ⟨h1, ?_⟩
      rcases nodeStep_ksrc hs with e | e <;> rw [e]
      · exact h2
      · simp
  · intro hl w' hw' hf
    obtain ⟨w, hw, e, -, hv⟩ := nodeStep_mem hs hw'
    obtain ⟨ef, -, ek, ev⟩ := wDat_eq e
    rw [← ef] at hf
    obtain ⟨d1, d2⟩ := c12 hl w hw hf
    refine ⟨by rw [← ek, ← ev]; exact d1, ?_⟩
    rcases hv with e | e <;> rw [e]
    · exact d2
    · exact Or.inr rfl
  · intro hl
    obtain ⟨d1, d2, d3⟩ := c13 hl
    refine ⟨d1, by rw [nodeStep_pgids hs]; exact d2, ?_⟩
    intro w' hw'
    obtain ⟨w, hw, e, -⟩ := nodeStep_mem hs hw'
    rw [← (wDat_eq e).2.1]
    obtain ⟨e1, e2, e3⟩ := d3 w hw
    refine ⟨e1, ?_, e3⟩
    intro l' hl'
    obtain ⟨rc, hrc, hp⟩ := e2 l' hl'
    obtain ⟨rc', hrc', hsc⟩ := bktStep_fwd h hrc
    exact ⟨rc', hrc', by rw [(nodeStep_nvf hsc).2.2.2.2.2]; exact hp⟩
  · intro hp
    obtain ⟨rp, hrp, hpl, hpc, w, hw, hwp⟩ := c15 hp
    obtain ⟨rp', hrp', hsp⟩ := bktStep_fwd h hrp
    obtain ⟨w', hw', e⟩ := nodeStep_mem' hsp hw
    refine ⟨rp', hrp', by rw [(nodeStep_nvf hsp).2.1]; exact hpl,
      by rw [(nodeStep_nv hsp).2.1]; exact hpc, w', hw', ?_⟩
    rw [(wDat_eq e).2.1]; exact hwp
  · intro c hc
    obtain ⟨rc, hrc, hp⟩ := c17 c hc
    obtain ⟨rc', hrc', hsc⟩ := bktStep_fwd h hrc
    exact ⟨rc', hrc', by rw [(nodeStep_nvf hsc).2.2.2.2.2]; exact hp⟩

theorem bktClean_step {v : View} {hwm : Nat} {bl : Loc} {B B' : BRec} (h : bktStep B B')
    (hc : bktClean v hwm bl B) : bktClean v hwm bl B' := by
  obtain ⟨hbv, hib, hnm, hbm, hipg, hisrc, hpst⟩ := bktStep_fields h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  unfold bktClean
  rw [posDisjoint_step h, posNodeFree_step h, hbv, hib, hnm, hipg, hisrc, hpst]
  refine ⟨c1, c2, ?_, c4, ?_, c6, ?_, ?_, c9, c10.1, fun nm c hc => c10.2 nm c (by rw [← hbm]; exact hc)⟩
  · intro hn
    obtain ⟨d1, d2⟩ := c3 hn
    exact ⟨bktStep_ns_empty h d1, d2⟩
  · intro c l hl
    obtain ⟨d1, r, hr, hp⟩ := c5 c l hl
    obtain ⟨r', hr', hs⟩ := bktStep_fwd h hr
    exact ⟨d1, r', hr', by rw [(nodeStep_nvf hs).2.2.2.2.1]; exact hp⟩
  · intro hr0 l r' hr'
    obtain ⟨r, hr, hs⟩ := bktStep_bwd h hr'
    rw [(nodeStep_nvf hs).2.1]; exact c7 hr0 l r hr
  · intro l r' hr'
    obtain ⟨r, hr, hs⟩ := bktStep_bwd h hr'
    exact nodeClean_step h hs (c8 l r hr)

/-! ## Keys -/

theorem nodeKeys_step {v : View} {B B' : BRec} {bnd : Loc → Option (List w8) × Option (List w8)}
    {l : Loc} {r r' : NRec} (h : bktStep B B') (hs : nodeStep r r') (hk : nodeKeys v B bnd l r) :
    nodeKeys v B' bnd l r' := by
  obtain ⟨-, -, hnm, hbm, -, -, -⟩ := bktStep_fields h
  obtain ⟨-, fl, fu, -, fpg, fpa⟩ := nodeStep_nvf hs
  obtain ⟨-, -, hkey, -, hnil, -⟩ := nodeStep_nv hs
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  unfold nodeKeys opened
  rw [hnm, hbm, fl, fu, fpg, fpa, hkey, nodeStep_key_len hs]
  refine ⟨?_, k2, ?_, ?_, k5, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, e, -⟩ := nodeStep_mem hs hw'
    rw [← (wDat_eq e).2.2.1]; exact k1 w hw
  · intro hp
    obtain ⟨d1, rp, i, w, hrp, hw, hwp, hwk, hb⟩ := k3 hp
    obtain ⟨rp', hrp', hsp⟩ := bktStep_fwd h hrp
    obtain ⟨w', hw', e⟩ := nodeStep_get' hsp hw
    obtain ⟨-, ep, ek, -⟩ := wDat_eq e
    refine ⟨fun e => d1 (hnil.1 e), rp', i, w', hrp', hw', by rw [ep]; exact hwp,
      by rw [ek]; exact hwk, ?_⟩
    rw [wEntryBnd_step hsp]; exact hb
  · intro hl
    obtain ⟨d1, kind, d2⟩ := k4 hl
    refine ⟨d1, kind, ?_⟩
    intro i w' hw'
    obtain ⟨w, hw, e⟩ := nodeStep_get hs hw'
    obtain ⟨-, ep, ek, -⟩ := wDat_eq e
    obtain ⟨e1, e2⟩ := d2 i w hw
    rw [← ep, ← ek, wEntryBnd_step hs]
    refine ⟨?_, e2⟩
    intro l' hl'
    obtain ⟨rc, hrc, hp⟩ := e1 l' hl'
    obtain ⟨rc', hrc', hsc⟩ := bktStep_fwd h hrc
    exact ⟨rc', hrc', by rw [(nodeStep_nvf hsc).2.1]; exact hp⟩
  · intro hl w' hw' hf
    obtain ⟨w, hw, e, -⟩ := nodeStep_mem hs hw'
    obtain ⟨ef, -, ek, ev⟩ := wDat_eq e
    rw [← ef] at hf
    rw [← ek, ← ev]
    exact k6 hl w hw hf

theorem bktKeys_step {v : View} {B B' : BRec} (h : bktStep B B') (hk : bktKeys v B) :
    bktKeys v B' := by
  obtain ⟨bnd, k1, k2, k3⟩ := hk
  obtain ⟨hbv, hib, -, -, -, -, -⟩ := bktStep_fields h
  refine ⟨bnd, ?_, ?_, ?_⟩
  · rw [hbv, hib]; exact k1
  · intro r' hr'
    rw [hbv] at hr'
    obtain ⟨r, hr, hs⟩ := bktStep_bwd h hr'
    rw [(nodeStep_nvf hs).2.2.2.2.2]; exact k2 r hr
  · intro l r' hr'
    obtain ⟨r, hr, hs⟩ := bktStep_bwd h hr'
    exact nodeKeys_step h hs (k3 l r hr)

/-! ## Nested buckets and nodes' pages -/

theorem entryIn_step {vw : View} {B B' : BRec} (h : bktStep B B') {k v : List w8}
    (he : entryIn vw B k v) : entryIn vw B' k v := by
  unfold entryIn
  rw [posRoot_step h]
  rcases he with ⟨l, r, w, hr, hl, hw, hk, hf, hv⟩ | he
  · obtain ⟨r', hr', hs⟩ := bktStep_fwd h hr
    obtain ⟨w', hw', e⟩ := nodeStep_mem' hs hw
    obtain ⟨ef, -, ek, ev⟩ := wDat_eq e
    exact Or.inl ⟨l, r', w', hr', by rw [(nodeStep_nvf hs).2.1]; exact hl, hw',
      by rw [ek]; exact hk, by rw [ef]; exact hf, by rw [ev]; exact hv⟩
  · exact Or.inr he

theorem nodePg_step {v : View} {root : w64} {r r' : NRec} (hs : nodeStep r r')
    (hp : nodePg v root r) : nodePg v root r' := by
  obtain ⟨-, fl, -, -, fpg, -⟩ := nodeStep_nvf hs
  obtain ⟨p1, p2⟩ := hp
  unfold nodePg
  rw [fl, fpg, (nodeStep_nv hs).2.2.1, nodeStep_wKey hs, nodeStep_key_len hs]
  refine ⟨?_, ?_⟩
  · intro hl
    obtain ⟨d1, d2⟩ := p1 hl
    refine ⟨?_, d2⟩
    intro w' hw'
    obtain ⟨w, hw, e, -⟩ := nodeStep_mem hs hw'
    rw [← (wDat_eq e).2.1]; exact d1 w hw
  · intro hl
    obtain ⟨d1, pg, d2, d3, d4, d5⟩ := p2 hl
    refine ⟨d1, pg, d2, d3, d4, ?_⟩
    intro i w' hw'
    obtain ⟨w, hw, e⟩ := nodeStep_get hs hw'
    rw [← (wDat_eq e).2.1]; exact d5 i w hw

end wok1

end bbolt
end EtcdGrove
end Perennial
