/-
`Bucket.spill`'s root loop (U9x, `notes/bbolt-proof-plan.md`): **a kept bucket stays searchable**
(`bktLocalOK_kept`): its nodes clean (`nodeClean_kept`: the data, page ids, children and parents are
the nodes', the sources `liveFresh`'s and `leafVs`'), its keys (`bktKeys_kept`) and its leaves'
page ids (`txPgLeaf`), over a view with the same pages and a mark not lower.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureKeep

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section keepok
variable [GooseExts]

theorem nodeSim_unbal {r r' : NRec} (h : nodeSim r r') : r'.nv.unbalanced' = r.nv.unbalanced' := by
  rw [h.1]

theorem fwd_kept {B B' : BRec} (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) {l : Loc}
    {r : NRec} (hr : B.ns !! l = some r) : ∃ r', B'.ns !! l = some r' ∧ nodeSim r r' := by
  have h := hns l; rw [hr] at h; exact optRel_some_l h

theorem bwd_kept {B B' : BRec} (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) {l : Loc}
    {r' : NRec} (hr : B'.ns !! l = some r') : ∃ r, B.ns !! l = some r ∧ nodeSim r r' := by
  have h := hns l; rw [hr] at h; exact optRel_some_r h

theorem mem_of_dat' {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) {w : WEntry}
    (hw : w ∈ ws) : ∃ w' ∈ ws', wDat w' = wDat w := by
  obtain ⟨w', hw', e⟩ := mem_of_dat h.symm hw
  exact ⟨w', hw', e.symm⟩

theorem get_of_dat' {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) {i : Nat}
    {w : WEntry} (hw : ws[i]? = some w) : ∃ w', ws'[i]? = some w' ∧ wDat w' = wDat w := by
  obtain ⟨w', hw', e⟩ := get_of_dat h.symm hw
  exact ⟨w', hw', e.symm⟩

theorem keys_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    ws'.map WEntry.key = ws.map WEntry.key := by
  have := congrArg (List.map fun d : w32 × w64 × List w8 × List w8 => d.2.2.1) h
  simpa [List.map_map, wDat, Function.comp_def] using this

theorem wEntryBnd_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat)
    (b : Option (List w8) × Option (List w8)) (i : Nat) : wEntryBnd b ws' i = wEntryBnd b ws i := by
  unfold wEntryBnd; rw [keys_of_dat h]

/-- **A node of a kept bucket stays clean** (its sources: `liveFresh`'s, `leafVs`). -/
theorem nodeClean_kept {v v' : View} {hwm hwm' : Nat} {bl : Loc} {B B' : BRec} (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (hv : v'.pages = v.pages)
    (hh : hwm ≤ hwm') {l : Loc} {r r' : NRec} (hsim : nodeSim r r') (hc : nodeClean v hwm bl B l r)
    (hlive : wsLive r'.ws) (hks : r'.nv.key' ≠ slice.nil → r'.ksrc ≠ Src.stale)
    (hvs : leafVs r') : nodeClean v' hwm' bl B' l r' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hc
  have hd := hsim.2.2.1
  refine ⟨by rw [nodeSim_bucket hsim]; exact c1, by rw [hsim.2.2.2.2.2.2]; exact c2,
    by rw [hsim.2.2.2.1, length_of_dat hd]; exact c3, wsSorted_of_dat hd c4, ?_, hlive,
    by rw [nodeSim_spilled hsim]; exact c7, by rw [nodeSim_pgid hsim, hs.2.2.1]; exact c8,
    by rw [nodeSim_pgid hsim, hs.2.1]; exact c9, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hsim.2.2.2.2.1]; exact c16, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, e⟩ := mem_of_dat hd hw'
    rw [wDat_key e]; exact c5 w hw
  · intro h0; rw [hs.2.1] at h0
    rw [nodeSim_pgid hsim, hv]; exact treeWF_hwm hh (c10 h0)
  · by_cases hk : r'.nv.key' = slice.nil
    · exact Or.inl hk
    · refine Or.inr ⟨?_, hks hk⟩
      rw [hsim.2.2.2.2.2.1]
      rcases c11 with e | e
      · exact absurd (hsim.2.1.2 e) hk
      · exact e.1
  · intro hl w' hw' hf
    obtain ⟨w, hw, e⟩ := mem_of_dat hd hw'
    have hl0 : r.nv.isLeaf' = true := by rw [← nodeSim_isLeaf hsim]; exact hl
    obtain ⟨d1, -⟩ := c12 hl0 w hw (by rw [← wDat_flags e]; exact hf)
    refine ⟨?_, ?_⟩
    · intro hbm; rw [hs.2.2.2.1, wDat_key e] at hbm
      rw [hv, wDat_value e]; exact bvalOK_hwm hh (d1 hbm)
    · exact hvs hl w' hw' hf
  · intro hl
    have hl0 : r.nv.isLeaf' = false := by rw [← nodeSim_isLeaf hsim]; exact hl
    obtain ⟨d1, d2, d3⟩ := c13 hl0
    refine ⟨by rw [length_of_dat hd]; exact d1, by rw [map_pgid_of_wDat hd]; exact d2, ?_⟩
    intro w' hw'
    obtain ⟨w, hw, e⟩ := mem_of_dat hd hw'
    obtain ⟨e1, e2, e3⟩ := d3 w hw
    rw [wDat_pgid e]
    refine ⟨by omega, ?_, ?_⟩
    · intro l' hl'
      rw [hs.2.2.1] at hl'
      obtain ⟨rc, hrc, hp⟩ := e2 l' hl'
      obtain ⟨rc', hrc', hsc⟩ := fwd_kept hns hrc
      exact ⟨rc', hrc', by rw [nodeSim_parent hsc]; exact hp⟩
    · intro hn; rw [hs.2.2.1] at hn
      rw [hv]; exact treeWF_hwm hh (e3 hn)
  · intro hp; rw [nodeSim_parent hsim] at hp
    rw [hs.1]; exact c14 hp
  · intro hp; rw [nodeSim_parent hsim] at hp
    obtain ⟨rp, hrp, hpl, hpc, w, hw, hwp⟩ := c15 hp
    obtain ⟨rp', hrp', hsp⟩ := fwd_kept hns hrp
    obtain ⟨w', hw', e⟩ := mem_of_dat' hsp.2.2.1 hw
    refine ⟨rp', by rw [nodeSim_parent hsim]; exact hrp', by rw [nodeSim_isLeaf hsp]; exact hpl,
      by rw [hsp.2.2.2.2.1]; exact hpc, w', hw', ?_⟩
    rw [wDat_pgid e, nodeSim_pgid hsim]; exact hwp
  · intro c hc
    rw [hsim.2.2.2.2.1] at hc
    obtain ⟨rc, hrc, hp⟩ := c17 c hc
    obtain ⟨rc', hrc', hsc⟩ := fwd_kept hns hrc
    exact ⟨rc', hrc', by rw [nodeSim_parent hsc]; exact hp⟩

/-- **A kept bucket stays clean.** -/
theorem bktClean_kept {v v' : View} {hwm hwm' : Nat} {bl : Loc} {B B' : BRec} (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (hv : v'.pages = v.pages)
    (hh : hwm ≤ hwm') (hc : bktClean v hwm bl B)
    (hinl : B.ib.root' = W64 0 → B.bv.rootNode' = null → B'.isrc = B.isrc ∧ B'.pst = B.pst)
    (hnode : ∀ l r r', B.ns !! l = some r → B'.ns !! l = some r' → nodeSim r r' →
      wsLive r'.ws ∧ (r'.nv.key' ≠ slice.nil → r'.ksrc ≠ Src.stale) ∧ leafVs r') :
    bktClean v' hwm' bl B' := by
  have hpos := pagePosAt_kept hs hns
  obtain ⟨hbv, hib, hnm, hbm, hipg⟩ := hs
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hbm]; exact c11⟩
  · intro h0 hn
    rw [hib] at h0; rw [hbv] at hn
    obtain ⟨e1, e2⟩ := hinl h0 hn
    rw [hbv, e1, e2, hipg]; exact c1 h0 hn
  · intro h0; rw [hib] at h0; rw [hib, hbv, hv]
    obtain ⟨d1, d2⟩ := c2 h0
    exact ⟨by omega, fun hn => treeWF_hwm hh (d2 hn)⟩
  · intro h0
    rw [hbv] at h0
    obtain ⟨hns0, hnm0⟩ := c3 h0
    refine ⟨?_, by rw [hnm]; exact hnm0⟩
    apply GMap.ext; intro y
    cases hy : B'.ns !! y with
    | none => show none = (∅ : GMap Loc NRec) !! y; simp
    | some ry' =>
      obtain ⟨ry, hry, -⟩ := bwd_kept hns hy
      rw [hns0] at hry; simp at hry
  · rw [hbv, hnm, hib]; exact c4
  · intro c l hl
    rw [hnm] at hl
    obtain ⟨hnn, r, hr, hp⟩ := c5 c l hl
    obtain ⟨r', hr', e⟩ := fwd_kept hns hr
    exact ⟨hnn, r', hr', by rw [nodeSim_pgid e]; exact hp⟩
  · rw [hib, hbv]; exact c6
  · intro h0 l r' hr'
    rw [hib] at h0
    obtain ⟨r, hr, e⟩ := bwd_kept hns hr'
    rw [nodeSim_isLeaf e]; exact c7 h0 l r hr
  · intro l r' hr'
    obtain ⟨r, hr, e⟩ := bwd_kept hns hr'
    obtain ⟨n1, n2, n3⟩ := hnode l r r' hr hr' e
    exact nodeClean_kept ⟨hbv, hib, hnm, hbm, hipg⟩ hns hv hh e (c8 l r hr) n1 n2 n3
  · intro l1 i1 a1 l2 i2 a2 h1 h2 hne d hd
    rw [hv] at hd ⊢
    exact c9 l1 i1 a1 l2 i2 a2 ((hpos _ _ _).1 h1) ((hpos _ _ _).1 h2) hne d hd
  · intro l i c hp d hd
    rw [hv] at hd; rw [hnm]
    exact c10 l i c ((hpos _ _ _).1 hp) d hd

/-- **A node's keys in a kept bucket** (the same bounds). -/
theorem nodeKeys_kept {v v' : View} {B B' : BRec} (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (hv : v'.pages = v.pages)
    {bnd : Loc → Option (List w8) × Option (List w8)} {l : Loc} {r r' : NRec}
    (hsim : nodeSim r r') (hk : nodeKeys v B bnd l r) : nodeKeys v' B' bnd l r' := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  have hd := hsim.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, e⟩ := mem_of_dat hd hw'
    rw [wDat_key e]; exact k1 w hw
  · intro hp; rw [nodeSim_parent hsim] at hp; exact k2 hp
  · intro hp; rw [nodeSim_parent hsim] at hp ⊢
    obtain ⟨d1, rp, i, w, hrp, hw, hwp, hwk, hb⟩ := k3 hp
    obtain ⟨rp', hrp', hsp⟩ := fwd_kept hns hrp
    obtain ⟨w', hw', e⟩ := get_of_dat' hsp.2.2.1 hw
    refine ⟨fun h0 => d1 (hsim.2.1.1 h0), rp', i, w', hrp', hw', ?_, ?_, ?_⟩
    · rw [wDat_pgid e, nodeSim_pgid hsim]; exact hwp
    · rw [wDat_key e, hsim.2.2.2.2.2.1]; exact hwk
    · rw [wEntryBnd_of_dat hsp.2.2.1]; exact hb
  · intro hl
    rw [nodeSim_isLeaf hsim] at hl
    obtain ⟨d1, kind, d2⟩ := k4 hl
    refine ⟨by rw [length_of_dat hd]; exact d1, kind, ?_⟩
    intro i w' hw'
    obtain ⟨w, hw, e⟩ := get_of_dat hd hw'
    obtain ⟨e1, e2⟩ := d2 i w hw
    rw [wDat_pgid e, wDat_key e, wEntryBnd_of_dat hd, hs.2.2.1, hv]
    refine ⟨?_, e2⟩
    intro l' hl'
    obtain ⟨rc, hrc, hp⟩ := e1 l' hl'
    obtain ⟨rc', hrc', hsc⟩ := fwd_kept hns hrc
    exact ⟨rc', hrc', by rw [nodeSim_isLeaf hsc]; exact hp⟩
  · intro hl hu hp
    rw [nodeSim_isLeaf hsim] at hl; rw [nodeSim_unbal hsim] at hu
    rw [nodeSim_parent hsim] at hp
    rw [length_of_dat hd]; exact k5 hl hu hp
  · intro hl w' hw' hf hr ho
    obtain ⟨w, hw, e⟩ := mem_of_dat hd hw'
    rw [nodeSim_isLeaf hsim] at hl
    rw [wDat_flags e] at hf; rw [wDat_value e] at hr ⊢
    rw [wDat_key e] at ho
    rw [hv]
    exact k6 hl w hw hf hr (by unfold opened at ho ⊢; rw [hs.2.2.2.1] at ho; exact ho)

theorem bktKeys_kept {v v' : View} {B B' : BRec} (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (hv : v'.pages = v.pages)
    (hk : bktKeys v B) : bktKeys v' B' := by
  obtain ⟨bnd, k1, k2, k3⟩ := hk
  refine ⟨bnd, ?_, ?_, ?_⟩
  · intro hn h0; rw [hs.1] at hn; rw [hs.2.1] at h0 ⊢; rw [hv]; exact k1 hn h0
  · intro r' hr'
    rw [hs.1] at hr'
    obtain ⟨r, hr, e⟩ := bwd_kept hns hr'
    rw [nodeSim_parent e]; exact k2 r hr
  · intro l r' hr'
    obtain ⟨r, hr, e⟩ := bwd_kept hns hr'
    exact nodeKeys_kept hs hns hv e (k3 l r hr)

theorem txPgLeaf_kept {B B' : BRec} {bl : Loc}
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) (h : txPgLeaf (GMap.singleton bl B)) :
    txPgLeaf (GMap.singleton bl B') := by
  intro bl' B1 hB1 l r' hr' hl w' hw'
  simp at hB1
  obtain ⟨rfl, rfl⟩ := hB1
  obtain ⟨r, hr, e⟩ := bwd_kept hns hr'
  obtain ⟨w, hw, e'⟩ := mem_of_dat e.2.2.1 hw'
  rw [wDat_pgid e']
  exact h bl B (by simp) l r hr (by rw [← nodeSim_isLeaf e]; exact hl) w hw

/-- **A kept bucket stays searchable** (see the module doc). -/
theorem bktLocalOK_kept {X X' : WX} {bl : Loc} (hloc : bktLocalOK X bl) (hkept : bktKept X X' bl)
    (hv : X'.v.pages = X.v.pages) (hvw : viewWF X'.v)
    (hh : X.t.mv.pgid'.toNat ≤ X'.t.mv.pgid'.toNat) (hlB : bl ∈ X'.liveB)
    (hreach : liveReach X) (hp' : derefPre X') (hf' : liveFresh X')
    (hinl : ∀ B B', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' →
      B.ib.root' = W64 0 → B.bv.rootNode' = null → B'.isrc = B.isrc ∧ B'.pst = B.pst)
    (hvs : ∀ B B' l r r', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' → B.ns !! l = some r →
      B'.ns !! l = some r' → l ∈ X.live → leafVs r → leafVs r') :
    bktLocalOK X' bl := by
  obtain ⟨-, B, hB, hcl, hk, hpl, hlive, -⟩ := hloc
  obtain ⟨B', hB', hs, hns⟩ := hkept B hB
  have hl' : ∀ l r', B'.ns !! l = some r' → l ∈ X'.live := by
    intro l r' hr'
    obtain ⟨r, hr, -⟩ := bwd_kept hns hr'
    exact live_kept hB hB' hs hns hreach hp' hlB hr (hlive l r hr)
  refine ⟨hlB, B', hB', bktClean_kept hs hns hv hh hcl (hinl B B' hB hB') ?_,
    bktKeys_kept hs hns hv hk, txPgLeaf_kept hns hpl, hl', hvw⟩
  intro l r r' hr hr' e
  obtain ⟨f1, f2⟩ := hf' bl B' l r' hB' hr' (hl' l r' hr')
  refine ⟨f1, f2, hvs B B' l r r' hB hB' hr hr' (hlive l r hr) ?_⟩
  intro hlf w hw hf
  exact ((hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.2.2.2.1 hlf w hw hf).2

end keepok

end Spill

end bbolt
end EtcdGrove
end Perennial
