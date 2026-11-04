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

end keepok

end Spill

end bbolt
end EtcdGrove
end Perennial
