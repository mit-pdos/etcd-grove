/- Lean-first (no Rocq counterpart).

# The full layout's static relation across a step (unit `locks`, session 7; `notes/wal-units/locks.md`)

Pure. The invariant states each WAL's crash condition on the layout as of the WAL directory's last sync,
`unpurge lay.pg lay` (the segments removed since put back in front), with its static relation for the WAL
with `cut` at its first segment (`walFullD`; `WalFullOk`, `Cut.lean`). A step changes the WAL (`d` to `d'`)
and its named segments (`lay` to `lay'`) but not the removed ones (`pg`) nor `first`: `walAbsD_full_step`
rebuilds the full layout's relation from the old one (for the removed segments: frozen, their streams and
the history before them unchanged) and the new layout's (for the named ones).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

theorem getElem?_pg_left {pg segs : List SegG} {k : Nat} (hk : k < pg.length) :
    (pg ++ segs)[k]? = pg[k]? := List.getElem?_append_left hk

theorem getElem?_pg_right {pg segs : List SegG} {k : Nat} (hk : pg.length ≤ k) :
    (pg ++ segs)[k]? = segs[k - pg.length]? := List.getElem?_append_right hk

theorem drop_len_append {α : Type} (pg l : List α) (q : Nat) : (pg ++ l).drop (pg.length + q) = l.drop q := by
  rw [List.drop_append]; simp

/-- **`CrashTo` of the layout gives it of the layout with `pg` put back** (a crash that keeps none of the
removed segments). -/
theorem crashTo_unpurge {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (pg : List SegG) (hf : pg.length ≤ lay.first)
    (h : CrashTo C Mr d lay m' fo) : CrashTo C Mr d (unpurge pg lay) m' fo := by
  rcases h with h | ⟨q, I, hent, hq, hinos, hI, hlen, hst, hk, hlast⟩
  · exact Or.inl h
  refine Or.inr ⟨pg.length + q, I, hent, ?_, ?_, hI, hlen, ?_, ?_, ?_⟩
  · simp only [unpurge, List.length_append]; omega
  · simp only [unpurge]; rw [drop_len_append]; exact hinos
  · simp only [unpurge]
    have e : lay.first - pg.length + (pg.length + q) = lay.first + q := by omega
    rw [e]; exact hst
  · intro k g hg hlt
    simp only [unpurge] at hg hlt ⊢
    rw [drop_len_append] at hg
    have e : lay.first - pg.length + (pg.length + q) + k = lay.first + q + k := by omega
    rw [e] at hlt ⊢
    exact hk k g hg hlt
  · intro g hg
    have hne : lay.segs ≠ [] := by intro e; rw [e] at hq; simp at hq
    simp only [unpurge] at hg
    have e : (pg ++ lay.segs).getLast? = lay.segs.getLast? := by
      rw [List.getLast?_append]
      cases h' : lay.segs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h') hne
      | some _ => simp
    rw [e] at hg
    exact hlast g hg

/-- **`CrashTo` does not read the read position**: the crash condition of the full layout can be stated
for the WAL with `cut` at the full layout's first segment (where `WalAbsD` puts it). -/
theorem crashTo_cut_iff {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {F : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (c : Nat) :
    CrashTo C Mr { d with cut := c } F m' fo ↔ CrashTo C Mr d F m' fo := Iff.rfl

/-- The removed segments are no more than `first` (the full layout starts at `first - |pg|`). -/
theorem pg_le_first {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {e e0 : Ents} {dF : WalDur}
    (habs : WalAbsD C Mr d lay e) (hF : WalAbsD C Mr dF (unpurge lay.pg lay) e0) :
    lay.pg.length ≤ lay.first := by
  have h1 := habs.cuts.2.2
  have h2 := hF.cuts.2.2
  simp only [unpurge_first, unpurge_segs, unpurge_cuts, List.length_append] at h2
  have := List.length_pos_iff.2 habs.nonempty
  omega

/-- **The full layout's static relation after a step** (see the file header): the removed segments `pg`
and `first` unchanged; the segment starts, streams and history before `first` unchanged (`hstart`,
`hstream`, `hidx`); `pur` not lowered; every new named segment's name at or above an old one's (so above
the removed ones'); the full entries `e0'` listing the removed segments then the new named ones. -/
theorem walAbsD_full_step {C : WalCodec} {Mr : WalMarshal} {d d' : WalDur} {lay lay' : WalLay}
    {e e' e0 e0' : Ents}
    (habs : WalAbsD C Mr d lay e)
    (hF : WalAbsD C Mr (walFullD d lay.pg lay) (unpurge lay.pg lay) e0)
    (habs' : WalAbsD C Mr d' lay' e')
    (hpg : lay'.pg = lay.pg) (hfirst : lay'.first = lay.first)
    (hnd : ((lay.pg ++ lay.segs).map (·.ino)).Nodup)
    (hstart : ∀ i, i ≤ lay.first → segStart lay'.cuts i = segStart lay.cuts i)
    (hstream : ∀ i, i < lay.first → segStream C Mr d' lay'.cuts i = segStream C Mr d lay.cuts i)
    (hidx : ∀ i, i < lay.first →
      (histM d').take (segStart lay.cuts i) = (histM d).take (segStart lay.cuts i))
    (hpur : d.pur ≤ d'.pur)
    (hnm : ∀ b ∈ lay'.segs, ∃ c ∈ lay.segs, c.name = b.name ∨ go.GoStringLt c.name b.name)
    (hents0 : walInos e0' = (lay.pg ++ lay'.segs).map (·.ino)) :
    WalAbsD C Mr (walFullD d' lay'.pg lay') (unpurge lay'.pg lay') e0' := by
  have hpgf := pg_le_first habs hF
  have hne : lay.segs ≠ [] := habs.nonempty
  have hne' : lay'.segs ≠ [] := habs'.nonempty
  have hlen' := habs'.cuts.2.2
  have hsegs0 : 0 < lay.segs.length := List.length_pos_iff.2 hne
  rw [hpg]
  refine ⟨⟨?_, ?_⟩, ⟨habs'.cuts.1, habs'.cuts.2.1, ?_⟩, ?_, ⟨rfl, ?_⟩, ?_, ?_, ?_, habs'.synced,
    habs'.lastSynced, habs'.fit, habs'.tailStop, ?_, habs'.cutPos, ?_⟩
  · rw [hents0]; rfl
  · simp only [unpurge_segs, List.map_append]
    have hF2 := hF.names.2
    simp only [unpurge_segs, List.map_append] at hF2
    obtain ⟨hp1, -, hp3⟩ := List.pairwise_append.1 hF2
    refine List.pairwise_append.2 ⟨hp1, habs'.names.2, fun a ha b hb => ?_⟩
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    obtain ⟨c, hc, hcb⟩ := hnm b' hb'
    have hac := hp3 a ha c.name (List.mem_map_of_mem hc)
    rcases hcb with hcb | hcb
    · rw [← hcb]; exact hac
    · exact go.goStringLt_trans hac hcb
  · simp only [unpurge_first, unpurge_segs, unpurge_cuts, List.length_append]; omega
  · intro k g hk
    simp only [unpurge_first, unpurge_segs, unpurge_cuts] at hk ⊢
    by_cases hkp : k < lay.pg.length
    · rw [getElem?_pg_left hkp] at hk
      obtain ⟨sq, ix, h1, h2, h3⟩ := hF.nameBound k g (by simp only [unpurge_segs]; rw [getElem?_pg_left hkp]; exact hk)
      refine ⟨sq, ix, h1, h2, fun hpos => ?_⟩
      simp only [unpurge_first, unpurge_cuts] at h3
      rw [hfirst] at hpos ⊢
      have hi : lay.first - lay.pg.length + k < lay.first := by omega
      have eH : histM (walFullD d' lay.pg lay') = histM d' := rfl
      have eH0 : histM (walFullD d lay.pg lay) = histM d := rfl
      rw [eH, hstart _ (Nat.le_of_lt hi), hidx _ hi]
      rw [eH0] at h3
      exact h3 hpos
    · rw [getElem?_pg_right (by omega)] at hk
      obtain ⟨sq, ix, h1, h2, h3⟩ := habs'.nameBound (k - lay.pg.length) g hk
      refine ⟨sq, ix, h1, h2, fun hpos => ?_⟩
      have e : lay'.first - lay.pg.length + k = lay'.first + (k - lay.pg.length) := by omega
      rw [e]; exact h3 (by omega)
  · intro hpos
    simp only [unpurge_first, unpurge_cuts, walFullD] at hpos ⊢
    by_cases hp0 : lay.pg = []
    · rw [hp0, List.length_nil, Nat.sub_zero] at hpos ⊢
      rw [← habs'.cut.1]; exact habs'.cut.2 hpos
    · have hlt : 0 < lay.pg.length := List.length_pos_iff.2 hp0
      rw [hfirst] at hpos ⊢
      rw [hstart _ (by omega)]
      have := hF.cut.2 (by simp only [unpurge_first]; omega)
      simp only [walFullD] at this
      exact Nat.le_trans this hpur
  · intro g hg
    simp only [unpurge_segs, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hF.metas g (by simp only [unpurge_segs]; exact List.mem_append_left _ hg)
      refine ⟨h1, h2, h3, h4, Or.inr ?_⟩
      rcases h5 with h5 | h5
      · rw [unpurge_getLast? _ hne] at h5
        exfalso
        rw [List.map_append] at hnd
        exact (List.nodup_append.1 hnd).2.2 g.ino (List.mem_map_of_mem hg) g.ino
          (List.mem_map_of_mem (List.mem_of_getLast? h5)) rfl
      · exact h5
    · obtain ⟨h1, h2, h3, h4, h5⟩ := habs'.metas g hg
      refine ⟨h1, h2, h3, h4, ?_⟩
      rw [unpurge_getLast? _ hne']; exact h5
  · intro k g hk hg
    simp only [unpurge_first, unpurge_segs, unpurge_cuts, List.length_append] at hk hg ⊢
    by_cases hkp : k < lay.pg.length
    · rw [getElem?_pg_left hkp] at hg
      have := hF.intact k g (by simp only [unpurge_segs, List.length_append]; omega)
        (by simp only [unpurge_segs]; rw [getElem?_pg_left hkp]; exact hg)
      simp only [unpurge_first, unpurge_cuts] at this
      rw [hfirst]
      have hi : lay.first - lay.pg.length + k < lay.first := by omega
      show g.bs = (segStream C Mr d' lay'.cuts (lay.first - lay.pg.length + k)).map durB
      rw [hstream _ hi]; exact this
    · rw [getElem?_pg_right (by omega)] at hg
      have := habs'.intact (k - lay.pg.length) g (by omega) hg
      have e : lay'.first - lay.pg.length + k = lay'.first + (k - lay.pg.length) := by omega
      show g.bs = (segStream C Mr d' lay'.cuts (lay'.first - lay.pg.length + k)).map durB
      rw [e]; exact this
  · intro g hg
    rw [unpurge_getLast? _ hne'] at hg
    exact habs'.last g hg
  · simp only [unpurge_segs]; intro h
    exact hne' (List.append_eq_nil_iff.1 h).2
  · intro k g hk
    simp only [unpurge_first, unpurge_segs] at hk ⊢
    by_cases hkp : k < lay.pg.length
    · rw [getElem?_pg_left hkp] at hk
      obtain ⟨ix, hix⟩ := hF.seqName k g (by simp only [unpurge_segs]; rw [getElem?_pg_left hkp]; exact hk)
      simp only [unpurge_first] at hix
      exact ⟨ix, by rw [hfirst]; exact hix⟩
    · rw [getElem?_pg_right (by omega)] at hk
      obtain ⟨ix, hix⟩ := habs'.seqName (k - lay.pg.length) g hk
      have e : lay'.first - lay.pg.length + k = lay'.first + (k - lay.pg.length) := by omega
      exact ⟨ix, by rw [e]; exact hix⟩

/-- **The full layout's relation after a step keeping the history and the cuts** (`walAbsD_full_step`). -/
theorem walAbsD_full_same {C : WalCodec} {Mr : WalMarshal} {d d' : WalDur} {lay lay' : WalLay}
    {e e' e0 e0' : Ents}
    (habs : WalAbsD C Mr d lay e)
    (hF : WalAbsD C Mr (walFullD d lay.pg lay) (unpurge lay.pg lay) e0)
    (habs' : WalAbsD C Mr d' lay' e')
    (hpg : lay'.pg = lay.pg) (hfirst : lay'.first = lay.first) (hcuts : lay'.cuts = lay.cuts)
    (hnd : ((lay.pg ++ lay.segs).map (·.ino)).Nodup)
    (hH : d'.H = d.H) (hmd : d'.metadata = d.metadata) (hpur : d.pur ≤ d'.pur)
    (hnm : ∀ b ∈ lay'.segs, ∃ c ∈ lay.segs, c.name = b.name ∨ go.GoStringLt c.name b.name)
    (hents0 : walInos e0' = (lay.pg ++ lay'.segs).map (·.ino)) :
    WalAbsD C Mr (walFullD d' lay'.pg lay') (unpurge lay'.pg lay') e0' := by
  have eM : histM d' = histM d := by simp [histM, hH]
  refine walAbsD_full_step habs hF habs' hpg hfirst hnd (fun i _ => by rw [hcuts])
    (fun i _ => ?_) (fun i _ => by rw [eM]) hpur hnm hents0
  simp [segStream, segRecs, eM, hmd, hcuts]

end pure

end WalFs
end EtcdGrove
end Perennial

end
