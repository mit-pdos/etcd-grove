/- Lean-first (no Rocq counterpart).

# A synced WAL's crash (`notes/wal-fsext-plan.md`, W2)

Pure. `crashTo_synced`: a WAL whose every segment byte is durable (each `ByteG` a `durB`), whose
synced mark is its whole history, whose last segment's stream is written (`wr`) and followed by zeros
(the preallocation, an 8-byte multiple or nothing), comes back from a crash that keeps its
directory's `.wal` names as they are (`hnames`) as itself: `CrashTo` with the image the history, no
segment dropped. This is the state right after a cut's `fdatasync` of the new segment (S/wal.go:925),
and what `crashOkA_rename`'s `hkept` asks of the new layout (`CutCrash.lean`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCrash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section synced
variable [GooseExts]


/-! ## The `.wal` names -/

/-- Sorting by name (`sort.Strings`) does not see the order of its input. -/
theorem mergeSort_name_perm {l1 l2 : List GoString} (h : l1.Perm l2) :
    l1.mergeSort (fun a b => decide (go.GoStringLt a b ∨ a = b)) =
      l2.mergeSort (fun a b => decide (go.GoStringLt a b ∨ a = b)) := by
  have htr : ∀ a b c : GoString, decide (go.GoStringLt a b ∨ a = b) = true →
      decide (go.GoStringLt b c ∨ b = c) = true → decide (go.GoStringLt a c ∨ a = c) = true := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · exact Or.inl (go.goStringLt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr rfl
  have hto : ∀ a b : GoString,
      (decide (go.GoStringLt a b ∨ a = b) || decide (go.GoStringLt b a ∨ b = a)) = true := by
    intro a b
    by_cases h1 : go.GoStringLt a b
    · simp [h1]
    by_cases h2 : go.GoStringLt b a
    · simp [h2]
    simp [go.goStringLt_eq_of_not_lt h1 h2]
  refine List.Perm.eq_of_pairwise (le := fun a b => decide (go.GoStringLt a b ∨ a = b) = true) ?_
    (List.pairwise_mergeSort htr hto _) (List.pairwise_mergeSort htr hto _)
    ((List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm))
  intro a b _ _ h1 h2
  simp only [decide_eq_true_eq] at h1 h2
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd h2 (go.goStringLt_asymm h1)
    · exact h2.symm
  · exact h1

theorem mem_walKeys {E1 E2 : Ents} (h : ∀ b, walNameP b = true → E1 !! b = E2 !! b) (b : GoString) :
    b ∈ ((GMap.toList E1).map (·.1)).filter walNameP →
      b ∈ ((GMap.toList E2).map (·.1)).filter walNameP := by
  simp only [List.mem_filter, List.mem_map]
  rintro ⟨⟨⟨b', v⟩, hm, rfl⟩, hw⟩
  rw [GMap.mem_toList] at hm
  exact ⟨⟨(b', v), (GMap.mem_toList _ _ _).2 (by rw [← h b' hw]; exact hm), rfl⟩, hw⟩

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self ..), filterMap_congr' (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **Two directories agreeing on their `.wal` names have the same `.wal` files.** -/
theorem walInos_congr {E1 E2 : Ents} (h : ∀ b, walNameP b = true → E1 !! b = E2 !! b) :
    walInos E1 = walInos E2 := by
  have hn : walNames E1 = walNames E2 := by
    unfold walNames
    apply mergeSort_name_perm
    refine (List.perm_ext_iff_of_nodup ((GMap.toList_keys_nodup _).filter _)
      ((GMap.toList_keys_nodup _).filter _)).2 (fun b => ⟨mem_walKeys h b,
        mem_walKeys (fun b hb => (h b hb).symm) b⟩)
  unfold walInos
  rw [hn]
  apply filterMap_congr'
  intro b hb
  have hw : walNameP b = true := by
    unfold walNames at hb; exact (List.mem_filter.1 (List.mem_mergeSort.1 hb)).2
  rw [h b hw]

/-- A segment all of whose bytes are durable comes back as its bytes. -/
theorem img_durable {g : SegG} {f : Fs.OsFile}
    (hfc : FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (some f))
    (hdur : ∀ y ∈ g.bs, y = durB y.1) (hlo : g.om.lo = g.bs.length) (hhi : g.om.hi = g.bs.length) :
    f.contents = g.bs.map (·.1) := by
  have hbs : g.bs = (g.bs.map (·.1)).map durB := by
    rw [List.map_map]
    exact (List.map_id' g.bs).symm.trans (List.map_congr_left (fun y hy => hdur y hy))
  rw [hbs] at hfc
  exact durable_img hfc (by rw [hlo]; simp) (by rw [hhi]; simp)

/-- **A synced WAL's crash** (see the file header). -/
theorem crashTo_synced (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (ents : Ents)
    (m' : Tree) (fo : Ino → Option Fs.OsFile)
    (habs : WalAbsD C Mr d lay ents) (hm : d.m = d.H.length)
    (hdur : ∀ g ∈ lay.segs, ∀ y ∈ g.bs, y = durB y.1)
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hold0 : ∀ b, lay.wr ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
    (hz : lay.old.length - lay.wr = 0 ∨ 8 ≤ lay.old.length - lay.wr)
    (hnames : walInos (entsOf m' lay.j) = walInos ents)
    (hdir : (d.named = false ∧ m'.entry lay.jr lay.nm = none) ∨
      m'.entry lay.jr lay.nm = some (.dir lay.j))
    (hfc : ∀ g ∈ lay.segs, FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino))
    (hnamed : ∀ g ∈ lay.segs, Named m' g.ino → (fo g.ino).isSome) :
    CrashTo C Mr d lay m' fo := by
  rcases hdir with hl | hent
  · exact Or.inl hl
  right
  have hd : WalDur.mk d.H d.m d.unl d.pur d.cut d.metadata d.named d.sized = d := rfl
  have hinos : walInos (entsOf m' lay.j) = lay.segs.map (·.ino) := hnames.trans habs.names.1
  -- every segment's file is there, its image its bytes
  have hsome : ∀ g ∈ lay.segs, ∃ f, fo g.ino = some f ∧ f.contents = g.bs.map (·.1) := by
    intro g hg
    have hn : Named m' g.ino :=
      named_of_mem_walInos (J := lay.j) (by rw [hinos]; exact List.mem_map_of_mem hg)
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hnamed g hg hn)
    have hm' := habs.metas g hg
    refine ⟨f, hf, img_durable (by rw [← hf]; exact hfc g hg) (hdur g hg) hm'.2.2.1 hm'.2.2.2⟩
  have hsorted := habs.cuts.2.1
  have hlast : segStart lay.cuts lay.cuts.length ≤ d.H.length := hm ▸ habs.lastSynced
  refine ⟨0, d.H, hent, List.length_pos_iff.2 habs.nonempty, by rw [List.drop_zero]; exact hinos,
    walImg_refl (by omega), hlast, ?_, ?_, ?_⟩
  · -- the first segment's start
    rw [Nat.add_zero]
    refine Nat.le_min.2 ⟨?_, Nat.le_trans (segStart_le_length hsorted _) hlast⟩
    by_cases h0 : 0 < lay.first
    · rw [← habs.cut.1]; exact habs.cut.2 h0
    · have : lay.first = 0 := by omega
      rw [this]; simp [segStart]
  · -- every segment but the last: its frames
    intro k g hk hkc
    rw [List.drop_zero] at hk
    rw [hd]
    have hkl : k + 1 < lay.segs.length := by have := habs.cuts.2.2; omega
    obtain ⟨f, hf, hc⟩ := hsome g (List.mem_of_getElem? hk)
    rw [habs.intact k g hkl hk, List.map_map] at hc
    simp only [imgOf, hf, Option.map_some, Option.getD_some, Nat.add_zero, hc]
    exact (List.map_id' _).symm.trans (List.map_congr_left (fun _ _ => rfl)) |>.symm
  · -- the last: its stream, then zeros
    intro g hg
    rw [hd]
    obtain ⟨f, hf, hc⟩ := hsome g (List.mem_of_getLast? hg)
    obtain ⟨hso, hwr, hlen, hwro, hbytes, -⟩ := habs.last g hg
    dsimp only
    generalize hS : segStream C Mr d lay.cuts lay.cuts.length = S at hwr htail hbytes ⊢
    have himg : imgOf (fo g.ino) = S ++ List.replicate (lay.old.length - S.length) 0 := by
      simp only [imgOf, hf, Option.map_some, Option.getD_some, hc]
      apply List.ext_getElem (by simp; omega)
      intro b h1 h2
      simp only [List.getElem_map]
      have hb := hbytes b (g.bs[b]'(by simpa using h1)) (List.getElem?_eq_getElem _)
      unfold ByteOk at hb
      by_cases hbS : b < S.length
      · rw [List.getElem_append_left hbS]
        have hw : decide (b < lay.wr) = true := by simp; omega
        rw [hw] at hb
        split at hb
        · rw [hb]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbS]
        · simp only [if_true] at hb
          rw [hb.1]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbS]
      · rw [List.getElem_append_right (by omega)]
        simp only [List.getElem_replicate]
        have hw : decide (b < lay.wr) = false := by simp; omega
        have hs : decide (b < lay.so) = false := by simp; omega
        rw [hw, hs] at hb
        simp only [Bool.false_eq_true, if_false] at hb
        rw [hb]
        exact hold0 b (by omega) (by simp at h1; omega)
    rw [himg]
    refine ⟨List.prefix_append _ _, fun r len c' => ?_⟩
    rw [decStep_zeros C true (z := lay.old.length - S.length) (by rw [← htail]; exact hz)
      (by simp)]
    simp

end synced

end WalFs
end EtcdGrove
end Perennial

end
