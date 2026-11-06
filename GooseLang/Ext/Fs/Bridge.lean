/-
The bridge from the sector model to the per-byte reasoning of the program logic: a byte that is
clean in every version of its sector, and that no change in flight may change, is what every crash
leaves (`crash_keeps_clean`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- The change of kind `k` may change byte `b` of a file of size `s` (`Affects`, by kind). -/
def KAff (s : Nat) (k : OsChangeKind) (b : Nat) : Prop :=
  match k with
  | .write off data => min off s ≤ b ∧ b < off + data.length
  | .truncate sz => min s sz ≤ b

theorem affects_kaff (st : OsState) (c : OsChange) (b : Nat) :
    Affects st c b ↔ KAff (st.size c.ino) c.kind b := by
  unfold Affects KAff; cases c.kind <;> simp [inRange]

/-- Byte `b` of the sector version `v`: the byte at its offset in the sector. -/
theorem rawAt_def (f : OsFile) (b : Nat) :
    f.rawAt b = (f.secs (b / 512)).last.toList.getD (b % 512) 0 := rfl

theorem secOf_getD (c : List w8) (b : Nat) :
    (secOf c (b / 512)).toList.getD (b % 512) 0 = c.getD b 0 := by
  have hb : b % 512 < 512 := Nat.mod_lt _ (by decide)
  have he : 512 * (b / 512) + b % 512 = b := Nat.div_add_mod b 512
  simp only [secOf, List.getD_eq_getElem?_getD, Vector.toList_ofFn, List.getElem?_ofFn]
  simp [hb, he]

/-- A change leaves a byte outside its bytes as it was, if the new contents keep it. -/
theorem rawAt_change (f : OsFile) (c : List w8) (lo hi b : Nat) (hb : ¬ (lo ≤ b ∧ b < hi))
    (hc : c.getD b 0 = f.rawAt b) : (f.change c lo hi).rawAt b = f.rawAt b := by
  rw [rawAt_def, rawAt_def]
  simp only [OsFile.change]
  split
  · have hl : ({ vers := (f.secs (b / 512)).vers ++ [secOf c (b / 512)], dirty := true } :
        Sector).last = secOf c (b / 512) := by simp [Sector.last]
    rw [hl, secOf_getD, hc, rawAt_def]
  · rfl

/-- `P`: byte `b` is below the size, and the page cache's versions hold `x` there. -/
def HoldsAt (f : OsFile) (b : Nat) (x : w8) : Prop := b < f.size ∧ f.rawAt b = x

theorem resized_getD (f : OsFile) (sz b : Nat) (hb : b < sz) : (f.resized sz).getD b 0 = f.rawAt b := by
  simp [OsFile.resized, List.getD_eq_getElem?_getD, hb]

theorem resized_length (f : OsFile) (sz : Nat) : (f.resized sz).length = sz := by
  simp [OsFile.resized]

/-- The bytes `written` gives outside the written range: what the file's versions hold. -/
theorem written_out (f : OsFile) (off : Nat) (d : List w8) (b : Nat) (hd : d ≠ [])
    (hbs : b < f.size) (hb : b < off ∨ off + d.length ≤ b) :
    (f.written off d).getD b 0 = f.rawAt b ∧ b < (f.written off d).length := by
  unfold OsFile.written
  rw [if_neg hd]
  generalize hn : max f.size (off + d.length) = n
  have hn1 : f.size ≤ n := by omega
  have hn2 : off + d.length ≤ n := by omega
  have hcl : (f.resized n).length = n := resized_length f n
  have hA : ((f.resized n).take off).length = off := by
    rw [List.length_take, hcl]; exact Nat.min_eq_left (by omega)
  have hAd : ((f.resized n).take off ++ d).length = off + d.length := by
    rw [List.length_append, hA]
  have hD : ((f.resized n).drop (off + d.length)).length = n - (off + d.length) := by
    rw [List.length_drop, hcl]
  have hlen : ((f.resized n).take off ++ d ++ (f.resized n).drop (off + d.length)).length = n := by
    rw [List.length_append, hAd, hD]; omega
  refine ⟨?_, by rw [hlen]; omega⟩
  rw [List.getD_eq_getElem?_getD]
  rcases hb with hlt | hge
  · rw [List.getElem?_append_left (by rw [hAd]; omega), List.getElem?_append_left (by rw [hA]; exact hlt),
      List.getElem?_take_of_lt hlt, ← List.getD_eq_getElem?_getD, resized_getD _ _ _ (by omega)]
  · rw [List.getElem?_append_right (by rw [hAd]; exact hge), hAd, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
    have : off + d.length + (b - (off + d.length)) = b := by omega
    rw [this, resized_getD _ _ _ (by omega)]

theorem holds_landWrite {f : OsFile} {b : Nat} {x : w8} (off : Nat) (data : List w8) (k : Nat)
    (hk : k ≤ data.length) (hp : HoldsAt f b x) (hn : ¬ KAff f.size (.write off data) b ∨
      (b < off ∨ off + data.length ≤ b)) :
    HoldsAt (f.landWrite off data k) b x := by
  have hout : b < off ∨ off + data.length ≤ b := by
    rcases hn with hn | hn
    · simp only [KAff] at hn
      by_cases h : b < off
      · exact .inl h
      · right
        exact Classical.byContradiction fun h' => hn ⟨by omega, by omega⟩
    · exact hn
  unfold OsFile.landWrite
  split
  · exact hp
  rename_i hk0
  have hlen : (data.take k).length = k := by rw [List.length_take]; exact Nat.min_eq_left hk
  have hd : data.take k ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have hout' : b < off ∨ off + (data.take k).length ≤ b := by
    rw [hlen]; rcases hout with h | h
    · exact .inl h
    · right; omega
  have hc := written_out f off (data.take k) b hd hp.1 hout'
  have hbs := hp.1
  have hnr : ¬ (min off f.size ≤ b ∧ b < off + k) := by
    intro ⟨h1, h2⟩
    rw [hlen] at hout'
    rcases hout' with h3 | h3
    · have : min off f.size = off ∨ min off f.size = f.size := by omega
      omega
    · omega
  refine ⟨?_, ?_⟩
  · simp only [OsFile.change]; exact hc.2
  · rw [rawAt_change _ _ _ _ _ hnr hc.1, hp.2]

theorem holds_truncate {f : OsFile} {b : Nat} {x : w8} (sz' : Nat) (hp : HoldsAt f b x)
    (hb : b < sz') : HoldsAt (f.truncate sz') b x := by
  unfold OsFile.truncate
  have hc : (f.resized sz').getD b 0 = f.rawAt b := resized_getD _ _ _ hb
  refine ⟨by simp [OsFile.change, OsFile.resized]; exact hb, ?_⟩
  rw [rawAt_change _ _ _ _ _ (by have := hp.1; omega) hc, hp.2]

/-- **Changes that land around byte `b` leave it.** -/
theorem holds_landed {s b : Nat} {x : w8} :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → HoldsAt f b x →
      (∀ k ∈ ks, ¬ KAff s k b) → b < s → HoldsAt g b x := by
  intro ks f g hl
  induction hl with
  | nil f => intro hp _ _; exact hp
  | write off data k ks f g hk _ ih =>
    intro hp hn hs
    apply ih _ (fun k' hk' => hn k' (List.mem_cons_of_mem _ hk')) hs
    apply holds_landWrite off data k hk hp (.inr ?_)
    have := hn _ List.mem_cons_self
    simp only [KAff] at this
    by_cases h : b < off
    · exact .inl h
    · right
      exact Classical.byContradiction fun h' => this ⟨by omega, by omega⟩
  | trunc sz sz' ks f g h1 h2 _ ih =>
    intro hp hn hs
    apply ih _ (fun k' hk' => hn k' (List.mem_cons_of_mem _ hk')) hs
    have := hn _ List.mem_cons_self
    simp only [KAff] at this
    exact holds_truncate sz' hp (by have := hp.1; omega)

/-- **A crash keeps a clean byte** that no change in flight may change: every version of its
sector, and every landing of the changes in flight, holds it. -/
theorem crash_keeps_clean {st : OsState} {i : Ino} {f f' : OsFile} {b : Nat} {x : w8}
    (hf : st.fs.files !! i = some f) (hc : CrashFile st i f f') (hp : HoldsAt f b x)
    (hv : ∀ v ∈ (f.secs (b / 512)).vers, v.toList.getD (b % 512) 0 = x)
    (hn : ¬ InflightAt st i b) (hsz : b < f'.size) :
    f'.contents[b]? = some x := by
  obtain ⟨sz, vs, -, hcand, rfl⟩ := hc
  have hb : b < sz := hsz
  simp only [OsFile.contents, OsFile.ofDisk, List.getElem?_map, List.getElem?_range hb,
    Option.map_some, OsFile.rawAt, Sector.last, List.getLast?_singleton, Option.getD_some]
  congr 1
  rcases hcand (b / 512) with hmem | ⟨ks, g, hperm, hl, hvg⟩
  · exact hv _ hmem
  · have hs : st.size i = f.size := by simp [OsState.size, OsState.file, hf]
    have hg := holds_landed hl hp (s := f.size) (fun k hk => by
      have hk' := hperm.mem_iff.1 hk
      simp only [changesOn, List.mem_map, List.mem_filter, decide_eq_true_eq] at hk'
      obtain ⟨c, ⟨⟨⟨t, c'⟩, hmem, rfl⟩, hci⟩, rfl⟩ := hk'
      intro ha
      apply hn
      refine ⟨t, c', (GMap.mem_toList _ _ _).1 hmem, hci, ?_⟩
      rw [affects_kaff, hci, hs]; exact ha) hp.1
    rw [hvg]; exact hg.2

end Fs
end Perennial

end
