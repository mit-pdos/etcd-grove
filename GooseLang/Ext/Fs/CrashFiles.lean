/-
What the ghost state of the files and of the tree (`Ghost.lean`) says across a crash (`OsCrash`,
`Impl.lean`): a machine crash (a process's restart is one, by the environment's assumption on
restarts). Untrusted. The relations below also allow the restart outcome of an earlier version of
the semantics (the history kept whole, `TreeCrashed`'s first case; `restartFile_rel`), which no crash
produces now: they are weaker than needed, and the clients' proofs are unchanged.

* **The pure relation** (`FileCrashedG`, `crash_rel`): a file the old generation knew, if the new
  state has it, has a size within the old crash bounds `[m.lo, m.hi]`, and every byte the old
  generation knew clean is in it, with its value, and is clean in it. A machine crash keeps such a
  byte by `Bridge.crash_keeps_clean`; a restart by `clean_landed` (the changes in flight land around
  it). The tree after a crash is the old history (a restart) or a prefix of it replayed, nothing
  logged (a machine crash, by `Crash.crash_seq`: the log is sequential).
* **The new generation's ghost state** (`os_local_initG`): allocated from any state with no process
  state whose files and tree are well formed: every file with its `OsMeta` from the state
  (`metaOf`: its sizes and crash bounds, its known durable bytes, no mapping) and its bytes, each
  flagged clean if it is (`bytesOf`); the tree's history the state's. After a machine crash every
  file is on disk (`metaOf_ofDisk`, `bytesOf_ofDisk`: all of it durable and clean); after a restart
  the page cache's dirty sectors stay dirty, so a byte not clean in the old state is not in the new.
-/
module

public import GooseLang.Ext.Fs.World
public import GooseLang.Ext.Fs.Bridge
public import GooseLang.Ext.Fs.Crash

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Clean bytes and sizes across a landing -/

/-- A change leaves a clean byte outside its bytes clean, if the new contents keep it. -/
theorem clean_change {f : OsFile} {c : List w8} {lo hi b : Nat} (hb : ¬ (lo ≤ b ∧ b < hi))
    (hc : c.getD b 0 = f.rawAt b) (hcl : b < c.length) (hcp : CleanPhys f b) :
    CleanPhys (f.change c lo hi) b := by
  obtain ⟨hlo, hv⟩ := hcp
  have hr := rawAt_change f c lo hi b hb hc
  refine ⟨?_, fun v hv' => ?_⟩
  · simp only [OsFile.change]; omega
  · rw [hr]
    simp only [OsFile.change] at hv'
    split at hv'
    · simp only [List.mem_append, List.mem_singleton] at hv'
      rcases hv' with hv' | rfl
      · exact hv v hv'
      · rw [secOf_getD, hc]
    · exact hv v hv'

theorem clean_landWrite {f : OsFile} {b : Nat} (off : Nat) (data : List w8) (k : Nat)
    (hk : k ≤ data.length) (hbs : b < f.size) (hcp : CleanPhys f b)
    (hout : b < off ∨ off + data.length ≤ b) :
    CleanPhys (f.landWrite off data k) b := by
  unfold OsFile.landWrite
  split
  · exact hcp
  rename_i hk0
  have hlen : (data.take k).length = k := by rw [List.length_take]; exact Nat.min_eq_left hk
  have hd : data.take k ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have hout' : b < off ∨ off + (data.take k).length ≤ b := by
    rw [hlen]; rcases hout with h | h
    · exact .inl h
    · right; omega
  have hc := written_out f off (data.take k) b hd hbs hout'
  have hnr : ¬ (min off f.size ≤ b ∧ b < off + k) := by
    intro ⟨h1, h2⟩
    rw [hlen] at hout'
    rcases hout' with h3 | h3
    · have : min off f.size = off ∨ min off f.size = f.size := by omega
      omega
    · omega
  exact clean_change hnr hc.1 hc.2 hcp

theorem clean_truncate {f : OsFile} {b : Nat} (sz' : Nat) (hbs : b < f.size) (hb : b < sz')
    (hcp : CleanPhys f b) : CleanPhys (f.truncate sz') b := by
  unfold OsFile.truncate
  exact clean_change (by omega) (resized_getD _ _ _ hb) (by rw [resized_length]; exact hb) hcp

/-- **Changes that land around a clean byte leave it clean**, with its value. -/
theorem clean_landed {s b : Nat} {x : w8} :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → HoldsAt f b x → CleanPhys f b →
      (∀ k ∈ ks, ¬ KAff s k b) → b < s → HoldsAt g b x ∧ CleanPhys g b := by
  intro ks f g hl
  induction hl with
  | nil f => intro hp hc _ _; exact ⟨hp, hc⟩
  | write off data k ks f g hk _ ih =>
    intro hp hc hn hs
    have hout : b < off ∨ off + data.length ≤ b := by
      have := hn _ List.mem_cons_self
      simp only [KAff] at this
      by_cases h : b < off
      · exact .inl h
      · right
        exact Classical.byContradiction fun h' => this ⟨by omega, by omega⟩
    exact ih (holds_landWrite off data k hk hp (.inr hout))
      (clean_landWrite off data k hk hp.1 hc hout)
      (fun k' hk' => hn k' (List.mem_cons_of_mem _ hk')) hs
  | trunc sz sz' ks f g h1 h2 _ ih =>
    intro hp hc hn hs
    have := hn _ List.mem_cons_self
    simp only [KAff] at this
    have hb : b < sz' := by have := hp.1; omega
    exact ih (holds_truncate sz' hp hb) (clean_truncate sz' hp.1 hb hc)
      (fun k' hk' => hn k' (List.mem_cons_of_mem _ hk')) hs

/-- The bounds a change in flight keeps a file's size within (`MetaOk.targets`). -/
def KBound (lo hi : Nat) : OsChangeKind → Prop
  | .write off data => off + data.length ≤ hi
  | .truncate sz => lo ≤ sz ∧ sz ≤ hi

theorem written_length (f : OsFile) (off : Nat) (d : List w8) (hd : d ≠ []) :
    (f.written off d).length = max f.size (off + d.length) := by
  unfold OsFile.written
  rw [if_neg hd]
  generalize hn : max f.size (off + d.length) = n
  have hcl : (f.resized n).length = n := resized_length f n
  have : off + d.length ≤ n := by omega
  simp only [List.length_append, List.length_take, List.length_drop, hcl]
  omega

/-- **Changes that land keep the size within the bounds**, the file's and every change's. -/
theorem size_landed {lo hi : Nat} :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → lo ≤ f.size → f.size ≤ hi →
      (∀ k ∈ ks, KBound lo hi k) → lo ≤ g.size ∧ g.size ≤ hi := by
  intro ks f g hl
  induction hl with
  | nil f => intro h1 h2 _; exact ⟨h1, h2⟩
  | write off data k ks f g hk _ ih =>
    intro h1 h2 hb
    have hk' : off + data.length ≤ hi := hb _ List.mem_cons_self
    have hs : f.size ≤ (f.landWrite off data k).size ∧ (f.landWrite off data k).size ≤ hi := by
      unfold OsFile.landWrite; split
      · exact ⟨Nat.le_refl _, h2⟩
      · rename_i hk0
        have hd : data.take k ≠ [] := by
          intro h; have := congrArg List.length h
          rw [List.length_take, Nat.min_eq_left hk] at this; exact hk0 this
        simp only [OsFile.change]
        rw [written_length f off _ hd, List.length_take]
        constructor <;> omega
    exact ih (by omega) hs.2 (fun k' hk'' => hb k' (List.mem_cons_of_mem _ hk''))
  | trunc sz sz' ks f g hs1 hs2 _ ih =>
    intro h1 h2 hb
    have hk' : lo ≤ sz ∧ sz ≤ hi := hb _ List.mem_cons_self
    have hs : (f.truncate sz').size = sz' := by
      simp only [OsFile.truncate, OsFile.change, resized_length]
    exact ih (by rw [hs]; omega) (by rw [hs]; omega)
      (fun k' hk'' => hb k' (List.mem_cons_of_mem _ hk''))

/-- Changes that land keep every sector's versions non-empty, and the size within the size range. -/
theorem wf_landed :
    ∀ {ks : List OsChangeKind} {f g : OsFile}, Landed ks f g → (∀ n, (f.secs n).vers ≠ []) →
      f.sizeLo ≤ f.size → f.size ≤ f.sizeHi →
      (∀ n, (g.secs n).vers ≠ []) ∧ g.sizeLo ≤ g.size ∧ g.size ≤ g.sizeHi := by
  have hch : ∀ (f : OsFile) (c : List w8) (lo hi : Nat), (∀ n, (f.secs n).vers ≠ []) →
      (∀ n, ((f.change c lo hi).secs n).vers ≠ []) ∧
        (f.change c lo hi).sizeLo ≤ (f.change c lo hi).size ∧
        (f.change c lo hi).size ≤ (f.change c lo hi).sizeHi := by
    intro f c lo hi hv
    refine ⟨fun n => ?_, by simp only [OsFile.change]; omega, by simp only [OsFile.change]; omega⟩
    simp only [OsFile.change]; split
    · simp
    · exact hv n
  intro ks f g hl
  induction hl with
  | nil f => intro hv h1 h2; exact ⟨hv, h1, h2⟩
  | write off data k ks f g hk _ ih =>
    intro hv h1 h2
    unfold OsFile.landWrite at ih
    split at ih
    · exact ih hv h1 h2
    · obtain ⟨a, b, c⟩ := hch f _ _ _ hv; exact ih a b c
  | trunc sz sz' ks f g _ _ _ ih =>
    intro hv _ _
    obtain ⟨a, b, c⟩ := hch f _ _ _ hv; exact ih a b c

/-! ## The pure relation across a crash -/

/-- What a crash did to the file of inode `i`, which the old generation knew as `m`, with bytes
`Γb`: if the new state has it, its size is within the old crash bounds and every byte the old
ghost state knew clean is in it, with its value, and clean. -/
def FileCrashedG (Γb : GMap (Ino × Nat) (w8 × Bool)) (i : Ino) (m : OsMeta) (fo : Option OsFile) :
    Prop :=
  ∀ f', fo = some f' → m.lo ≤ f'.size ∧ f'.size ≤ m.hi ∧
    ∀ b x, Γb !! (i, b) = some (x, true) → f'.contents[b]? = some x ∧ CleanPhys f' b

/-- The same, as a client sees it: from the old `OsMeta` `m` and the bytes of the runs `rs` (each
`(off, dq, xs)`, the bytes `xs` from `off` on). -/
def FileCrashedR (m : OsMeta) (rs : List (Nat × DFrac × List (w8 × Bool))) (fo : Option OsFile) :
    Prop :=
  ∀ f', fo = some f' → m.lo ≤ f'.size ∧ f'.size ≤ m.hi ∧
    ∀ r ∈ rs, ∀ k x, r.2.2[k]? = some x → x.2 = true →
      f'.contents[r.1 + k]? = some x.1 ∧ CleanPhys f' (r.1 + k)

theorem fileCrashedR_of_g {Γb : GMap (Ino × Nat) (w8 × Bool)} {i : Ino} {m : OsMeta}
    {fo : Option OsFile} {rs : List (Nat × DFrac × List (w8 × Bool))}
    (h : FileCrashedG Γb i m fo)
    (hxs : ∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (i, r.1 + k) = some r.2.2[k]) :
    FileCrashedR m rs fo := by
  intro f' hf
  obtain ⟨h1, h2, h3⟩ := h f' hf
  refine ⟨h1, h2, fun r hr k x hk hc => ?_⟩
  obtain ⟨hk', hx⟩ := List.getElem?_eq_some_iff.1 hk
  have := hxs r hr k hk'
  rw [hx] at this
  obtain ⟨y, c⟩ := x
  simp only at hc ⊢; subst hc
  exact h3 _ _ this

/-- The changes in flight on the file `i` of `st`: none affects a byte no change in flight may
change. -/
theorem changesOn_noaff {st : OsState} {i : Ino} {f : OsFile} {b : Nat}
    (hf : st.fs.files !! i = some f) (hn : ¬ InflightAt st i b) :
    ∀ k ∈ changesOn st i, ¬ KAff f.size k b := by
  have hs : st.size i = f.size := by simp [OsState.size, OsState.file, hf]
  intro k hk' ha
  simp only [changesOn, List.mem_map, List.mem_filter, decide_eq_true_eq] at hk'
  obtain ⟨c, ⟨⟨⟨t, c'⟩, hmem, rfl⟩, hci⟩, rfl⟩ := hk'
  apply hn
  refine ⟨t, c', (GMap.mem_toList _ _ _).1 hmem, hci, ?_⟩
  rw [affects_kaff, hci, hs]; exact ha

/-- The changes in flight on the file `i` keep its size within the bounds of its `OsMeta`. -/
theorem changesOn_bound {st : OsState} {i : Ino} {m : OsMeta} {f : OsFile}
    (hf : st.fs.files !! i = some f) (hok : MetaOk st i m f) :
    ∀ k ∈ changesOn st i, KBound m.lo m.hi k := by
  have hs : st.size i = f.size := by simp [OsState.size, OsState.file, hf]
  intro k hk'
  simp only [changesOn, List.mem_map, List.mem_filter, decide_eq_true_eq] at hk'
  obtain ⟨c, ⟨⟨⟨t, c'⟩, hmem, rfl⟩, hci⟩, rfl⟩ := hk'
  have ht := hok.targets t c' ((GMap.mem_toList _ _ _).1 hmem) hci
  unfold OsChange.target at ht
  unfold KBound
  revert ht
  cases c'.kind with
  | write off data => intro ht; dsimp only at ht; omega
  | truncate sz => intro ht; exact ht

section rel
variable {st : OsState} {Γb : GMap (Ino × Nat) (w8 × Bool)} {Γm : GMap Ino OsMeta}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo}

/-- **A machine crash keeps what the old ghost state knew** of a file it keeps. -/
theorem crashFile_rel (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino} {m : OsMeta}
    {f f' : OsFile} (hm : Γm !! i = some m) (hf : st.fs.files !! i = some f)
    (hc : CrashFile st i f f') : FileCrashedG Γb i m (some f') := by
  intro g hg; cases hg
  obtain ⟨f0, hf0, hok⟩ := hcoh.meta_some i m hm
  rw [hf] at hf0; cases hf0
  have hcopy := hc
  obtain ⟨sz, vs, ⟨hlo, hhi⟩, -, rfl⟩ := hc
  have hsizes := hwf.sizes i f (by simp [OsState.file, hf])
  refine ⟨?_, ?_, fun b x hb => ?_⟩
  · show m.lo ≤ sz
    rcases hlo with h | ⟨t, c, ht, hci, h⟩
    · exact Nat.le_trans hok.lo h
    · exact Nat.le_trans (hok.targets t c ht hci).1 h
  · show sz ≤ m.hi
    rcases hhi with h | ⟨t, c, ht, hci, h⟩
    · exact Nat.le_trans h hok.hi
    · exact Nat.le_trans h (hok.targets t c ht hci).2
  · obtain ⟨f1, hf1, hcur, hclean⟩ := hcoh.bytes i b (x, true) hb
    simp only [OsState.file, hf, Option.some.injEq] at hf1; subst hf1
    obtain ⟨⟨hlo', hv⟩, hnin⟩ := hclean rfl
    have hsz : st.size i = f.size := by simp [OsState.size, OsState.file, hf]
    have hbsz : b < f.size := by omega
    have hraw : f.rawAt b = x := by
      rw [contents_getElem?, if_pos hbsz] at hcur; cases hcur; rfl
    have hbimg : b < sz := by
      rcases hlo with h | ⟨t, c, ht, hci, h⟩
      · omega
      · revert h
        unfold OsChange.target
        rcases hck : c.kind with ⟨off, data⟩ | szt
        · rw [hci, hsz]; intro h; dsimp only at h; omega
        · intro h
          dsimp only at h
          apply Classical.byContradiction; intro hlt
          apply hnin
          refine ⟨t, c, ht, hci, ?_⟩
          unfold Affects; rw [hck]; dsimp only; rw [hci, hsz]; omega
    have hk := crash_keeps_clean hf hcopy ⟨hbsz, hraw⟩ (fun v hv' => by rw [hv v hv', hraw]) hnin
      hbimg
    refine ⟨hk, ?_, fun v hv' => ?_⟩
    · simp [OsFile.ofDisk]; exact hbimg
    · simp only [OsFile.ofDisk, List.mem_singleton] at hv'; subst hv'
      simp [OsFile.rawAt, OsFile.ofDisk, Sector.last]

/-- **A restart keeps what the old ghost state knew** of a file: its changes in flight land around
the bytes it knew clean. -/
theorem restartFile_rel (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) {i : Ino} {m : OsMeta}
    {f g : OsFile} (hm : Γm !! i = some m) (hf : st.fs.files !! i = some f)
    {ks : List OsChangeKind} (hperm : ks.Perm (changesOn st i)) (hl : Landed ks f g) :
    FileCrashedG Γb i m (some g) := by
  intro g' hg; cases hg
  obtain ⟨f0, hf0, hok⟩ := hcoh.meta_some i m hm
  rw [hf] at hf0; cases hf0
  have hsizes := hwf.sizes i f (by simp [OsState.file, hf])
  have hsz := size_landed hl (by have := hok.lo; omega) (by have := hok.hi; omega)
    (fun k hk => changesOn_bound hf hok k (hperm.mem_iff.1 hk))
  refine ⟨hsz.1, hsz.2, fun b x hb => ?_⟩
  obtain ⟨f1, hf1, hcur, hclean⟩ := hcoh.bytes i b (x, true) hb
  simp only [OsState.file, hf, Option.some.injEq] at hf1; subst hf1
  obtain ⟨hcp, hnin⟩ := hclean rfl
  have hbsz : b < f.size := by have := hcp.1; omega
  have hraw : f.rawAt b = x := by
    rw [contents_getElem?, if_pos hbsz] at hcur; cases hcur; rfl
  obtain ⟨hh, hc⟩ := clean_landed (s := f.size) hl ⟨hbsz, hraw⟩ hcp
    (fun k hk => changesOn_noaff hf hnin k (hperm.mem_iff.1 hk)) hbsz
  refine ⟨?_, hc⟩
  rw [contents_getElem?, if_pos hh.1, hh.2]

end rel

/-! ## The new generation's ghost values -/

open Classical in
/-- The ghost `OsMeta` of a file of a new generation: its sizes and crash bounds, whether no sector
is lost, its known durable bytes (those of the oldest version of each sector), no mapping, and no
claim of zeros past the size. -/
def metaOf (f : OsFile) : OsMeta :=
  ⟨f.size, f.sizeLo, f.sizeHi,
    decide (∀ n, (f.secs n).dirty = false → (f.secs n).vers.length ≤ 1), ∅,
    (List.range f.size).map (fun b =>
      some ((((f.secs (b / 512)).vers.head?).getD zeroSec).toList.getD (b % 512) 0)),
    false⟩

open Classical in
/-- The bytes of a file of a new generation, each flagged clean if it is. -/
def bytesOf (f : OsFile) : List (w8 × Bool) :=
  (List.range f.size).map (fun b => (f.rawAt b, decide (CleanPhys f b)))

theorem bytesOf_length (f : OsFile) : (bytesOf f).length = f.size := by simp [bytesOf]

/-- A file on disk: one version per sector, the size range a point. -/
theorem ofDisk_clean (vs : Nat → SecBytes) (sz b : Nat) (hb : b < sz) :
    CleanPhys (OsFile.ofDisk vs sz) b := by
  refine ⟨by simp [OsFile.ofDisk]; exact hb, fun v hv => ?_⟩
  simp only [OsFile.ofDisk, List.mem_singleton] at hv; subst hv
  simp [OsFile.rawAt, OsFile.ofDisk, Sector.last]

/-- **After a machine crash, a file's ghost values say it is on disk.** -/
theorem metaOf_ofDisk (vs : Nat → SecBytes) (sz : Nat) :
    metaOf (OsFile.ofDisk vs sz) = initMeta (OsFile.ofDisk vs sz) := by
  unfold metaOf initMeta
  congr 1
  · simp [OsFile.ofDisk]
  · simp only [OsFile.contents, List.map_map]
    apply List.map_congr_left
    intro b _
    simp [OsFile.rawAt, OsFile.ofDisk, Sector.last]

open Classical in
theorem bytesOf_ofDisk (vs : Nat → SecBytes) (sz : Nat) :
    bytesOf (OsFile.ofDisk vs sz) = (OsFile.ofDisk vs sz).contents.map (·, true) := by
  simp only [bytesOf, OsFile.contents, List.map_map]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp, Prod.mk.injEq, true_and]
  have : b < sz := by simpa [OsFile.ofDisk] using hb
  exact @decide_eq_true _ (Classical.propDecidable _) (ofDisk_clean vs sz b this)

/-- The bytes of the files of `st`, each flagged clean if it is. -/
def bytesMapG (st : OsState) : GMap (Ino × Nat) (w8 × Bool) :=
  ⟨fun k => (st.file k.1).bind (fun f => (bytesOf f)[k.2]?),
   ⟨st.fs.files.toList.flatMap (fun pf => (List.range pf.2.size).map (fun b => (pf.1, b))),
    fun ⟨i, b⟩ h => by
      simp only [List.mem_flatMap]
      cases hf : st.file i with
      | none => simp [hf] at h
      | some f =>
        simp only [hf, Option.bind_some] at h
        refine ⟨⟨i, f⟩, (GMap.mem_toList _ _ _).2 hf, ?_⟩
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
        refine ⟨b, ?_, by simp⟩
        rw [← bytesOf_length]
        exact (Option.isSome_iff_exists.1 h).elim fun _ h' => (List.getElem?_eq_some_iff.1 h').1⟩⟩

/-- The files of `st`, with their ghost `OsMeta`. -/
def metaMapG (st : OsState) : GMap Ino OsMeta := GMap.fmap metaOf st.fs.files

open Classical in
theorem bytesOf_get (f : OsFile) (b : Nat) :
    (bytesOf f)[b]? = if b < f.size then some (f.rawAt b, decide (CleanPhys f b)) else none := by
  simp only [bytesOf, List.getElem?_map]
  split
  · rename_i h; rw [List.getElem?_range h]; rfl
  · rename_i h; rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- A state with no process state, well formed, is coherent with the ghost maps of its files. -/
theorem osCohG {st : OsState} (hp : st.proc = ProcState.empty) (hwf : OsWf st) :
    OsCoh st (bytesMapG st) (metaMapG st) ∅ ∅ := by
  classical
  have hnoinfl : ∀ i b, ¬ InflightAt st i b := by
    rintro i b ⟨t, c, ht, -⟩; simp [hp, ProcState.empty] at ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; simp [metaMapG]
  · intro i m hm
    simp only [metaMapG, GMap.lookup_fmap] at hm
    cases hfo : st.fs.files !! i with
    | none => simp [hfo] at hm
    | some f =>
      simp only [hfo, Option.map_some, Option.some.injEq] at hm
      subst hm
      refine ⟨f, rfl, ⟨rfl, Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_, ?_, fun h => by
        simp [metaOf] at h⟩⟩
      · intro h; simp only [metaOf] at h; exact of_decide_eq_true h
      · intro b len; simp [metaOf, hp, ProcState.empty]
      · intro t c ht; simp [hp, ProcState.empty] at ht
      · intro b d hb v hv
        simp only [metaOf, List.getElem?_map] at hb
        by_cases hbs : b < f.size
        · rw [List.getElem?_range hbs] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          rw [hv] at hb; simpa using hb
        · rw [List.getElem?_eq_none (by simp; omega)] at hb; cases hb
  · intro i b x hx
    simp only [bytesMapG, GMap.lookup_mk] at hx
    cases hf : st.file i with
    | none => simp [hf] at hx
    | some f =>
      simp only [hf, Option.bind_some] at hx
      rw [bytesOf_get] at hx
      split at hx
      · rename_i hb
        cases hx
        refine ⟨f, rfl, by rw [contents_getElem?, if_pos hb], fun h => ⟨of_decide_eq_true h, ?_⟩⟩
        exact hnoinfl i b
      · cases hx
  · intro i f b hf hb
    simp [bytesMapG, hf, bytesOf_get, hb]
  · simp [hp, ProcState.empty]
  · intro t; simp [hp, ProcState.empty]
  · intro t ti h; simp at h
  · intro t ti h; simp at h
  · intro t ti h; simp at h
  · intro t ti h; simp at h


/-! ## The state after a crash, and what it keeps -/

/-- What a crash did to the tree's history `V`: kept it (a restart), or kept a prefix of it, nothing
logged since (a machine crash: the durable tree with a prefix of the log replayed). -/
def TreeCrashed (V V' : Hist) : Prop :=
  V' = V ∨ ∃ n, n ≤ V.2.length ∧ V' = (replay ((V.2.take n).map (·.op)) V.1, [])

section after
variable {st st' : OsState} {Γb : GMap (Ino × Nat) (w8 × Bool)} {Γm : GMap Ino OsMeta}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo} {V : Hist} {Γdf : GMap w64 (Ino × DirPh)}
  {Γc : GMap Nat (Nat × Qp)}

/-- After a machine crash, the state is one a program may start in. -/
theorem machineCrash_init (htw : FsTreeWf st) (htc : TreeCoh st V Γdf Γc)
    (hc : MachineCrash st st') :
    FsInit st' ∧ ∃ n, n ≤ st.fs.metaLog.length ∧
      st'.fs.treeDur = replay ((st.fs.metaLog.take n).map (·.op)) st.fs.treeDur := by
  obtain ⟨hp, hr, hlog, hcom, hino, ⟨S, hSlt, -, hcl, htr⟩, hfiles⟩ := hc
  obtain ⟨n, hn, hk⟩ := crash_seq htc.seq hSlt hcl
  rw [hk] at htr
  obtain ⟨hwf, hnamed, hlt⟩ := htw.hist n hn
  refine ⟨⟨hp, hlog, hcom, by rw [hr]; exact htw.roots, by rw [hr, htr]; exact hwf, ?_, ?_, ?_, ?_⟩,
    n, hn, htr⟩
  · intro i hi
    obtain ⟨f, f', -, -, hf'⟩ := (hfiles i).1 hi
    rw [hf']; simp
  · intro i f hf
    by_cases hi : Named st'.fs.treeDur i
    · refine ⟨hi, ?_⟩
      obtain ⟨f0, f', -, ⟨sz, vs, -, -, rfl⟩, hf'⟩ := (hfiles i).1 hi
      rw [hf] at hf'; cases hf'; exact ⟨vs, sz, rfl⟩
    · rw [(hfiles i).2 hi] at hf; cases hf
  · intro i hi
    rw [hino]
    have hn' : Named st'.fs.treeDur i := by
      apply Classical.byContradiction; intro hn'
      rw [GMap.mem_iff, (hfiles i).2 hn'] at hi; cases hi
    rw [htr] at hn'
    obtain ⟨f, hf⟩ := hnamed i hn'
    exact htw.files_lt i (by rw [GMap.mem_iff, hf]; rfl)
  · intro j hj; rw [hino]; rw [htr] at hj; exact hlt j hj

/-- **What a crash keeps**: the new state's files and tree are well formed, coherent with a history
`V'` that is a crash of the old one, every file it names is a file of the new state, and every file
the old ghost state knew is, if the new state has it, as `FileCrashedG` says. -/
theorem osCrash_rel (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) (htw : FsTreeWf st)
    (htc : TreeCoh st V Γdf Γc) (hc : OsCrash st st') :
    st'.proc = ProcState.empty ∧ st'.fs.roots = st.fs.roots ∧ OsWf st' ∧ FsTreeWf st' ∧
    ∃ V', TreeCoh st' V' ∅ ∅ ∧ TreeCrashed V V' ∧
      (∀ i, Named V'.now i → (st'.fs.files !! i).isSome) ∧
      ∀ i m, Γm !! i = some m → FileCrashedG Γb i m (st'.fs.files !! i) := by
  obtain ⟨hinit, n, hn, htr⟩ := machineCrash_init htw htc hc
  obtain ⟨hwf', -⟩ := osInit_wf_coh hinit
  obtain ⟨htw', htc'⟩ := fsInit_tree hinit
  have hfiles := hc.2.2.2.2.2.2
  refine ⟨hinit.1, hc.2.1, hwf', htw', _, htc', .inr ⟨n, ?_, ?_⟩, ?_, ?_⟩
  · rw [htc.hist]; exact hn
  · rw [htc.hist, htr]
  · intro i hi
    have hi' : Named st'.fs.treeDur i := by
      simpa [Hist.now, Hist.ops, replay] using hi
    obtain ⟨f, f', -, -, hf'⟩ := (hfiles i).1 hi'
    rw [hf']; rfl
  · intro i m hm
    intro f' hf'
    by_cases hi : Named st'.fs.treeDur i
    · obtain ⟨f, f'', hf, hcf, hf''⟩ := (hfiles i).1 hi
      rw [hf''] at hf'; cases hf'
      exact crashFile_rel hwf hcoh hm hf hcf _ rfl
    · rw [(hfiles i).2 hi] at hf'; cases hf'

end after
end Fs
end Perennial

end
