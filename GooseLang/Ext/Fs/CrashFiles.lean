/-
What the ghost state of the files and of the tree (`Ghost.lean`) says across a crash (`OsCrash`,
`Impl.lean`): a machine crash (a process's restart is one, by the environment's assumption on
restarts). Untrusted.

* **The tree** after a crash keeps a closed set of the log's entries, with the committed ones
  (`closed_cut`, from the disciplines of the tree's coherence, `TreeCohS`), and the state after a
  crash is one a program may start in (`machineCrash_initS`: `FsInit`), so the new generation's
  ghost state is allocated as the first generation's (`os_local_init`).
* **A file** (`FileCrashedR`, `crashSeen_crashed`): the ghost bytes mirror each byte's crash
  candidates exactly, so a crash keeps of a file the old generation knew, as `m` with the bytes
  of the runs `rs`, a size within `m`'s crash bounds, on disk, and each byte of a run below that
  size one of its candidates; past the zeros `m` knows, zeros. `CrashSeenR` keeps the crashed
  state, its coherence with the old ghost maps and the crash premise `Q`, for a client that needs
  more (a premise on crashes is stated of the state's candidates).
-/
module

public import GooseLang.Ext.Fs.World
public import GooseLang.Ext.Fs.Crash
public import GooseLang.Ext.Fs.TreeCutProof

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The state after a crash, and what it keeps -/

section after
variable {st st' : OsState} {Γb : GMap (Ino × Nat) ByteG} {Γm : GMap Ino OsMeta}
  {Γf : GMap w64 OsFd} {Γt : GMap Nat TokInfo} {Γc : GMap Nat CallV}

/-- **After a machine crash, the state is one a program may start in**
(`closed_cut`, from the shared mode's disciplines on the log), and each slot of the new tree holds
what it held right after the last kept entry writing it. -/
theorem machineCrash_initS {Γdf : GMap w64 (Ino × DirPhS)} (htw : FsTreeWf st)
    {Γg : GMap Nat CallV} (htc : TreeCohS st Γdf Γc Γg) (hc : MachineCrash st st') :
    FsInit st' ∧ ∃ S, (∀ x, S x → x < st.fs.metaLog.length) ∧ Closed st.fs.metaLog S ∧
      (∀ y, st.fs.committed y → S y) ∧
      ∀ j b, st'.fs.treeDur.entry j b = slotAfter st.fs.treeDur st.fs.metaLog S j b := by
  obtain ⟨hp, hr, hlog, hcom, hino, -, ⟨S, hSlt, hSc, hcl, htr⟩, hfiles⟩ := hc
  obtain ⟨ρ, hrc, -⟩ := htc.rc
  obtain ⟨hwf, hslot, hnamed, hkeys⟩ := closed_cut htc.starts htc.pss
    hrc.dox hrc.tags htc.valid (fun t ht => (htw.hist t ht).1) hSlt hcl
  refine ⟨⟨hp, hlog, hcom, by rw [hr]; exact htw.roots, by rw [hr, htr]; exact hwf, ?_, ?_, ?_, ?_⟩,
    S, hSlt, hcl, hSc, fun j b => by rw [htr]; exact hslot j b⟩
  · intro i hi
    obtain ⟨f, f', -, -, hf'⟩ := (hfiles i).1 hi
    rw [hf']; simp
  · intro i f hf
    by_cases hi : Named st'.fs.treeDur i
    · refine ⟨hi, ?_⟩
      obtain ⟨f0, f', -, ⟨sz, vs, -, hmx, -, rfl⟩, hf'⟩ := (hfiles i).1 hi
      rw [hf] at hf'; cases hf'; exact ⟨vs, sz, hmx, rfl⟩
    · rw [(hfiles i).2 hi] at hf; cases hf
  · intro i hi
    rw [hino]
    have hn' : Named st'.fs.treeDur i := by
      apply Classical.byContradiction; intro hn'
      rw [GMap.mem_iff, (hfiles i).2 hn'] at hi; cases hi
    rw [htr] at hn'
    obtain ⟨t', ht', hnt⟩ := hnamed i hn'
    obtain ⟨f, hf⟩ := (htw.hist t' ht').2.1 i hnt
    exact htw.files_lt i (by rw [GMap.mem_iff, hf]; rfl)
  · intro j hj; rw [hino]; rw [htr] at hj
    obtain ⟨t, ht, hjt⟩ := hkeys j hj
    exact (htw.hist t ht).2.2 j hjt

/-- **What a crash keeps of the tree**: the new state is one a program may
start in, on the same roots, every file it names is there, and the crash kept a closed set of the
log's entries, with the committed ones, each slot as right after its last kept writer. -/
theorem osCrash_relS {Γdf : GMap w64 (Ino × DirPhS)} (htw : FsTreeWf st)
    {Γg : GMap Nat CallV} (htc : TreeCohS st Γdf Γc Γg) (hc : OsCrash st st') :
    FsInit st' ∧ st'.fs.roots = st.fs.roots ∧
      (∀ i, Named st'.fs.treeDur i → (st'.fs.files !! i).isSome) ∧
      ∃ S, (∀ x, S x → x < st.fs.metaLog.length) ∧ Closed st.fs.metaLog S ∧
        (∀ y, st.fs.committed y → S y) ∧
        ∀ j b, st'.fs.treeDur.entry j b = slotAfter st.fs.treeDur st.fs.metaLog S j b := by
  obtain ⟨hinit, hS⟩ := machineCrash_initS htw htc hc
  have hfiles := hc.2.2.2.2.2.2.2
  refine ⟨hinit, hc.2.1, fun i hi => ?_, hS⟩
  obtain ⟨f, f', -, -, hf'⟩ := (hfiles i).1 hi
  rw [hf']; rfl

end after

/-! ## A file across a crash -/

/-- What a crash did to a file the old generation knew as `m`, with the bytes of the runs `rs`
(each `(off, dq, xs)`, the bytes `xs` from `off` on): if the new state has it, it is on disk, its
size is within `m`'s crash bounds, each byte of a run below that size is one of the byte's crash
candidates or, at or past `m.lo`, zero (writeback's zeroing, `CrashFile`), the bytes from the
zeros `m` knows on are zeros, and each byte past the size whose candidates `m` knows (`tc`: the
bytes a truncate cut off, a file on disk's) is one of them or, at or past `m.lo`, zero. -/
def FileCrashedR (m : OsMeta) (rs : List (Nat × DFrac × List ByteG)) (fo : Option OsFile) : Prop :=
  ∀ f', fo = some f' → (∃ img, f' = OsFile.ofDisk img f'.size) ∧ m.lo ≤ f'.size ∧ f'.size ≤ m.hi ∧
    (∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), r.1 + k < f'.size →
      (∃ s, (f'.cache (r.1 + k), s) ∈ (r.2.2[k]).2) ∨ (m.lo ≤ r.1 + k ∧ f'.cache (r.1 + k) = 0)) ∧
    (∀ z, m.zf = some z → ∀ b, z ≤ b → b < f'.size → f'.cache b = 0) ∧
    (∀ b c, m.size ≤ b → m.tc !! b = some c → b < f'.size →
      (∃ s, (f'.cache b, s) ∈ c) ∨ (m.lo ≤ b ∧ f'.cache b = 0))

/-- The facts of a crash the restarted program learns of the file of inode `i`, taken with the old
generation's `OsMeta` `m`, the bytes of the runs `rs` and the changes in flight `ts`: the crash
(and the premise `Q`) made the new file `fo` from the crashed state `st`, which is coherent with
the old ghost maps, in which `i`'s `OsMeta` is `m`, the runs' bytes are as `rs` says, and the
changes in flight on `i` are those of `ts`. -/
def CrashSeenR (Q : OsState → OsState → Prop) (i : Ino) (m : OsMeta)
    (rs : List (Nat × DFrac × List ByteG)) (ts : List (Nat × TokInfo)) (fo : Option OsFile) :
    Prop :=
  ∃ (st st' : OsState) (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta)
    (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    OsWf st ∧ OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧ st'.fs.files !! i = fo ∧
    Γm !! i = some m ∧
    (∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (i, r.1 + k) = some r.2.2[k]) ∧
    (∀ t ti, Γt !! t = some ti → ti.ino = i → (t, ti) ∈ ts) ∧
    (∀ x ∈ ts, Γt !! x.1 = some x.2)

/-- **A crash keeps what the ghost state knew of a file** (`FileCrashedR`). -/
theorem crashSeen_crashed {Q : OsState → OsState → Prop} {i : Ino} {m : OsMeta}
    {rs : List (Nat × DFrac × List ByteG)} {ts : List (Nat × TokInfo)} {fo : Option OsFile}
    (h : CrashSeenR Q i m rs ts fo) : FileCrashedR m rs fo := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hwf, hcoh, hc, -, hfo, hm, hrs, -, -⟩ := h
  intro f' hf'
  subst hfo
  obtain ⟨f, hf, hok⟩ := hcoh.meta_some i m hm
  have hn : Named st'.fs.treeDur i := by
    apply Classical.byContradiction; intro hn
    rw [(hc.2.2.2.2.2.2.2 i).2 hn] at hf'; cases hf'
  obtain ⟨f0, f1, hf0, ⟨sz, img, ⟨hlo, hhi, -⟩, -, hcand, rfl⟩, hf1⟩ := (hc.2.2.2.2.2.2.2 i).1 hn
  rw [hf] at hf0; cases hf0
  rw [hf'] at hf1; cases hf1
  have hb : ∀ b, b < sz → (OsFile.ofDisk img sz).cache b = img b := fun b hb => by
    simp only [OsFile.ofDisk, diskByte]
    rw [if_pos (by simp only [pageIn, decide_eq_true_eq]; have := Nat.mul_div_le b 4096; omega)]
  refine ⟨⟨img, rfl⟩, ?_, ?_, fun r hr k hk hks => ?_, fun z hz b hzb hbs => ?_,
    fun b cs hsb hc hbs => ?_⟩
  · show m.lo ≤ sz
    rcases hlo with h | ⟨t, c, ht, hci, h⟩
    · exact Nat.le_trans hok.lo h
    · exact Nat.le_trans (hok.targets t c ht hci).1 h
  · show sz ≤ m.hi
    rcases hhi with h | ⟨t, c, ht, hci, h⟩
    · exact Nat.le_trans h hok.hi
    · exact Nat.le_trans h (hok.targets t c ht hci).2
  · obtain ⟨f1, hf1, -, -, -, hrel⟩ := hcoh.bytes i _ _ (hrs r hr k hk)
    simp only [OsState.file, hf, Option.some.injEq] at hf1; subst hf1
    simp only [OsFile.ofDisk] at hks
    rw [hb _ hks]
    rcases hcand (r.1 + k) with ⟨s, hs⟩ | ⟨hl, h0⟩
    · exact .inl (hrel.mem hs)
    · exact .inr ⟨Nat.le_trans hok.lo hl, h0⟩
  · simp only [OsFile.ofDisk] at hbs
    rw [hb _ hbs]
    rcases hcand b with ⟨s, hs⟩ | ⟨-, h0⟩
    · rw [(hok.zf z hz).2 b hzb, List.mem_singleton] at hs
      exact (Prod.mk.inj hs).1
    · exact h0
  · simp only [OsFile.ofDisk] at hbs
    rw [hb _ hbs]
    rcases hcand b with ⟨s, hs⟩ | ⟨hl, h0⟩
    · rw [hok.tail b cs (by rw [← hok.size]; exact hsb) hc] at hs
      exact .inl ⟨s, hs⟩
    · exact .inr ⟨Nat.le_trans hok.lo hl, h0⟩

/-- **A crash leaves no file larger than `maxBytes`** (the model's bound, `Impl.lean`): what the
restarted program may use of a file's size beside `FileCrashedR` (a segment's size bound across
restarts, the WAL's `ReadAll`). -/
theorem crashSeen_max {Q : OsState → OsState → Prop} {i : Ino} {m : OsMeta}
    {rs : List (Nat × DFrac × List ByteG)} {ts : List (Nat × TokInfo)} {fo : Option OsFile}
    (h : CrashSeenR Q i m rs ts fo) : ∀ f', fo = some f' → f'.size ≤ maxBytes := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, -, -, hc, -, hfo, -, -, -, -⟩ := h
  intro f' hf'
  subst hfo
  have hn : Named st'.fs.treeDur i := by
    apply Classical.byContradiction; intro hn
    rw [(hc.2.2.2.2.2.2.2 i).2 hn] at hf'; cases hf'
  obtain ⟨f0, f1, -, hcf, hf1⟩ := (hc.2.2.2.2.2.2.2 i).1 hn
  rw [hf'] at hf1; cases hf1
  obtain ⟨sz, img, -, hmx, -, rfl⟩ := hcf
  exact hmx

/-- **The size a crash leaves is one `m` knows** (`OsMeta.xs`), or one a change in flight on the
file allows: its target for an `ftruncate`; for a `pwrite` or `fallocate`, any size between the
smallest of those `m` knows (or the target) and the largest (or the target), so the size itself for
a write inside a file whose known sizes are its size alone. -/
theorem crashSeen_xs {Q : OsState → OsState → Prop} {i : Ino} {m : OsMeta}
    {rs : List (Nat × DFrac × List ByteG)} {ts : List (Nat × TokInfo)} {fo : Option OsFile}
    (h : CrashSeenR Q i m rs ts fo) : ∀ f', fo = some f' → ∀ l, m.xs = some l →
      f'.size ∈ l ∨ ∃ x ∈ ts, (x.2.kind.isTrunc = true → f'.size = x.2.target) ∧
        ((∃ a ∈ l, a ≤ f'.size) ∨ x.2.target ≤ f'.size) ∧
        ((∃ b ∈ l, f'.size ≤ b) ∨ f'.size ≤ x.2.target) := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hwf, hcoh, hc, -, hfo, hm, -, hts, -⟩ := h
  intro f' hf' l hl
  subst hfo
  obtain ⟨f, hf, hok⟩ := hcoh.meta_some i m hm
  have hn : Named st'.fs.treeDur i := by
    apply Classical.byContradiction; intro hn
    rw [(hc.2.2.2.2.2.2.2 i).2 hn] at hf'; cases hf'
  obtain ⟨f0, f1, hf0, ⟨sz, img, ⟨hlo, hhi, hsz⟩, -, -, rfl⟩, hf1⟩ := (hc.2.2.2.2.2.2.2 i).1 hn
  rw [hf] at hf0; cases hf0
  rw [hf'] at hf1; cases hf1
  show sz ∈ l ∨ ∃ x ∈ ts, (x.2.kind.isTrunc = true → sz = x.2.target) ∧
    ((∃ a ∈ l, a ≤ sz) ∨ x.2.target ≤ sz) ∧ ((∃ b ∈ l, sz ≤ b) ∨ sz ≤ x.2.target)
  rcases hsz with h | h | h | ⟨t, c, ht, hci, htr⟩
  · exact .inl (hok.xs l hl sz (.inl h))
  · exact .inl (hok.xs l hl sz (.inr (.inl h)))
  · exact .inl (hok.xs l hl sz (.inr (.inr (.inr h))))
  · obtain ⟨ti, hti⟩ := Option.isSome_iff_exists.1 (by rw [hcoh.toks t, ht]; rfl)
    obtain ⟨hino, hk, -, -, htg, -⟩ := hcoh.tok_is t ti c hti ht
    -- the change in flight the bounds name is this one
    have hone : ∀ t' c', st.proc.inflight !! t' = some c' → c'.ino = i → c'.target = ti.target :=
      fun t' c' ht' hci' => by
        have := hwf.infl_one t c t' c' ht ht' (hci.trans hci'.symm)
        subst this; rw [ht] at ht'; cases ht'; exact htg
    refine .inr ⟨(t, ti), hts t ti hti (hino.symm.trans hci), fun hk' => ?_, ?_, ?_⟩
    · rw [← htg]; exact htr (by rw [hk]; exact hk')
    · rcases hlo with h | ⟨t', c', ht', hci', h⟩
      · exact .inl ⟨f.sizeLo, hok.xs l hl _ (.inr (.inl rfl)), h⟩
      · exact .inr (by rw [← hone t' c' ht' hci']; exact h)
    · rcases hhi with h | ⟨t', c', ht', hci', h⟩
      · exact .inl ⟨f.sizeHi, hok.xs l hl _ (.inr (.inr (.inl rfl))), h⟩
      · exact .inr (by rw [← hone t' c' ht' hci']; exact h)

end Fs
end Perennial

end
