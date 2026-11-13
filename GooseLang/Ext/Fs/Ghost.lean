/-
The ghost state of the Linux file extension (`GooseLang/Ext/Fs/Impl.lean`): its values, the pure
relations between it and the extension's state, and the extension's ghost state for the adequacy
theorem (`ExtInterp`). The specs are in `Specs.lean`; the step lemmas and the resources in
`World.lean`. Untrusted.

* Ghost maps, all in the one `AllG GF`: the bytes of the page cache, `(i, b) ↦ (x, cs)` for every
  byte `b < size` of the file of inode `i`, its page-cache value and its crash candidates, exactly
  (`ByteG`); the files, `i ↦ m` (an `OsMeta`: the size, its crash bounds, the mappings, the bytes
  that may not be durable, the zeros known past the size); the fds; the changes in flight
  (`TokInfo`); the tree's history (one entry, `Hist`); the directory fds (`DirPh`); the calls on
  paths in flight (`calls`, token ↦ start).
* The relations: `OsWf` (the state alone) and `OsCoh` (the files' maps mirror the state); `FsTreeWf`
  and `TreeCoh` (the history is the state's durable tree and log, the log is `Sequential`, a
  directory fd's read holds a view of the history).
* A change in flight holds the whole of its file's `OsMeta` and the bytes below the size it
  announced (`tokRes`): at most one change is in flight on a file (the semantics' stuck rule), and
  while it is, nothing else changes the file.
* The heap: `cellView`, the invariant `osInv` of `World.lean`.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat
public import GooseLang.Ext.Fs.TreeGhost
public import GooseLang.Ext.Fs.NamesGhost
public import GooseLang.Ext.Fs.Bridge
public import GooseLang.Ext.Fs.Crash
public import GooseLang.Ext.Fs.SemOk
public import GooseLang.Ext.Fs.CommitMono

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost values -/

/-- What the ghost state holds of a byte of the page cache: its value and its crash candidates. -/
abbrev ByteG := w8 × Cands

/-- A durable byte holding `x`: its one candidate is `x`, as of the last sync. -/
abbrev durB (x : w8) : ByteG := (x, [(x, 0)])

/-- What the ghost state knows of a file. -/
structure OsMeta where
  /-- The size of the page cache. -/
  size : Nat
  /-- Bounds of the size a crash may leave the file with. -/
  lo : Nat
  hi : Nat
  /-- The mappings of the file: base address to length. -/
  maps : GMap Loc Nat
  /-- Every byte below the size outside `[dlo, dhi)` is durable (`durB`): a successful sync makes
  every byte so, and a change adds the bytes it announces. -/
  dlo : Nat
  dhi : Nat
  /-- Zeros known past an offset: `some z` if `z` is at least the size and every byte from `z` on
  has the one candidate 0, stamped 0 (durable zeros: a file created in this generation, `some 0`; a
  file on disk, or after a successful sync, the end of its size's last page). -/
  zf : Option Nat := none
  /-- Candidates known past the size: `some c` for a byte `b` at or past the size if its
  candidates are `c` (a file on disk: every byte's, its value on disk at stamp 0, the bytes past
  the size included, which a crash may have left in the size's last page). A change forgets the
  bytes it announces; a successful sync forgets all of them (`zf` keeps its zeros). -/
  tc : GMap Nat Cands := ∅
  /-- How the file's byte resources' candidates relate to the state's (`CandRel`): `none`, the
  same; `some c`, after a sync without the bytes (`wp_osFsyncB`) at change number `c`: the state's
  are one candidate stamped 0, then the resource's stamped after `c`. -/
  cut : Option Nat := none

/-- How the candidates `cs` of a byte resource relate to the state's `sc`, as `cut` says: the same
(`none`); or (`some c`, after a sync without the bytes at change number `c`) the same candidates
stamped after `c`, and every value of the state's among the resource's. -/
def CandRel : Option Nat → Cands → Cands → Prop
  | none, cs, sc => sc = cs
  | some c, cs, sc => sc.filter (fun p => decide (c < p.2)) = cs.filter (fun p => decide (c < p.2)) ∧
      ∀ p ∈ sc, ∃ s, (p.1, s) ∈ cs

/-- Equal candidates relate under any cut. -/
theorem CandRel.of_eq (o : Option Nat) {cs sc : Cands} (h : sc = cs) : CandRel o cs sc := by
  subst h
  cases o with
  | none => rfl
  | some c => exact ⟨rfl, fun p hp => ⟨p.2, hp⟩⟩

/-- A change numbered after the cut appends its candidate to both. -/
theorem CandRel.append {o : Option Nat} {cs sc : Cands} (h : CandRel o cs sc) (v : w8) (n : Nat)
    (hn : ∀ c, o = some c → c < n) : CandRel o (cs ++ [(v, n)]) (sc ++ [(v, n)]) := by
  cases o with
  | none => simp only [CandRel] at h ⊢; rw [h]
  | some c =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, fun p hp => ?_⟩
    · rw [List.filter_append, List.filter_append, h1]
    · rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨s, hs⟩ := h2 p hp; exact ⟨s, List.mem_append_left _ hs⟩
      · simp at hp; subst hp; exact ⟨n, by simp⟩

/-- A durable byte relates to itself under any cut. -/
theorem CandRel.dur (o : Option Nat) (x : w8) : CandRel o [(x, 0)] [(x, 0)] := CandRel.of_eq o rfl

/-- The state's candidates' values are among the resource's. -/
theorem CandRel.mem {o : Option Nat} {cs sc : Cands} (h : CandRel o cs sc) {p : w8 × Nat}
    (hp : p ∈ sc) : ∃ s, (p.1, s) ∈ cs := by
  cases o with
  | none => simp only [CandRel] at h; subst h; exact ⟨p.2, hp⟩
  | some c => exact h.2 p hp

/-- The cut of the file `i` in the files' ghost map `Γm`. -/
def cutOf (Γm : GMap Ino OsMeta) (i : Ino) : Option Nat := (Γm !! i).bind OsMeta.cut

/-- `[dlo, dhi)` with `[lo, hi)` added: the smallest interval that holds both (an empty interval,
`dhi ≤ dlo`, holds nothing). -/
def OsMeta.touch (m : OsMeta) (lo hi : Nat) : OsMeta :=
  if hi ≤ lo then m
  else if m.dhi ≤ m.dlo then { m with dlo := lo, dhi := hi }
  else { m with dlo := min m.dlo lo, dhi := max m.dhi hi }

/-- An in-flight change, as the ghost state records it: its file, what it does, its number (the
stamp of the candidates it announced), the file's `OsMeta` before its first step, and the bytes
below the size it announced, as its first step left them. What it announced is determined by its
kind and the size at its first step (`TokInfo.lo`, `hi`, `val`, `target`). -/
structure TokInfo where
  ino : Ino
  kind : OsChangeKind
  n : Nat
  m0 : OsMeta
  saved : List ByteG

/-- The first byte the change announced. -/
def TokInfo.lo (ti : TokInfo) : Nat :=
  match ti.kind with
  | .write off _ => min off ti.m0.size
  | .truncate sz => min ti.m0.size sz

/-- The end of the bytes the change announced. -/
def TokInfo.hi (ti : TokInfo) : Nat :=
  match ti.kind with
  | .write off data => off + data.length
  | .truncate sz => max ti.m0.size sz

/-- The value the change announced for byte `b` (in its range). -/
def TokInfo.val (ti : TokInfo) (b : Nat) : w8 :=
  match ti.kind with
  | .write off data => if off ≤ b then data.getD (b - off) 0 else 0
  | .truncate _ => 0

/-- The size the change leaves the file with. -/
def TokInfo.target (ti : TokInfo) : Nat :=
  match ti.kind with
  | .write off data => max ti.m0.size (off + data.length)
  | .truncate sz => sz

/-- `m` as a change's first step leaves it, which announced `[lo, hi)` with the target `tg`: the
bytes it announced below the size may no longer be durable; past the zeros known, they no longer
have only the zero candidate; a crash may leave the file with the target size. -/
def OsMeta.announce (m : OsMeta) (lo hi tg : Nat) : OsMeta :=
  { m.touch lo hi with
    zf := m.zf.map (fun z => if lo < hi then max z hi else z),
    lo := min m.lo tg, hi := max m.hi tg,
    tc := m.tc.filter (fun b _ => !inRange lo hi b) }

@[simp] theorem OsMeta.touch_cut (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).cut = m.cut := by
  unfold OsMeta.touch; split
  · rfl
  · split <;> rfl

@[simp] theorem OsMeta.announce_cut (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).cut = m.cut := by
  simp [OsMeta.announce]

/-- The `OsMeta` a change holds. -/
def TokInfo.meta (ti : TokInfo) : OsMeta := ti.m0.announce ti.lo ti.hi ti.target

/-- The change `c` in flight is the one `ti` records. -/
def TokInfo.Is (ti : TokInfo) (c : OsChange) : Prop :=
  c.ino = ti.ino ∧ c.kind = ti.kind ∧ c.lo = ti.lo ∧ c.hi = ti.hi ∧ c.target = ti.target ∧
    ∀ b, inRange c.lo c.hi b = true → c.val b = ti.val b

instance OsMeta.countable : Pos.Countable OsMeta :=
  Pos.Countable.ofInjective
    (fun m => Pos.Countable.encode (m.size, m.lo, m.hi, m.maps, m.dlo, m.dhi, m.zf, m.tc, m.cut))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h; subst h1 h2 h3 h4 h5 h6 h7 h8 h9; rfl)

instance Qp.countable : Pos.Countable Qp :=
  Pos.Countable.ofInjective (fun q => Pos.Countable.encode (q.val.num, q.val.den))
    (fun a b h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Rat.ext h.1 h.2))

/-- The roots of the tree: each a path and its directory's inode. -/
abbrev Roots := List (GoString × Ino)

/-- Where a directory fd's read is, as the ghost state knows it: not begun; begun, with the names
returned `rs`; done. In every phase the fd holds a fraction `q` of the tree's history (in the state
interpretation, `rdRes`), from its open to its close, of which `g` is the directory's view: so the
directory cannot change while it is open. -/
inductive DirPh where
  | idle (g : DirG) (q : Qp)
  | reading (rs : List GoString) (g : DirG) (q : Qp)
  | done (g : DirG) (q : Qp)

/-- The view a directory fd's phase holds. -/
def DirPh.g : DirPh → DirG
  | .idle g _ => g
  | .reading _ g _ => g
  | .done g _ => g

/-- The fraction of the history a directory fd's phase holds. -/
def DirPh.q : DirPh → Qp
  | .idle _ q => q
  | .reading _ _ q => q
  | .done _ q => q

def DirPh.enc : DirPh → Nat × List GoString × DirG × Qp
  | .idle g q => (0, [], g, q)
  | .reading rs g q => (1, rs, g, q)
  | .done g q => (2, [], g, q)

instance DirPh.countable : Pos.Countable DirPh :=
  Pos.Countable.ofInjective (fun x => Pos.Countable.encode x.enc)
    (fun a b h => by
      have h : a.enc = b.enc := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [DirPh.enc])

instance OsFd.countable : Pos.Countable OsFd :=
  Pos.Countable.ofInjective (fun d => Pos.Countable.encode (d.ino, d.readable, d.writable))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)

def OsChangeKind.enc : OsChangeKind → (Nat × List w8) ⊕ Nat
  | .write off data => .inl (off, data)
  | .truncate sz => .inr sz

instance OsChangeKind.countable : Pos.Countable OsChangeKind :=
  Pos.Countable.ofInjective (fun k => Pos.Countable.encode k.enc)
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [OsChangeKind.enc])

instance TokInfo.countable : Pos.Countable TokInfo :=
  Pos.Countable.ofInjective (fun t => Pos.Countable.encode (t.ino, t.kind, t.n, t.m0, t.saved))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

/-! ## Derived facts about a state -/

section derived
variable (st : OsState)

/-- The state's files are well formed: what the operations maintain of them, independently of the
ghost state. -/
structure OsWf : Prop where
  fds : ∀ fd d, st.proc.fds !! fd = some d → ∃ f, st.file d.ino = some f
  maps : ∀ b m, st.proc.maps !! b = some m →
    (∃ f, st.file m.ino = some f) ∧ 0 < b.addr ∧ b.addr + m.len ≤ maxAddr ∧ 0 < m.len
  maps_disj : ∀ b1 m1 b2 m2, st.proc.maps !! b1 = some m1 → st.proc.maps !! b2 = some m2 →
    b1 ≠ b2 → b1.addr + m1.len ≤ b2.addr ∨ b2.addr + m2.len ≤ b1.addr
  infl : ∀ t c, st.proc.inflight !! t = some c → ∃ f, st.file c.ino = some f
  /-- At most one change is in flight on a file. -/
  infl_one : ∀ t1 c1 t2 c2, st.proc.inflight !! t1 = some c1 →
    st.proc.inflight !! t2 = some c2 → c1.ino = c2.ino → t1 = t2
  sizes : ∀ i f, st.file i = some f → f.sizeLo ≤ f.size ∧ f.size ≤ f.sizeHi
  /-- Every candidate's stamp is at most the last change's number. -/
  stamps : ∀ i f b p, st.file i = some f → p ∈ f.cand b → p.2 ≤ st.fs.stamp

/-- What the ghost `OsMeta` `m` of the file `f` of inode `i` says of it. -/
structure MetaOk (i : Ino) (m : OsMeta) (f : OsFile) : Prop where
  size : m.size = f.size
  lo : m.lo ≤ f.sizeLo
  hi : f.sizeHi ≤ m.hi
  maps : ∀ b len, m.maps !! b = some len ↔ st.proc.maps !! b = some ⟨i, len⟩
  targets : ∀ t c, st.proc.inflight !! t = some c → c.ino = i →
    m.lo ≤ c.target ∧ c.target ≤ m.hi
  dur : ∀ b, b < f.size → ¬ (m.dlo ≤ b ∧ b < m.dhi) → f.cand b = [(f.cache b, 0)]
  zf : ∀ z, m.zf = some z → f.size ≤ z ∧ ∀ b, z ≤ b → f.cand b = [(0, 0)]
  tail : ∀ b c, f.size ≤ b → m.tc !! b = some c → f.cand b = c

/-- The files' ghost maps mirror the state. -/
structure OsCoh (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta)
    (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo) : Prop where
  meta_dom : ∀ i, Γm !! i = none ↔ st.fs.files !! i = none
  meta_some : ∀ i m, Γm !! i = some m → ∃ f, st.fs.files !! i = some f ∧ MetaOk st i m f
  /-- A byte resource holds the page-cache value, one of its candidates' values, and candidates
  the state's relate to (`CandRel`, by the file's cut). -/
  bytes : ∀ i b x, Γb !! (i, b) = some x →
    ∃ f, st.file i = some f ∧ b < f.size ∧ x.1 = f.cache b ∧ (∃ s, (x.1, s) ∈ x.2) ∧
      CandRel (cutOf Γm i) x.2 (f.cand b)
  bytes_full : ∀ i f b, st.file i = some f → b < f.size → (Γb !! (i, b)).isSome
  fds : Γf = st.proc.fds
  toks : ∀ t, (Γt !! t).isSome = (st.proc.inflight !! t).isSome
  /-- A change in flight is the one its ghost entry records; it holds its file's `OsMeta`, as its
  first step left it; the size is the one its first step saw. -/
  tok_is : ∀ t ti c, Γt !! t = some ti → st.proc.inflight !! t = some c → ti.Is c
  tok_meta : ∀ t ti, Γt !! t = some ti → Γm !! ti.ino = some ti.meta
  tok_file : ∀ t ti, Γt !! t = some ti → ∃ f, st.file ti.ino = some f ∧ ti.m0.size = f.size ∧
    ti.lo ≤ ti.hi ∧ ti.saved.length = min ti.hi f.size - ti.lo
  /-- Each byte a change announced has its value as the last candidate, stamped with its number;
  before it, the candidates the byte had, which are the zero alone past the zeros known. -/
  tok_cand : ∀ t ti, Γt !! t = some ti → ∃ f, st.file ti.ino = some f ∧
    ∀ b, inRange ti.lo ti.hi b = true → ∃ c0, f.cand b = c0 ++ [(ti.val b, ti.n)] ∧
      (∀ z, ti.m0.zf = some z → z ≤ b → c0 = [(0, 0)]) ∧
      ∀ c, ti.m0.size ≤ b → ti.m0.tc !! b = some c → c0 = c
  /-- A cut is at most the last change's number. -/
  cut_le : ∀ i m c, Γm !! i = some m → m.cut = some c → c ≤ st.fs.stamp

end derived

/-- The candidates `m` knows of byte `b` at or past the size: `tc`'s, or the zero, stamped 0, from
`zf` on. -/
def OsMeta.pc (m : OsMeta) (b : Nat) : Option Cands :=
  match m.tc !! b with
  | some c => some c
  | none => match m.zf with
    | some z => if z ≤ b then some [(0, 0)] else none
    | none => none

theorem OsMeta.pc_some {m : OsMeta} {b : Nat} {c : Cands} (h : m.pc b = some c) :
    m.tc !! b = some c ∨ ∃ z, m.zf = some z ∧ z ≤ b ∧ c = [(0, 0)] := by
  unfold OsMeta.pc at h
  split at h
  · rename_i c' hc'; cases h; exact .inl hc'
  · split at h
    · rename_i z hz
      by_cases hzb : z ≤ b
      · rw [if_pos hzb] at h; cases h; exact .inr ⟨z, hz, hzb, rfl⟩
      · rw [if_neg hzb] at h; cases h
    · cases h

/-- What `pc` knows is the file's candidates. -/
theorem MetaOk.pc_cand {st : OsState} {i : Ino} {m : OsMeta} {f : OsFile} (h : MetaOk st i m f)
    (b : Nat) (c : Cands) (hb : f.size ≤ b) (hc : m.pc b = some c) : f.cand b = c := by
  rcases OsMeta.pc_some hc with ht | ⟨z, hz, hzb, rfl⟩
  · exact h.tail b c hb ht
  · exact (h.zf z hz).2 b hzb

/-- The tree is well formed: the roots are; every prefix of the log replayed on the durable tree is
a tree over the roots, whose files are files of `files` and whose inodes are below `nextIno`; a
directory fd is on a directory of the tree now; no fd number is both a file's and a directory's;
every inode of `files` is below `nextIno`. -/
structure FsTreeWf (st : OsState) : Prop where
  roots : RootsOk st.fs.roots
  hist : ∀ n, n ≤ st.fs.metaLog.length →
    TreeWf st.fs.roots (replay ((st.fs.metaLog.take n).map (·.op)) st.fs.treeDur) ∧
    (∀ i, Named (replay ((st.fs.metaLog.take n).map (·.op)) st.fs.treeDur) i →
      ∃ f, st.fs.files !! i = some f) ∧
    (∀ j, j ∈ replay ((st.fs.metaLog.take n).map (·.op)) st.fs.treeDur → j < st.fs.nextIno)
  dfds : ∀ fd df, st.proc.dfds !! fd = some df → df.ino ∈ st.tree
  disj : ∀ fd, st.proc.fds !! fd ≠ none → st.proc.dfds !! fd = none
  files_lt : ∀ i, i ∈ st.fs.files → i < st.fs.nextIno

/-- `st'` is `st` after a step that leaves the tree alone: the tree's state, the directory fds, the
calls in flight and the inode counter are the same, every inode of `files` stays one, and a new fd
of a file is no directory fd. Every step of the extension but the tree's does this. -/
structure TreeFrame (st st' : OsState) : Prop where
  roots : st'.fs.roots = st.fs.roots
  treeDur : st'.fs.treeDur = st.fs.treeDur
  metaLog : st'.fs.metaLog = st.fs.metaLog
  committed : st'.fs.committed = st.fs.committed
  nextIno : st'.fs.nextIno = st.fs.nextIno
  dfds : st'.proc.dfds = st.proc.dfds
  calls : st'.proc.calls = st.proc.calls
  dom : ∀ i, i ∈ st'.fs.files ↔ i ∈ st.fs.files
  fds : ∀ fd, st'.proc.fds !! fd ≠ none → st.proc.fds !! fd ≠ none ∨ st.proc.dfds !! fd = none

theorem TreeFrame.tree {st st' : OsState} (h : TreeFrame st st') : st'.tree = st.tree := by
  simp [OsState.tree, h.treeDur, h.metaLog]

theorem TreeFrame.wf {st st' : OsState} (h : TreeFrame st st') (hw : FsTreeWf st) :
    FsTreeWf st' := by
  refine ⟨h.roots ▸ hw.roots, fun n hn => ?_, ?_, ?_, ?_⟩
  · rw [h.metaLog] at hn ⊢; rw [h.treeDur, h.roots, h.nextIno]
    obtain ⟨h1, h2, h3⟩ := hw.hist n hn
    refine ⟨h1, fun i hi => ?_, h3⟩
    obtain ⟨f, hf⟩ := h2 i hi
    have hm : i ∈ st'.fs.files := (h.dom i).2 (by rw [GMap.mem_iff, hf]; rfl)
    rw [GMap.mem_iff] at hm
    cases hf' : st'.fs.files !! i with
    | none => rw [hf'] at hm; cases hm
    | some f' => exact ⟨f', rfl⟩
  · intro fd df hdf; rw [h.dfds] at hdf; rw [h.tree]; exact hw.dfds fd df hdf
  · intro fd hfd; rw [h.dfds]
    rcases h.fds fd hfd with h' | h'
    · exact hw.disj fd h'
    · exact h'
  · intro i hi; rw [h.nextIno]; exact hw.files_lt i ((h.dom i).1 hi)

theorem TreeFrame.refl (st : OsState) : TreeFrame st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ h => Or.inl h⟩

theorem TreeFrame.trans {st st' st'' : OsState} (h1 : TreeFrame st st') (h2 : TreeFrame st' st'') :
    TreeFrame st st'' := by
  refine ⟨h2.roots.trans h1.roots, h2.treeDur.trans h1.treeDur, h2.metaLog.trans h1.metaLog,
    h2.committed.trans h1.committed, h2.nextIno.trans h1.nextIno, h2.dfds.trans h1.dfds,
    h2.calls.trans h1.calls, fun i => (h2.dom i).trans (h1.dom i), fun fd h => ?_⟩
  rcases h2.fds fd h with h' | h'
  · exact h1.fds fd h'
  · rw [h1.dfds] at h'; exact Or.inr h'

/-! ## The tree's ghost state -/

/-- A directory fd's read, the ghost state's and the state's, agree: begun on the entries `g.now`,
with the names returned `rs`. -/
def PhOk : DirPh → OsDirRead → Prop
  | .idle _ _, .idle => True
  | .done _ _, .done => True
  | .reading rs g _, .reading u s r =>
    ∀ b, u b = (decide (NameOk b) && (g.now !! b).isSome) ∧
      s b = (decide (NameOk b) && (g.now !! b).isSome) ∧ r b = decide (b ∈ rs)
  | _, _ => False

/-- The tree's ghost state mirrors its state: the history is the state's durable tree and log, the
log is sequential (the metadata calls of a verified program do not overlap: the specs take the whole
history), a ghost entry for every directory fd, on its directory, its read as the state's, and a
directory being read the view of the history (unchanged since the read began: a read holds a
fraction of the history); a ghost entry for every call on a path in flight, with its start and the
fraction of the history it holds (`callRes`), its start the log's length (the log changes only by a
step holding the whole history, when no other call can be in flight). -/
structure TreeCoh (st : OsState) (V : Hist) (Γdf : GMap w64 (Ino × DirPh))
    (Γc : GMap Nat (Nat × Qp)) : Prop where
  hist : V = (st.fs.treeDur, st.fs.metaLog)
  seq : Sequential st.fs.metaLog
  fds : ∀ fd, (Γdf !! fd).map (·.1) = (st.proc.dfds !! fd).map (·.ino)
  ph : ∀ fd x df, Γdf !! fd = some x → st.proc.dfds !! fd = some df → PhOk x.2 df.rd
  rd : ∀ fd x, Γdf !! fd = some x → x.2.g = dview V x.1
  calls : ∀ t, (Γc !! t).map (·.1) = st.proc.calls !! t
  start : ∀ t x, Γc !! t = some x → x.1 = st.fs.metaLog.length

/-- `TreeCoh` depends on the durable tree, the log, the directory fds and the calls only. -/
theorem TreeCoh.congr {st st' : OsState} {V Γdf Γc} (h : TreeCoh st V Γdf Γc)
    (hd : st'.fs.treeDur = st.fs.treeDur) (hl : st'.fs.metaLog = st.fs.metaLog)
    (hf : st'.proc.dfds = st.proc.dfds) (hc : st'.proc.calls = st.proc.calls) :
    TreeCoh st' V Γdf Γc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by rw [hd, hl]; exact h1, by rw [hl]; exact h2, ?_, ?_, h5, ?_, ?_⟩
  · intro fd; rw [hf]; exact h3 fd
  · intro fd x df hx hdf; rw [hf] at hdf; exact h4 fd x df hx hdf
  · intro t; rw [hc]; exact h6 t
  · intro t x hx; rw [hl]; exact h7 t x hx

theorem TreeFrame.coh {st st' : OsState} {V Γdf Γc} (h : TreeFrame st st')
    (hc : TreeCoh st V Γdf Γc) : TreeCoh st' V Γdf Γc :=
  hc.congr h.treeDur h.metaLog h.dfds h.calls

section cells
attribute [local instance] Classical.propDecidable

/-- What byte `b` of a mapping of the file of `i` shows: the file's byte, or nothing (a hole). -/
def cellByte (st : OsState) (i : Ino) (b : Nat) : Option w8 :=
  match st.file i with
  | some f => if h : b < f.contents.length then
      (if InflightAt st i b then none else some f.contents[b]) else none
  | none => none

/-- The value of a cell showing `ob`. -/
def toCellVal [GooseExts] : Option w8 → val
  | some b => LitV (LitByte b)
  | none => osHole

theorem cellVal_eq [GooseExts] [GoGlobalContext] (st : OsState) (i : Ino) (b : Nat) :
    cellVal st i b = toCellVal (cellByte st i b) := by
  unfold cellVal cellByte
  rcases st.file i with _ | f
  · rfl
  · dsimp only
    by_cases hb : b < f.contents.length
    · simp only [hb, ↓reduceDIte]
      by_cases hn : InflightAt st i b
      · simp only [hn, ↓reduceIte]; rfl
      · simp only [hn, ↓reduceIte]; rfl
    · simp only [hb, ↓reduceDIte]; rfl

/-- The cells of the mappings of `maps`. -/
def mapCells (maps : GMap Loc OsMap) : List Loc :=
  maps.toList.flatMap (fun bm => (List.range bm.2.len).map (fun (k : Nat) => bm.1 +ₗ (k : Int)))

theorem mem_mapCells {maps : GMap Loc OsMap} {l : Loc} :
    l ∈ mapCells maps ↔ ∃ b m k, maps !! b = some m ∧ k < m.len ∧ l = b +ₗ (k : Int) := by
  simp only [mapCells, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨b, m⟩, hbm, k, hk, rfl⟩
    exact ⟨b, m, k, (GMap.mem_toList _ _ _).1 hbm, hk, rfl⟩
  · rintro ⟨b, m, k, hbm, hk, rfl⟩
    exact ⟨⟨b, m⟩, (GMap.mem_toList _ _ _).2 hbm, k, hk, rfl⟩

/-- What each mapped cell shows, and whether the extension holds all of it (while an in-flight
change may change it). -/
def cellView (st : OsState) : GMap Loc (Option w8 × Bool) :=
  ⟨fun l => if h : Mapped st l then
      some (cellByte st h.choose h.choose_spec.choose,
        decide (InflightAt st h.choose h.choose_spec.choose))
    else none,
   ⟨mapCells st.proc.maps, fun l hl => by
      by_cases h : Mapped st l
      · obtain ⟨i, k, b, m, hm, -, hk, rfl⟩ := h
        exact mem_mapCells.2 ⟨b, m, k, hm, hk, rfl⟩
      · simp [h] at hl⟩⟩

theorem mapsTo_unique {st : OsState} (hwf : OsWf st) {l : Loc} {i i' : Ino} {k k' : Nat}
    (h : MapsTo st l i k) (h' : MapsTo st l i' k') : i = i' ∧ k = k' := by
  obtain ⟨b, m, hm, rfl, hk, rfl⟩ := h
  obtain ⟨b', m', hm', rfl, hk', he⟩ := h'
  by_cases hb : b = b'
  · subst hb; rw [hm] at hm'; cases hm'
    have := loc_add_inj _ he; exact ⟨rfl, by omega⟩
  · exfalso
    have hd := hwf.maps_disj b m b' m' hm hm' hb
    have : b.addr + k = b'.addr + k' := by simpa [Loc.add] using congrArg Loc.addr he
    omega

theorem cellView_mapsTo {st : OsState} (hwf : OsWf st) {l : Loc} {i : Ino} {k : Nat}
    (h : MapsTo st l i k) :
    cellView st !! l = some (cellByte st i k, decide (InflightAt st i k)) := by
  have hm : Mapped st l := ⟨i, k, h⟩
  show (if h : Mapped st l then _ else _) = _
  rw [dite_eq_left_of_eq_true (eq_true hm)]
  obtain ⟨rfl, rfl⟩ := mapsTo_unique hwf hm.choose_spec.choose_spec h
  rfl

theorem cellView_none {st : OsState} {l : Loc} (h : ¬ Mapped st l) : cellView st !! l = none := by
  show (if h : Mapped st l then _ else _) = _
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem cellView_some {st : OsState} (hwf : OsWf st) {l : Loc} {x : Option w8 × Bool}
    (h : cellView st !! l = some x) :
    ∃ i k, MapsTo st l i k ∧ x = (cellByte st i k, decide (InflightAt st i k)) := by
  by_cases hm : Mapped st l
  · obtain ⟨i, k, hik⟩ := hm
    rw [cellView_mapsTo hwf hik] at h; cases h; exact ⟨i, k, hik, rfl⟩
  · rw [cellView_none hm] at h; cases h

theorem cellView_of_maps_empty {st : OsState} (h : st.proc.maps = ∅) : cellView st = ∅ := by
  apply GMap.ext; intro l
  rw [cellView_none]
  · rfl
  · rintro ⟨i, k, b, m, hm, -⟩; simp [h] at hm

end cells

/-! ## The ghost state -/

/-- What the adequacy theorem provides. -/
class OsGpreS (GF : BundledGFunctors) where
  osPreAllG : AllG GF

/-- The ghost names of the extension: the files' four maps (bytes, files, fds, in-flight changes),
the variable that ties the mapped cells' view to the invariant, and the tree's: its history (a map
of one entry), the directory fds, the calls in flight. -/
structure OsGS (GF : BundledGFunctors) where
  osAllG : AllG GF
  γb : GName
  γm : GName
  γf : GName
  γt : GName
  γv : GName
  γd : GName
  γdf : GName
  γc : GName
  /-- A lower bound on the committed prefix of the tree's log (`commitRes`). -/
  γcm : GName
  /-- The shared mode's (`notes/wal-fsext-i2-design.md`, §2): its history (a map of one entry,
  `Unit ↦ Roots × Hist`), its directory fds (`w64 ↦ Ino × DirPhS`), its calls in flight
  (`Nat ↦ Nat × Qp`), the call permission (`Unit ↦ Unit`, fractional), the name claims
  (`Ino × NameSet ↦ NamesH`), the log's length (a mono nat) and its entries (`Nat ↦ LogEntry`,
  persistent). Allocated at boot, used from the mode switch on. -/
  γs : GName
  γdfS : GName
  γcS : GName
  γperm : GName
  γn : GName
  γlen : GName
  γlog : GName

/-! ### The ghost maps of a ghost state `hL`, with the `AllG` of `hL` -/

section wrappers
variable {GF : BundledGFunctors} (hL : OsGS GF)
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- The authoritative map `m` of the ghost map `γ` of `hL`. -/
def gAuth (γ : GName) (m : GMap K V) : IProp GF :=
  letI := hL.osAllG; ghostMapAuth γ 1 m

/-- The entry `k ↦ v` of the ghost map `γ` of `hL`. -/
def gElem (γ : GName) (k : K) (dq : DFrac) (v : V) : IProp GF :=
  letI := hL.osAllG; ghostMapElem γ k dq v

/-- The ghost variable of the cells' view. -/
def gVar (q : Qp) (a : GMap Loc (Option w8 × Bool) × Nat) : IProp GF :=
  letI := hL.osAllG; ghostVar hL.γv q a

instance gElem_timeless (γ : GName) (k : K) (dq : DFrac) (v : V) :
    Timeless (gElem (K := K) (V := V) hL γ k dq v) := by
  unfold gElem; letI := hL.osAllG; infer_instance

instance gAuth_timeless (γ : GName) (m : GMap K V) : Timeless (gAuth hL γ m) := by
  unfold gAuth; letI := hL.osAllG; infer_instance

instance gVar_timeless (q : Qp) (a : GMap Loc (Option w8 × Bool) × Nat) :
    Timeless (gVar hL q a) := by
  unfold gVar; letI := hL.osAllG; infer_instance

theorem gAuth_lookup (γ : GName) (m : GMap K V) (k : K) (dq : DFrac) (v : V) :
    ⊢ gAuth hL γ m -∗ gElem hL γ k dq v -∗ ⌜m !! k = some v⌝ := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_lookup

theorem gAuth_update (γ : GName) (m : GMap K V) (k : K) (v w : V) :
    ⊢ gAuth hL γ m -∗ gElem hL γ k (DFrac.own 1) v ==∗
      gAuth hL γ (<[k := w]> m) ∗ gElem hL γ k (DFrac.own 1) w := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_update w

theorem gAuth_insert (γ : GName) (m : GMap K V) (k : K) (v : V) (h : m !! k = none) :
    ⊢ gAuth hL γ m ==∗ gAuth hL γ (<[k := v]> m) ∗ gElem hL γ k (DFrac.own 1) v := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_insert k v h

theorem gAuth_delete (γ : GName) (m : GMap K V) (k : K) (v : V) :
    ⊢ gAuth hL γ m -∗ gElem hL γ k (DFrac.own 1) v ==∗ gAuth hL γ (GMap.delete k m) := by
  unfold gAuth gElem; letI := hL.osAllG
  exact ghost_map_delete

theorem gElem_valid_2 (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢ gElem hL γ k dq1 v1 -∗ gElem hL γ k dq2 v2 -∗ ⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ := by
  unfold gElem; letI := hL.osAllG
  exact ghostMapElem_valid_2 k γ dq1 dq2 v1 v2

theorem gElem_valid (γ : GName) (k : K) (dq : DFrac) (v : V) :
    ⊢ gElem hL γ k dq v -∗ ⌜✓ dq⌝ := by
  unfold gElem; letI := hL.osAllG
  exact ghostMapElem_valid k γ dq v

theorem gElem_split (γ : GName) (k : K) (q1 q2 : Qp) (v : V) :
    gElem hL γ k (DFrac.own (q1 + q2)) v ⊣⊢ gElem hL γ k (DFrac.own q1) v ∗ gElem hL γ k (DFrac.own q2) v := by
  unfold gElem; letI := hL.osAllG
  exact (ghostMapElem_fractional k γ v).fractional q1 q2

theorem gVar_agree (q1 q2 : Qp) (a1 a2 : GMap Loc (Option w8 × Bool) × Nat) :
    ⊢ gVar hL q1 a1 -∗ gVar hL q2 a2 -∗ ⌜a1 = a2⌝ := by
  unfold gVar; letI := hL.osAllG
  exact ghostVar_agree _ _ _ _ _

theorem gVar_update (a1 a2 b : GMap Loc (Option w8 × Bool) × Nat) :
    ⊢ gVar hL (1 : Qp).half a1 -∗ gVar hL (1 : Qp).half a2 ==∗
      gVar hL (1 : Qp).half b ∗ gVar hL (1 : Qp).half b := by
  unfold gVar; letI := hL.osAllG
  exact ghostVar_update_halves _ _ _ _

end wrappers

/-! ### Runs of bytes -/

section bytes
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The bytes `xs` of the file `i` from `off` on. -/
def bytesG (i : Ino) (off : Nat) (dq : DFrac) (xs : List (ByteG)) : IProp GF :=
  [∗list] k ↦ x ∈ xs, gElem hL hL.γb (i, off + k) dq x

instance bytesG_timeless (i : Ino) (off : Nat) (dq : DFrac) (xs : List (ByteG)) :
    Timeless (bytesG hL i off dq xs) := by
  unfold bytesG; infer_instance

theorem bytesG_nil (i : Ino) (off : Nat) (dq : DFrac) :
    bytesG hL i off dq [] ⊣⊢ emp := .rfl

theorem bytesG_cons (i : Ino) (off : Nat) (dq : DFrac) (x : ByteG)
    (xs : List (ByteG)) :
    bytesG hL i off dq (x :: xs) ⊣⊢ gElem hL hL.γb (i, off) dq x ∗ bytesG hL i (off + 1) dq xs := by
  unfold bytesG
  refine BigSepL.bigSepL_cons.trans ?_
  rw [Nat.add_zero]
  refine sep_congr .rfl (.of_eq ?_)
  apply BigSepL.bigSepL_eq_of_forall_eq
  intro k _
  rw [show off + (k + 1) = off + 1 + k by omega]

theorem bytesG_append (i : Ino) (dq : DFrac) :
    ∀ (off : Nat) (xs ys : List (ByteG)),
    bytesG hL i off dq (xs ++ ys) ⊣⊢ bytesG hL i off dq xs ∗ bytesG hL i (off + xs.length) dq ys
  | off, [], ys => by
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    exact ⟨by iintro H; iframe; iempintro, by iintro ⟨-, H⟩; iexact H⟩
  | off, x :: xs, ys => by
    refine (bytesG_cons hL i off dq x (xs ++ ys)).trans ?_
    refine (sep_congr .rfl (bytesG_append i dq (off + 1) xs ys)).trans ?_
    rw [show off + 1 + xs.length = off + (x :: xs).length by simp; omega]
    refine BIBase.BiEntails.trans ?_ (sep_congr (bytesG_cons hL i off dq x xs).symm .rfl)
    exact ⟨by iintro ⟨H1, H2, H3⟩; iframe, by iintro ⟨⟨H1, H2⟩, H3⟩; iframe⟩

/-- `m` with the bytes `ys` from `off` on. -/
def insertBytes (i : Ino) : Nat → List (ByteG) → GMap (Ino × Nat) (ByteG) →
    GMap (Ino × Nat) (ByteG)
  | _, [], m => m
  | off, y :: ys, m => insertBytes i (off + 1) ys (<[(i, off) := y]> m)

theorem lookup_insertBytes (i : Ino) : ∀ (off : Nat) (ys : List (ByteG))
    (m : GMap (Ino × Nat) (ByteG)) (q : Ino) (j : Nat),
    insertBytes i off ys m !! (q, j) =
      if q = i ∧ off ≤ j ∧ j < off + ys.length then ys[j - off]? else m !! (q, j)
  | off, [], m, q, j => by simp [insertBytes]; intros; omega
  | off, y :: ys, m, q, j => by
    simp only [insertBytes, lookup_insertBytes i (off + 1) ys, GMap.lookup_insert_eq_iff,
      Prod.mk.injEq, List.length_cons]
    by_cases hq : q = i
    · subst hq
      by_cases hj : j = off
      · subst hj; simp; intro h; omega
      · by_cases h1 : off + 1 ≤ j ∧ j < off + 1 + ys.length
        · rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, by omega, by omega⟩]
          rw [show j - off = (j - (off + 1)) + 1 by omega]; simp
        · rw [if_neg (fun h => h1 h.2), if_neg (fun h => hj (Eq.symm h.2))]
          rw [if_neg (fun h => by omega)]
    · simp [hq, Ne.symm hq]

theorem bytesG_update (i : Ino) : ∀ (off : Nat) (xs ys : List (ByteG))
    (Γb : GMap (Ino × Nat) (ByteG)), ys.length = xs.length →
    gAuth hL hL.γb Γb ∗ bytesG hL i off (DFrac.own 1) xs ⊢
      |==> (gAuth hL hL.γb (insertBytes i off ys Γb) ∗ bytesG hL i off (DFrac.own 1) ys)
  | off, [], [], Γb, _ => by
    simp only [insertBytes]
    iintro ⟨H, -⟩; imodintro; iframe; iapply (bytesG_nil hL i off _).2; iempintro
  | off, x :: xs, y :: ys, Γb, hl => by
    simp only [insertBytes]
    iintro ⟨H, Hb⟩
    icases (bytesG_cons hL i off _ x xs).1 $$ Hb with ⟨Hx, Hxs⟩
    imod gAuth_update hL _ _ _ _ y $$ H Hx with ⟨H, Hy⟩
    imod bytesG_update i (off + 1) xs ys _ (by simpa using hl) $$ [H Hxs] with ⟨H, Hys⟩
    · iframe
    imodintro
    iframe H
    iapply (bytesG_cons hL i off _ y ys).2
    iframe
  | _, [], _ :: _, _, hl => by simp at hl
  | _, _ :: _, [], _, hl => by simp at hl

theorem bytesG_alloc (i : Ino) : ∀ (off : Nat) (ys : List (ByteG))
    (Γb : GMap (Ino × Nat) (ByteG)), (∀ k, k < ys.length → Γb !! (i, off + k) = none) →
    gAuth hL hL.γb Γb ⊢
      |==> (gAuth hL hL.γb (insertBytes i off ys Γb) ∗ bytesG hL i off (DFrac.own 1) ys)
  | off, [], Γb, _ => by
    simp only [insertBytes]
    iintro H; imodintro; iframe; iapply (bytesG_nil hL i off _).2; iempintro
  | off, y :: ys, Γb, hfree => by
    simp only [insertBytes]
    iintro H
    imod gAuth_insert hL _ _ (i, off) y (by simpa using hfree 0 (by simp)) $$ H with ⟨H, Hy⟩
    imod bytesG_alloc i (off + 1) ys _ (fun k hk => by
        rw [GMap.lookup_insert_ne _ _ (by simp; omega)]
        · rw [show off + 1 + k = off + (k + 1) by omega]; exact hfree (k + 1) (by simp; omega))
      $$ H with ⟨H, Hys⟩
    imodintro
    iframe H
    iapply (bytesG_cons hL i off _ y ys).2
    iframe

/-- `m` without the bytes `[off, off + n)` of `i`. -/
def deleteBytes (i : Ino) : Nat → Nat → GMap (Ino × Nat) (ByteG) →
    GMap (Ino × Nat) (ByteG)
  | _, 0, m => m
  | off, n + 1, m => deleteBytes i (off + 1) n (GMap.delete (i, off) m)

theorem lookup_deleteBytes (i : Ino) : ∀ (off n : Nat)
    (m : GMap (Ino × Nat) (ByteG)) (q : Ino) (j : Nat),
    deleteBytes i off n m !! (q, j) = if q = i ∧ off ≤ j ∧ j < off + n then none else m !! (q, j)
  | off, 0, m, q, j => by simp [deleteBytes]; intros; omega
  | off, n + 1, m, q, j => by
    simp only [deleteBytes, lookup_deleteBytes i (off + 1) n, GMap.lookup_delete_iff,
      Prod.mk.injEq]
    by_cases hq : q = i
    · subst hq
      by_cases hj : j = off
      · subst hj; simp
      · by_cases h1 : off + 1 ≤ j ∧ j < off + 1 + n
        · rw [if_pos ⟨rfl, h1⟩, if_pos ⟨rfl, by omega, by omega⟩]
        · rw [if_neg (fun h => h1 h.2), if_neg (fun h => hj (Eq.symm h.2)),
            if_neg (fun h => by omega)]
    · simp [hq, Ne.symm hq]

theorem bytesG_delete (i : Ino) : ∀ (off : Nat) (xs : List (ByteG))
    (Γb : GMap (Ino × Nat) (ByteG)),
    gAuth hL hL.γb Γb ∗ bytesG hL i off (DFrac.own 1) xs ⊢
      |==> gAuth hL hL.γb (deleteBytes i off xs.length Γb)
  | off, [], Γb => by simp only [List.length_nil, deleteBytes]; iintro ⟨H, -⟩; imodintro; iexact H
  | off, x :: xs, Γb => by
    simp only [List.length_cons, deleteBytes]
    iintro ⟨H, Hb⟩
    icases (bytesG_cons hL i off _ x xs).1 $$ Hb with ⟨Hx, Hxs⟩
    imod gAuth_delete hL _ _ _ _ $$ H Hx with H
    iapply bytesG_delete i (off + 1) xs _
    iframe

theorem bytesG_lookup (i : Ino) (off : Nat) (dq : DFrac) (xs : List (ByteG))
    (Γb : GMap (Ino × Nat) (ByteG)) :
    ⊢ gAuth hL hL.γb Γb -∗ bytesG hL i off dq xs -∗
      ⌜∀ k (hk : k < xs.length), Γb !! (i, off + k) = some xs[k]⌝ := by
  iintro HA Hbs
  iapply pure_forall.2; iintro %k
  iapply pure_forall.2; iintro %hk
  unfold bytesG
  icases BigSepL.bigSepL_lookup (Φ := fun k (x : ByteG) => gElem hL hL.γb (i, off + k) dq x)
    (List.getElem?_eq_getElem hk) $$ Hbs with Hb
  iapply gAuth_lookup $$ HA Hb

theorem bytesG_lookup_runs (i : Ino) (Γb : GMap (Ino × Nat) ByteG) :
    ∀ rs : List (Nat × DFrac × List ByteG),
    ⊢ gAuth hL hL.γb Γb -∗ ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) -∗
      ⌜∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (i, r.1 + k) = some r.2.2[k]⌝
  | [] => by
    iintro _ _
    ipureintro
    intro r hr; cases hr
  | r :: rs => by
    iintro HA Hrs
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    icases bytesG_lookup hL i r.1 r.2.1 r.2.2 Γb $$ HA Hr with %h1
    icases bytesG_lookup_runs i Γb rs $$ HA Hrs with %h2
    ipureintro
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | h
    · exact h1
    · exact h2 r' h

end bytes

/-! ## The start -/

/-- The candidates of the bytes of `f` past its size in its size's last page. -/
def tailMap (f : OsFile) : GMap Nat Cands :=
  ⟨fun b => if f.size ≤ b ∧ b < pageUp f.size then some (f.cand b) else none,
   ⟨List.range (pageUp f.size), fun k h => by
     by_cases hk : f.size ≤ k ∧ k < pageUp f.size
     · exact List.mem_range.2 hk.2
     · simp [hk] at h⟩⟩

theorem tailMap_lookup (f : OsFile) (b : Nat) :
    tailMap f !! b = if f.size ≤ b ∧ b < pageUp f.size then some (f.cand b) else none := rfl

/-- What `tailMap` records is the file's candidates. -/
theorem tailMap_cand (f : OsFile) (b : Nat) (c : Cands) (h : tailMap f !! b = some c) :
    f.cand b = c := by
  rw [tailMap_lookup] at h
  split at h
  · cases h; rfl
  · cases h

/-- The ghost `OsMeta` of a file as on disk: all of it durable, zeros past its last page (durable
zeros), and the candidates of the bytes past its size in its last page (`tailMap`). -/
def initMeta (f : OsFile) : OsMeta :=
  ⟨f.size, f.size, f.size, ∅, 0, 0, some (pageUp f.size), tailMap f, none⟩

/-- The bytes of the files of `st`, each as the state has it. -/
def bytesMapF (F : GMap Ino OsFile) : GMap (Ino × Nat) ByteG :=
  ⟨fun k => (F !! k.1).bind (fun f => if k.2 < f.size then some (f.cache k.2, f.cand k.2) else none),
   ⟨F.toList.flatMap (fun pf => (List.range pf.2.size).map (fun b => (pf.1, b))),
    fun ⟨i, b⟩ h => by
      simp only [List.mem_flatMap]
      cases hf : F !! i with
      | none => simp [hf] at h
      | some f =>
        simp only [hf, Option.bind_some] at h
        refine ⟨⟨i, f⟩, (GMap.mem_toList _ _ _).2 hf, ?_⟩
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
        split at h
        · exact ⟨b, by assumption, by simp⟩
        · simp at h⟩⟩

theorem bytesMapF_lookup (F : GMap Ino OsFile) (i : Ino) (b : Nat) :
    bytesMapF F !! (i, b) = (F !! i).bind (fun f => if b < f.size then some (f.cache b, f.cand b) else none) :=
  rfl

/-- The bytes of the files of `st`. -/
def bytesMap (st : OsState) : GMap (Ino × Nat) ByteG := bytesMapF st.fs.files

/-- The files of `st`, as on disk. -/
def metaMap (st : OsState) : GMap Ino OsMeta := GMap.fmap initMeta st.fs.files

section ghost
variable {GF : BundledGFunctors}

/-- What the state interpretation holds for each change in flight: its file's `OsMeta`, whole, and
the bytes below the size it announced. -/
def tokRes (hL : OsGS GF) (Γt : GMap Nat TokInfo) : IProp GF :=
  iprop([∗map] _t ↦ ti ∈ Γt,
    gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗ bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved)

/-- What the state interpretation holds of each directory fd: the fraction of the history its open
took, so that no one changes the directory while it is open. -/
def rdPart (hL : OsGS GF) (x : Ino × DirPh) : IProp GF :=
  iprop(∃ RV : Roots × Hist, gElem hL hL.γd () (DFrac.own x.2.q) RV ∗ ⌜x.2.g = dview RV.2 x.1⌝)

def rdRes (hL : OsGS GF) (Γdf : GMap w64 (Ino × DirPh)) : IProp GF :=
  iprop([∗map] _fd ↦ x ∈ Γdf, rdPart hL x)

/-- What the state interpretation holds of each call on a path in flight: the fraction of the
history its `CallBegin` took, so that no one changes the tree while it is in flight (and the holder
of the rest of the history knows that no other call is). -/
def callRes (hL : OsGS GF) (Γc : GMap Nat (Nat × Qp)) : IProp GF :=
  iprop([∗map] _t ↦ x ∈ Γc, ∃ RV : Roots × Hist, gElem hL hL.γd () (DFrac.own x.2) RV)

/-- The authoritative lower bound `c` on the committed prefix of the tree's log. -/
def gCommit (hL : OsGS GF) (c : Nat) : IProp GF :=
  letI := hL.osAllG; monoNatAuthOwn hL.γcm 1 c

/-- A lower bound `n` on the committed prefix of the tree's log (persistent). -/
def gCommitLb (hL : OsGS GF) (n : Nat) : IProp GF :=
  letI := hL.osAllG; monoNatLbOwn hL.γcm n

instance gCommitLb_persistent (hL : OsGS GF) (n : Nat) : Persistent (gCommitLb hL n) := by
  unfold gCommitLb; letI := hL.osAllG; infer_instance

instance gCommitLb_timeless (hL : OsGS GF) (n : Nat) : Timeless (gCommitLb hL n) := by
  unfold gCommitLb; letI := hL.osAllG; infer_instance

instance gCommit_timeless (hL : OsGS GF) (n : Nat) : Timeless (gCommit hL n) := by
  unfold gCommit; letI := hL.osAllG; infer_instance

/-- What the state interpretation holds of the committed entries of the tree's log: the
authoritative lower bound `c` on them, every entry below `c` committed (`DirSync` raises it; a step
never uncommits an entry, `fsStep_commitGrows`). -/
def commitRes (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ c : Nat, ⌜∀ y, y < c → st.fs.committed y⌝ ∗ gCommit hL c)

theorem commitRes_grow (hL : OsGS GF) {st st' : OsState} (h : CommitGrows st st') :
    commitRes hL st ⊢ commitRes hL st' := by
  unfold commitRes
  iintro ⟨%c, %hc, H⟩
  iexists c
  iframe H
  ipureintro; exact fun y hy => h y (hc y hy)

/-- The lower bound held, with the authoritative one: below it. -/
theorem gCommitLb_valid (hL : OsGS GF) (c n : Nat) :
    ⊢ gCommit hL c -∗ gCommitLb hL n -∗ ⌜n ≤ c⌝ := by
  unfold gCommit gCommitLb
  letI := hL.osAllG
  iintro H1 H2
  icases monoNatLbOwn_valid _ _ _ _ $$ H1 H2 with %h
  ipureintro; exact h.2

/-- The authoritative lower bound raised, with a lower bound of the new value. -/
theorem gCommit_update (hL : OsGS GF) (c c' : Nat) (h : c ≤ c') :
    ⊢ gCommit hL c ==∗ gCommit hL c' ∗ gCommitLb hL c' := by
  unfold gCommit gCommitLb
  letI := hL.osAllG
  iapply mono_nat_own_update c' h

/-- A lower bound weakened. -/
theorem gCommitLb_le (hL : OsGS GF) {n : Nat} (n' : Nat) (h : n' ≤ n) :
    ⊢ gCommitLb hL n -∗ gCommitLb hL n' := by
  unfold gCommitLb
  letI := hL.osAllG
  iapply monoNatLbOwn_le n' h

/-- The tree's roots and history, as a ghost map of one entry. -/
def histMap (RV : Roots × Hist) : GMap Unit (Roots × Hist) := {[() := RV]}

/-- What the state interpretation holds, in the legacy mode, of the shared mode's ghost state
(`notes/wal-fsext-i2-design.md`, §2.1, review M3): its authorities, empty (the log's length `0`),
and the whole call permission. So no resource of the shared mode exists in the legacy mode. -/
def legacyHolds (hL : OsGS GF) : IProp GF :=
  iprop(gAuth hL hL.γs (∅ : GMap Unit (Roots × Hist)) ∗
    gAuth hL hL.γdfS (∅ : GMap w64 (Ino × DirPhS)) ∗ gAuth hL hL.γcS (∅ : GMap Nat (Nat × Qp)) ∗
    gElem hL hL.γperm () (DFrac.own 1) () ∗ gAuth hL hL.γn (∅ : GMap (Ino × NameSet) NamesH) ∗
    (letI := hL.osAllG; monoNatAuthOwn hL.γlen 1 0) ∗ gAuth hL hL.γlog (∅ : GMap Nat LogEntry))

/-- What the state interpretation holds, in the shared mode, of each call on a path in flight:
the fraction of the call permission its `CallBegin` took. -/
def callResS (hL : OsGS GF) (Γc : GMap Nat (Nat × Qp)) : IProp GF :=
  iprop([∗map] _t ↦ x ∈ Γc, gElem hL hL.γperm () (DFrac.own x.2) ())

/-- A shared directory fd's read, the ghost state's and the state's, agree: not begun, done, or
begun when the log had `r0` entries, the names of `N` returned `rs`; while no entry from `r0` on
wrote a name of `N` in the directory `j`, those names are as the state's read has them; every name
the read has seen is valid. -/
def PhOkS (st : OsState) (j : Ino) : DirPhS → OsDirRead → Prop
  | .idle, .idle => True
  | .done, .done => True
  | .reading N r0 rs, .reading u s r =>
    r0 ≤ st.fs.metaLog.length ∧ (∀ b, s b = true → NameOk b) ∧
    ((∀ x (e : LogEntry), r0 ≤ x → st.fs.metaLog[x]? = some e → ∀ b, N.Mem b → ¬ e.op.Writes j b) →
      ∀ b, N.Mem b → u b = present st j b ∧ s b = present st j b ∧ r b = decide (b ∈ rs))
  | _, _ => False

/-- The tree's ghost state, in the shared mode, mirrors its state (the design's `TreeCohS`): the
log's disciplines (`TreeCut.lean`; the legacy prefix below `s0` exempt), a ghost entry for every
directory fd and every call on a path in flight; a call began no later than now, a call holding the
whole permission began now, and every call began after every directory operation and every entry
of the legacy prefix. -/
structure TreeCohS (st : OsState) (s0 : Nat) (Γdf : GMap w64 (Ino × DirPhS))
    (Γc : GMap Nat (Nat × Qp)) : Prop where
  starts : Starts st.fs.metaLog
  pss : PerSlotSeq st.fs.metaLog
  dox : DirOpExcl st.fs.metaLog s0
  valid : LogValid st.fs.treeDur st.fs.metaLog s0
  s0le : s0 ≤ st.fs.metaLog.length
  fds : ∀ fd, (Γdf !! fd).map (·.1) = (st.proc.dfds !! fd).map (·.ino)
  ph : ∀ fd x df, Γdf !! fd = some x → st.proc.dfds !! fd = some df → PhOkS st x.1 x.2 df.rd
  calls : ∀ t, (Γc !! t).map (·.1) = st.proc.calls !! t
  callsLe : ∀ t x, Γc !! t = some x → x.1 ≤ st.fs.metaLog.length
  whole : ∀ t x, Γc !! t = some x → x.2 = 1 → x.1 = st.fs.metaLog.length
  after : ∀ t x, Γc !! t = some x → ∀ y (ey : LogEntry), st.fs.metaLog[y]? = some ey →
    (ey.op.IsDirOp ∨ y < s0) → y < x.1

/-- The interpretation of the tree of `st` in the legacy mode: the whole-history logic's, and the
shared mode's authorities, empty (`legacyHolds`). -/
def treeLegacy (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (V : Hist) (Γdf : GMap w64 (Ino × DirPh)) (Γc : GMap Nat (Nat × Qp)),
    ⌜FsTreeWf st ∧ TreeCoh st V Γdf Γc⌝ ∗ gAuth hL hL.γd (histMap (st.fs.roots, V)) ∗
    gAuth hL hL.γdf Γdf ∗
    gAuth hL hL.γc Γc ∗ rdRes hL Γdf ∗ callRes hL Γc ∗ legacyHolds hL)

/-- The interpretation of the tree of `st` in the shared mode, begun when the log had `s0`
entries: the legacy history frozen at `V0` and held whole, no legacy directory fd or call (so no
legacy resource exists); the shared history's authority (the state's), its directory fds and calls,
and the call permission's fractions of the calls in flight. -/
def treeShared (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (V0 : Hist) (s0 : Nat) (Γdf : GMap w64 (Ino × DirPhS)) (Γc : GMap Nat (Nat × Qp)),
    ⌜FsTreeWf st ∧ TreeCohS st s0 Γdf Γc⌝ ∗
    gAuth hL hL.γd (histMap (st.fs.roots, V0)) ∗ gElem hL hL.γd () (DFrac.own 1) (st.fs.roots, V0) ∗
    gAuth hL hL.γdf (∅ : GMap w64 (Ino × DirPh)) ∗ gAuth hL hL.γc (∅ : GMap Nat (Nat × Qp)) ∗
    gAuth hL hL.γs (histMap (st.fs.roots, ((st.fs.treeDur, st.fs.metaLog) : Hist))) ∗
    gAuth hL hL.γdfS Γdf ∗ gAuth hL hL.γcS Γc ∗ callResS hL Γc)

/-- The interpretation of the tree of `st`: in the legacy mode or in the shared mode, and the
committed prefix's bound (both modes'). -/
def treeCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop((treeLegacy hL st ∨ treeShared hL st) ∗ commitRes hL st)

/-- `PhOkS` depends on the durable tree and the log only. -/
theorem PhOkS.congr {st st' : OsState} {j : Ino} {x : DirPhS} {r : OsDirRead} (h : PhOkS st j x r)
    (hd : st'.fs.treeDur = st.fs.treeDur) (hl : st'.fs.metaLog = st.fs.metaLog) :
    PhOkS st' j x r := by
  have hp : ∀ b, present st' j b = present st j b := by
    intro b; simp [present, OsState.tree, hd, hl]
  cases x <;> cases r <;> simp only [PhOkS] at h ⊢
  refine ⟨hl ▸ h.1, h.2.1, fun hn b hb => ?_⟩
  simp only [hp]
  exact h.2.2 (fun x e hx he => hn x e hx (hl ▸ he)) b hb

/-- `TreeCohS` depends on the durable tree, the log, the directory fds and the calls only. -/
theorem TreeCohS.congr {st st' : OsState} {s0 Γdf Γc} (h : TreeCohS st s0 Γdf Γc)
    (hd : st'.fs.treeDur = st.fs.treeDur) (hl : st'.fs.metaLog = st.fs.metaLog)
    (hf : st'.proc.dfds = st.proc.dfds) (hc : st'.proc.calls = st.proc.calls) :
    TreeCohS st' s0 Γdf Γc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨hl ▸ h1, hl ▸ h2, hl ▸ h3, by rw [hd, hl]; exact h4, hl ▸ h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fd; rw [hf]; exact h6 fd
  · intro fd x df hx hdf; rw [hf] at hdf; exact (h7 fd x df hx hdf).congr hd hl
  · intro t; rw [hc]; exact h8 t
  · intro t x hx; rw [hl]; exact h9 t x hx
  · intro t x hx hq; rw [hl]; exact h10 t x hx hq
  · intro t x hx y ey hy; rw [hl] at hy; exact h11 t x hx y ey hy

/-- A step that leaves the tree alone keeps its interpretation, in either mode. -/
theorem treeCtx_frame (hL : OsGS GF) {st st' : OsState} (h : TreeFrame st st') :
    treeCtx hL st ⊢ treeCtx hL st' := by
  unfold treeCtx treeLegacy treeShared
  iintro ⟨Hm, Hcm⟩
  isplitl [Hm]
  · icases Hm with (⟨%V, %Γdf, %Γc, %hw, Had, Haf, Hac, Hrd, Hcr, Hlh⟩ |
      ⟨%V0, %s0, %Γdf, %Γc, %hw, Had, Hd, Haf, Hac, Has, Hadf, Hacs, Hcr⟩)
    · ileft
      iexists V, Γdf, Γc
      rw [h.roots]
      iframe Had Haf Hac Hrd Hcr Hlh
      ipureintro
      exact ⟨h.wf hw.1, h.coh hw.2⟩
    · iright
      iexists V0, s0, Γdf, Γc
      rw [h.roots, h.treeDur, h.metaLog]
      iframe Had Hd Haf Hac Has Hadf Hacs Hcr
      ipureintro
      exact ⟨h.wf hw.1, hw.2.congr h.treeDur h.metaLog h.dfds h.calls⟩
  · iapply commitRes_grow hL (commitGrows_of_eq h.committed) $$ Hcm

/-- The start resources of the tree: its history, whole (nothing logged on the tree it starts
with). -/
def treeStart (hL : OsGS GF) (st : OsState) : IProp GF :=
  gElem hL hL.γd () (DFrac.own 1) ((st.fs.roots, ((st.fs.treeDur, ([] : List LogEntry)) : Hist)) :
    Roots × Hist)

/-- The interpretation of the files of `st`. -/
def osCtxF (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta)
      (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    ⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗ gAuth hL hL.γf Γf ∗ gAuth hL hL.γt Γt ∗
    tokRes hL Γt ∗
    gVar hL (1 : Qp).half (cellView st, GMap.size st.proc.inflight))

/-- The interpretation of the state `st`: its files and its tree. -/
def osCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(osCtxF hL st ∗ treeCtx hL st)

/-- The start resources for a state with no fd, change or mapping: every file and byte, whole, and
the half of the cells' view that the invariant takes (`osInv_alloc`). -/
def osStartF (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(([∗map] k ↦ x ∈ bytesMap st, gElem hL hL.γb k (DFrac.own 1) x) ∗
    ([∗map] i ↦ m ∈ metaMap st, gElem hL hL.γm i (DFrac.own 1) m) ∗
    gVar hL (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0))

/-- The start resources: the files' and the tree's. -/
def osStart (hL : OsGS GF) (st : OsState) : IProp GF := iprop(osStartF hL st ∗ treeStart hL st)

end ghost

theorem ofDisk_cand_lt (img : Nat → w8) (sz b : Nat) (hb : b < sz) :
    (OsFile.ofDisk img sz).cand b = [((OsFile.ofDisk img sz).cache b, 0)] := by
  simp [OsFile.ofDisk]

theorem ofDisk_cand_past (img : Nat → w8) (sz b : Nat) (hb : pageUp sz ≤ b) :
    (OsFile.ofDisk img sz).cand b = [(0, 0)] := by
  simp [OsFile.ofDisk, diskByte_past hb]

/-- `initMeta` says what is true of a file on disk. -/
theorem metaOk_ofDisk {st : OsState} {i : Ino} (img : Nat → w8) (sz : Nat)
    (hmaps : ∀ b m, st.proc.maps !! b = some m → m.ino ≠ i)
    (hinfl : ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ i) :
    MetaOk st i (initMeta (OsFile.ofDisk img sz)) (OsFile.ofDisk img sz) := by
  refine ⟨rfl, by simp [initMeta, OsFile.ofDisk], by simp [initMeta, OsFile.ofDisk], ?_, ?_, ?_, ?_,
    fun b c _ h => tailMap_cand _ b c h⟩
  · intro b len
    simp only [initMeta]
    constructor
    · intro h; simp at h
    · intro h; exact absurd rfl (hmaps b _ h)
  · intro t c ht hc; exact absurd hc (hinfl t c ht)
  · intro b hb _; exact ofDisk_cand_lt img sz b hb
  · intro z hz
    simp only [initMeta, Option.some.injEq] at hz; subst hz
    refine ⟨le_pageUp _, fun b hb => ofDisk_cand_past img sz b hb⟩

theorem osInit_wf_coh {st : OsState} (h : FsInit st) :
    OsWf st ∧ OsCoh st (bytesMap st) (metaMap st) ∅ ∅ := by
  obtain ⟨hproc, -, -, -, -, -, hdisk, -, -⟩ := h
  have hdisk' : ∀ i f, st.file i = some f → ∃ img sz, f = OsFile.ofDisk img sz :=
    fun i f hf => (hdisk i f hf).2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro fd d h; simp [hproc, ProcState.empty] at h
  · intro b m h; simp [hproc, ProcState.empty] at h
  · intro b1 m1 _ _ h; simp [hproc, ProcState.empty] at h
  · intro t c h; simp [hproc, ProcState.empty] at h
  · intro t1 c1 _ _ h; simp [hproc, ProcState.empty] at h
  · intro i f hf
    obtain ⟨img, sz, rfl⟩ := hdisk' i f hf; simp [OsFile.ofDisk]
  · intro i f b p hf hp
    obtain ⟨img, sz, rfl⟩ := hdisk' i f hf
    simp only [OsFile.ofDisk, List.mem_singleton] at hp; subst hp; simp
  · intro i; simp [metaMap]
  · intro i m hm
    simp only [metaMap, GMap.lookup_fmap] at hm
    cases hfo : st.fs.files !! i with
    | none => simp [hfo] at hm
    | some f =>
      simp only [hfo, Option.map_some, Option.some.injEq] at hm
      subst hm
      obtain ⟨img, sz, rfl⟩ := hdisk' i f hfo
      exact ⟨_, rfl, metaOk_ofDisk img sz (fun b m h => by simp [hproc, ProcState.empty] at h)
        (fun t c h => by simp [hproc, ProcState.empty] at h)⟩
  · intro i b x hx
    simp only [bytesMap, bytesMapF_lookup] at hx
    cases hf : st.fs.files !! i with
    | none => simp [hf] at hx
    | some f =>
      simp only [hf, Option.bind_some] at hx
      split at hx
      · cases hx
        obtain ⟨img, sz, rfl⟩ := hdisk' i f hf
        refine ⟨_, hf, by assumption, rfl, ⟨0, by simp [OsFile.ofDisk]⟩, ?_⟩
        simp [cutOf, metaMap, GMap.lookup_fmap, hf, initMeta, CandRel]
      · cases hx
  · intro i f b hf hb
    simp only [bytesMap, bytesMapF_lookup]
    simp [show st.fs.files !! i = some f from hf, hb]
  · simp [hproc, ProcState.empty]
  · intro t; simp [hproc, ProcState.empty]
  · intro t ti c h; simp at h
  · intro t ti h; simp at h
  · intro t ti h; simp at h
  · intro t ti h; simp at h
  · intro i m c hm hc
    simp only [metaMap, GMap.lookup_fmap] at hm
    cases hfo : st.fs.files !! i with
    | none => simp [hfo] at hm
    | some f => simp [hfo] at hm; subst hm; simp [initMeta] at hc

/-- An initial tree is well formed, and coherent with the history of nothing logged on it, and no
fd. -/
theorem fsInit_tree {st : OsState} (h : FsInit st) :
    FsTreeWf st ∧ TreeCoh st (st.fs.treeDur, []) ∅ ∅ := by
  obtain ⟨hproc, hlog, -, hroots, hwf, hnamed, -, hfiles, hdirs⟩ := h
  refine ⟨⟨hroots, fun n _ => ?_, ?_, ?_, hfiles⟩, ⟨by rw [hlog], by rw [hlog]; intro x e he; simp at he, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hlog]; simp only [List.take_nil, List.map_nil, replay, List.foldl_nil]
    refine ⟨hwf, fun i hi => ?_, hdirs⟩
    have := hnamed i hi
    cases hf : st.fs.files !! i with
    | none => exact absurd hf this
    | some f => exact ⟨f, rfl⟩
  · intro fd df h; simp [hproc, ProcState.empty] at h
  · intro fd _; simp [hproc, ProcState.empty]
  · intro fd; simp [hproc, ProcState.empty]
  · intro fd x df hx; simp at hx
  · intro fd x hx; simp at hx
  · intro t; simp [hproc, ProcState.empty]
  · intro t x hx; simp at hx

theorem os_local_init {GF : BundledGFunctors} (hPre : OsGpreS GF) (st : OsState) (h : FsInit st) :
    ⊢@{IProp GF} |==> ∃ hL : OsGS GF, osCtx hL st ∗ osStart hL st := by
  letI := hPre.osPreAllG
  obtain ⟨hwf, hcoh⟩ := osInit_wf_coh h
  obtain ⟨htw, htc⟩ := fsInit_tree h
  have hproc := h.1
  imod ghost_map_alloc (GF := GF) (bytesMap st) with ⟨%γb, Hab, Hb⟩
  imod ghost_map_alloc (GF := GF) (metaMap st) with ⟨%γm, Ham, Hm⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 OsFd) with ⟨%γf, Haf, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat TokInfo) with ⟨%γt, Hat, -⟩
  imod ghostVar_alloc (GF := GF) ((∅ : GMap Loc (Option w8 × Bool)), 0) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc (GF := GF)
    (histMap (st.fs.roots, ((st.fs.treeDur, ([] : List LogEntry)) : Hist))) with ⟨%γd, Had, Hd⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 (Ino × DirPh)) with ⟨%γdf, Hadf, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat (Nat × Qp)) with ⟨%γc, Hac, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcm, Hcm, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Unit (Roots × Hist)) with ⟨%γs, Has, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 (Ino × DirPhS)) with ⟨%γdfS, Hadfs, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat (Nat × Qp)) with ⟨%γcS, Hacs, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Unit Unit) with ⟨%γperm, Hap, -⟩
  imod ghost_map_insert (GF := GF) () () (by rfl) $$ Hap with ⟨-, Hperm⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap (Ino × NameSet) NamesH) with ⟨%γn, Han, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γlen, Halen, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat LogEntry) with ⟨%γlog, Halog, -⟩
  imodintro
  iexists (⟨hPre.osPreAllG, γb, γm, γf, γt, γv, γd, γdf, γc, γcm, γs, γdfS, γcS, γperm, γn, γlen,
    γlog⟩ : OsGS GF)
  isplitl [Hab Ham Haf Hat Hv1 Had Hadf Hac Hcm Has Hadfs Hacs Hperm Han Halen Halog]
  · unfold osCtx osCtxF treeCtx tokRes gAuth gVar commitRes gCommit
    isplitl [Hab Ham Haf Hat Hv1]
    · iexists (bytesMap st), (metaMap st), ∅, ∅
      rw [cellView_of_maps_empty (by rw [hproc]; rfl),
        show st.proc.inflight = ∅ by rw [hproc]; rfl, GMap.map_size_empty]
      iframe Hab Ham Haf Hat Hv1
      isplitr
      · ipureintro; exact ⟨hwf, hcoh⟩
      · iapply BigSepM.bigSepM_empty.2; itrivial
    · isplitl [Had Hadf Hac Has Hadfs Hacs Hperm Han Halen Halog]
      · ileft
        unfold treeLegacy legacyHolds gAuth gElem
        iexists ((st.fs.treeDur, ([] : List LogEntry)) : Hist), ∅, ∅
        iframe Had Hadf Hac Has Hadfs Hacs Hperm Han Halen Halog
        isplitr
        · ipureintro; exact ⟨htw, htc⟩
        unfold callRes rdRes
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        · iapply BigSepM.bigSepM_empty.2; itrivial
      iexists 0
      iframe Hcm
      ipureintro; intro y hy; exact absurd hy (Nat.not_lt_zero _)
  · unfold osStart osStartF treeStart gElem gVar histMap
    ihave Hd := (show ([∗map] k ↦ v ∈ ({[() := (st.fs.roots,
          ((st.fs.treeDur, ([] : List LogEntry)) : Hist))]} : GMap Unit (Roots × Hist)),
          ghostMapElem (GF := GF) γd k (DFrac.own 1) v) ⊢
        ghostMapElem γd () (DFrac.own 1)
          ((st.fs.roots, ((st.fs.treeDur, ([] : List LogEntry)) : Hist)) : Roots × Hist) from
      (BigSepM.bigSepM_singleton (M := GMap Unit)
        (Φ := fun (k : Unit) (v : Roots × Hist) =>
          ghostMapElem (GF := GF) γd k (DFrac.own 1) v)).1) $$ Hd
    iframe

/-- The ghost state of the Linux file extension. The program gets every file and byte of the initial
state, the tree's history, and the means to allocate the invariant of the mapped cells
(`osInv_alloc`). -/
instance fs_interp : ExtInterp fsExt where
  LocalGS := OsGS
  GlobalGS _ := Unit
  localCtx := osCtx
  globalCtx _ _ := iprop(True)
  PreG := OsGpreS
  initgP _ := True
  initP st _ := FsInit st
  globalStart _ _ := iprop(True)
  localStart := osStart
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre st _ h := os_local_init hPre st h

end Fs
end Perennial
