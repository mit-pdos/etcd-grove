/-
The ghost state of the Linux file extension (`GooseLang/Ext/Fs/Impl.lean`): its values, the pure
relations between it and the extension's state, and the extension's ghost state for the adequacy
theorem (`ExtInterp`). The specs are in `Specs.lean`; the step lemmas and the resources in
`World.lean`. Untrusted.

* Ghost maps, all in the one `AllG GF`: the bytes of the page cache, `(i, b) ↦ (x, cs)` for every
  byte `b < size` of the file of inode `i`, its page-cache value and its crash candidates, exactly
  (`ByteG`); the files, `i ↦ m` (an `OsMeta`: the size, its crash bounds, the mappings, the bytes
  that may not be durable, the zeros known past the size); the fds; the changes in flight
  (`TokInfo`); the tree's history (one entry, `Hist`, the state's), its directory fds (`DirPhS`),
  its calls on paths in flight (logging and guard calls), the call permission, the name claims, the
  log's length and entries.
* The relations: `OsWf` (the state alone) and `OsCoh` (the files' maps mirror the state); `FsTreeWf`
  and `TreeCohS` (the log's disciplines, and the ghost entries of the directory fds and calls
  mirror the state's). The tree's interpretation `treeCtx` has one shape, its history's authority
  the state's (`notes/fs-interp-state-determined.md`); a generation starts with its names filled in
  (`treeStart`).
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
public import GooseLang.Ext.Fs.TreeCutProof
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
  /-- The page cache is zero from the size to `cz` (nothing known if `cz` is at most the size): an
  `ftruncate` zeroes it to the end of the page holding the larger of the old and new ends (`rsPost`),
  and a write, a growth or a sync keeps it (the bytes past the new size were past the old one, and
  none of them is written). A sync of a file whose last page is known zero past the size makes the
  zeros known from the size on (`OsMeta.synced`). -/
  cz : Nat := 0
  /-- Stamps of resizes of the file known to the client (each among the file's `OsFile.rzs`,
  `MetaOk.rz`): a resize that landed with its cut-off candidates known (`rsPostK true`) adds its
  stamp; nothing else changes it. Ghost only: what a client (the WAL, at a crash) needs to tell a
  resize's zero candidates from a `pwrite`'s (W1, `notes/wal-fsext-plan.md` §2.5). -/
  rz : List Nat := []
  /-- **The sizes a crash may leave the file at**, if known (`some l`): each of `OsFile.CrashSz`
  (the size, the smallest size since the last sync, `OsFile.szCrash`) is in `l` (`MetaOk.xs`), where
  `lo` and `hi` only bound them. A sync, a boot or a crash makes it the size alone; a landed
  `ftruncate` adds its size (`OsFile.land` adds only that one); a `pwrite` that may reach past
  the size, or an `fallocate` that changes it, forgets them (`none`: `land` adds every size in
  between); nothing else changes it. Ghost only: what a client learns at a crash (`crashSeen_xs`). -/
  xs : Option (List Nat) := none

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
  | .falloc sz => min ti.m0.size sz

/-- The end of the bytes the change announced. -/
def TokInfo.hi (ti : TokInfo) : Nat :=
  match ti.kind with
  | .write off data => off + data.length
  | .truncate sz => pageEnd (max ti.m0.size sz)
  | .falloc sz => max ti.m0.size sz

/-- The value the change announced for byte `b` (in its range). -/
def TokInfo.val (ti : TokInfo) (b : Nat) : w8 :=
  match ti.kind with
  | .write off data => if off ≤ b then data.getD (b - off) 0 else 0
  | .truncate _ => 0
  | .falloc _ => 0

/-- The size the change leaves the file with. -/
def TokInfo.target (ti : TokInfo) : Nat :=
  match ti.kind with
  | .write off data => max ti.m0.size (off + data.length)
  | .truncate sz => sz
  | .falloc sz => sz

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

@[simp] theorem OsMeta.touch_rz (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).rz = m.rz := by
  unfold OsMeta.touch; split
  · rfl
  · split <;> rfl

@[simp] theorem OsMeta.announce_rz (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).rz = m.rz := by
  simp [OsMeta.announce]

@[simp] theorem OsMeta.announce_cut (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).cut = m.cut := by
  simp [OsMeta.announce]

@[simp] theorem OsMeta.touch_xs (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).xs = m.xs := by
  unfold OsMeta.touch; split
  · rfl
  · split <;> rfl

@[simp] theorem OsMeta.announce_xs (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).xs = m.xs := by
  simp [OsMeta.announce]

/-- The `OsMeta` a change holds. -/
def TokInfo.meta (ti : TokInfo) : OsMeta := ti.m0.announce ti.lo ti.hi ti.target

/-- The change `c` in flight is the one `ti` records. -/
def TokInfo.Is (ti : TokInfo) (c : OsChange) : Prop :=
  c.ino = ti.ino ∧ c.kind = ti.kind ∧ c.lo = ti.lo ∧ c.hi = ti.hi ∧ c.target = ti.target ∧
    ∀ b, inRange c.lo c.hi b = true → c.val b = ti.val b

instance OsMeta.countable : Pos.Countable OsMeta :=
  Pos.Countable.ofInjective
    (fun m => Pos.Countable.encode (m.size, m.lo, m.hi, m.maps, m.dlo, m.dhi, m.zf, m.tc, m.cut, m.cz,
      m.rz, m.xs))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
      subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12; rfl)

instance Qp.countable : Pos.Countable Qp :=
  Pos.Countable.ofInjective (fun q => Pos.Countable.encode (q.val.num, q.val.den))
    (fun a b h => by
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Rat.ext h.1 h.2))

instance OsFd.countable : Pos.Countable OsFd :=
  Pos.Countable.ofInjective
    (fun d => Pos.Countable.encode (d.ino, d.readable, d.writable, d.ofd, d.flk))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

instance LockKind.countable : Pos.Countable LockKind :=
  Pos.Countable.ofInjective (fun k => Pos.Countable.encode (k = LockKind.ofd : Bool))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all)

def OsChangeKind.enc : OsChangeKind → (Nat × List w8) ⊕ (Bool × Nat)
  | .write off data => .inl (off, data)
  | .truncate sz => .inr (true, sz)
  | .falloc sz => .inr (false, sz)

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
  /-- The sizes in order, and none past `maxBytes` (the model's bound: no step, crash or start
  makes a file larger, `Impl.lean`'s `maxBytes`). -/
  sizes : ∀ i f, st.file i = some f → f.sizeLo ≤ f.size ∧ f.size ≤ f.sizeHi ∧ f.sizeHi ≤ maxBytes
  /-- Every candidate's stamp is at most the last change's number. -/
  stamps : ∀ i f b p, st.file i = some f → p ∈ f.cand b → p.2 ≤ st.fs.stamp

/-- The sizes a crash may leave the file `f` at, apart from a change in flight (`CrashFile`): its
size, its smallest size since the last sync, and its crash sizes (`OsFile.szCrash`). -/
def OsFile.CrashSz (f : OsFile) (s : Nat) : Prop := s = f.size ∨ s = f.sizeLo ∨ f.szCrash s

/-- After a sync, the size is the one crash size. -/
theorem OsFile.crashSz_synced {f : OsFile} {busy : Nat → Prop} [DecidablePred busy] {s : Nat}
    (h : (f.synced busy).CrashSz s) : s = f.size := by
  simp only [OsFile.CrashSz, OsFile.synced] at h; rcases h with h | h | h <;> exact h

/-- A landing adds the sizes `OsFile.land` adds: its size for an `ftruncate`, every size between
the old and the new one otherwise. -/
theorem OsFile.crashSz_land {f : OsFile} {c : OsChange} {e sz s : Nat}
    (h : (f.land c e sz).CrashSz s) :
    f.CrashSz s ∨ (if c.kind.isTrunc then s = sz else min f.size sz ≤ s ∧ s ≤ max f.size sz) := by
  simp only [OsFile.CrashSz, OsFile.land] at h ⊢
  rcases h with h | h | h | h
  · right; subst h; split <;> omega
  · by_cases hl : f.sizeLo ≤ sz
    · left; right; left; omega
    · right; split <;> omega
  · left; right; right; exact h
  · right; exact h

/-- A landing that leaves the size as it was adds no crash size. -/
theorem OsFile.crashSz_land_same {f : OsFile} {c : OsChange} {e sz s : Nat}
    (hsz : (f.land c e sz).size = f.size) (h : (f.land c e sz).CrashSz s) : f.CrashSz s := by
  have hs : sz = f.size := hsz
  rcases OsFile.crashSz_land h with h | h
  · exact h
  · left; split at h <;> omega

/-- An `ftruncate`'s landing adds its size alone. -/
theorem OsFile.crashSz_land_trunc {f : OsFile} {c : OsChange} {e sz s : Nat}
    (hk : c.kind.isTrunc = true) (h : (f.land c e sz).CrashSz s) : f.CrashSz s ∨ s = sz := by
  rcases OsFile.crashSz_land h with h | h
  · exact .inl h
  · rw [if_pos hk] at h; exact .inr h

/-- What a synced `OsMeta` knows of the crash sizes (`some [size]`) holds of a synced file. -/
theorem OsFile.xs_synced {f : OsFile} {busy : Nat → Prop} [DecidablePred busy] {n : Nat}
    (hn : n = f.size) : ∀ l, some [n] = some l → ∀ s, (f.synced busy).CrashSz s → s ∈ l := by
  intro l hl s hs
  cases hl
  rw [OsFile.crashSz_synced hs, hn]; exact List.mem_singleton_self _

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
  cz : ∀ b, f.size ≤ b → b < m.cz → f.cache b = 0
  /-- The resize stamps `m` knows are the file's. -/
  rz : ∀ s ∈ m.rz, s ∈ f.rzs
  /-- The page cache is zero from the zeros known on (no step writes the page cache past every
  change's announced range; a sync zeroes it past the size's last page). What lets a write that
  lands up to the zeros known raise `cz` (`pwPost`). -/
  zc : ∀ z, m.zf = some z → ∀ b, z ≤ b → f.cache b = 0
  /-- The page cache is zero past the size's last page (Linux has no page there: a file from disk
  reads zeros past it, `OsFile.ofDisk`; a resize lands zeros to the end of the page it announced;
  a sync zeroes it). With `cz`, what lets a resize's landing raise `cz` (`rsCz`). -/
  ce : ∀ b, pageEnd f.size ≤ b → f.cache b = 0
  /-- The crash sizes `m` knows hold the file's (`OsMeta.xs`). -/
  xs : ∀ l, m.xs = some l → ∀ s, f.CrashSz s → s ∈ l

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
  /-- A resize in flight has its stamp among its file's resize stamps (its first step recorded it). -/
  tok_rz : ∀ t ti, Γt !! t = some ti → ti.kind.isResize = true → ∃ f, st.file ti.ino = some f ∧
    ti.n ∈ f.rzs
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

/-- **The zeros `m` knows start at or past its size, and the candidates it knows past them are the
zero** (`MetaOk`'s `zf` and `tail` together, `MetaOk.tcz`): a resize's first step tells it of the
`OsMeta` it found (`wp_osResizeStart`). The first half (`wal-tc8`): the WAL's truncate supply gets it
there, since its tie cannot mention the `OsMeta` and its invariant does not keep the fact. -/
def OsMeta.TcZ (m : OsMeta) : Prop :=
  (∀ z, m.zf = some z → m.size ≤ z) ∧
  ∀ z b c, m.zf = some z → z ≤ b → m.size ≤ b → m.tc !! b = some c → c = [((0 : w8), 0)]

theorem MetaOk.tcz {st : OsState} {i : Ino} {m : OsMeta} {f : OsFile} (h : MetaOk st i m f) :
    m.TcZ := by
  refine ⟨fun z hz => by rw [h.size]; exact (h.zf z hz).1, fun z b c hz hzb hsb hc => ?_⟩
  rw [← h.tail b c (by rw [← h.size]; exact hsb) hc, (h.zf z hz).2 b hzb]

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

/-- What the ghost state records of a call on a path in flight: its start (the log's length when it
began) and its path, as the state's `calls` has them, and the fraction it holds. -/
abbrev CallV := (Nat × GoString) × Qp

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
  /-- A lower bound on the committed prefix of the tree's log (`commitRes`). -/
  γcm : GName
  /-- The shared mode's (`notes/wal-fsext-i2-design.md`, §2): its history (a map of one entry,
  `Unit ↦ Roots × Hist`), its directory fds (`w64 ↦ Ino × DirPhS`), its calls in flight
  (`Nat ↦ (Nat × GoString) × Qp`: start, path, fraction), the call permission (`GoString ↦ Unit`, fractional,
  one per key: a root, or `[]` for the paths under no root, `callKey`), the name claims
  (`Ino × NameSet ↦ NamesH`), the log's length (a mono nat) and its entries (`Nat ↦ LogEntry`,
  persistent). Allocated at boot, used from the mode switch on. -/
  γs : GName
  γdfS : GName
  γcS : GName
  γperm : GName
  γn : GName
  γlen : GName
  γlog : GName
  /-- The shared mode's guard calls (`notes/wal-fsext-i2-design.md`, "Implementation log, guard
  calls"): calls that never log, each holding a fraction of the call permission (`Nat ↦ (Nat × GoString) × Qp`:
  begun at that log length, holding that fraction), apart from the logging calls of `γcS`. -/
  γg : GName
  /-- The fds of directories outside the roots' trees (`ProcState.ofds`, `w64 ↦ Unit`), each held
  whole by its owner (`osOutFd`). -/
  γo : GName
  /-- The exclusive locks (`LockKind × Ino ↦ w64`: the fd holding an exclusive lock of the kind on
  the file), each held whole by its owner (`osLock`; `lockCtx`). -/
  γlk : GName

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

/-! ### The entries of an fd map: an fd is never negative

The extension's fd predicates (`osFd`, `osDirFd`, `osDirFdS`, `osOutFd`) are such entries: `Open`
gives a free fd (`FdFree`: `0 ≤ fd.toInt`), and `os.File.Close`'s model tells a closed file (fd -1)
from an open one. -/

section fdElems
variable {GF : BundledGFunctors} (hL : OsGS GF)
variable {V : Type} [Pos.Countable V]

/-- The entry `fd ↦ v` of the fd map `γ`, `fd` not negative. -/
def gFdElem (γ : GName) (fd : w64) (dq : DFrac) (v : V) : IProp GF :=
  iprop(⌜0 ≤ fd.toInt⌝ ∗ gElem hL γ fd dq v)

instance gFdElem_timeless (γ : GName) (fd : w64) (dq : DFrac) (v : V) :
    Timeless (gFdElem hL γ fd dq v) := by
  unfold gFdElem; infer_instance

theorem gFdElem_nonneg (γ : GName) (fd : w64) (dq : DFrac) (v : V) :
    gFdElem hL γ fd dq v ⊢ ⌜0 ≤ fd.toInt⌝ := by
  unfold gFdElem; iintro ⟨%h, -⟩; ipureintro; exact h

theorem gFdElem_lookup (γ : GName) (m : GMap w64 V) (k : w64) (dq : DFrac) (v : V) :
    ⊢ gAuth hL γ m -∗ gFdElem hL γ k dq v -∗ ⌜m !! k = some v⌝ := by
  unfold gFdElem
  iintro HA ⟨-, H⟩
  iapply gAuth_lookup $$ HA H

theorem gFdElem_update (γ : GName) (m : GMap w64 V) (k : w64) (v w : V) :
    ⊢ gAuth hL γ m -∗ gFdElem hL γ k (DFrac.own 1) v ==∗
      gAuth hL γ (<[k := w]> m) ∗ gFdElem hL γ k (DFrac.own 1) w := by
  unfold gFdElem
  iintro HA ⟨%h, H⟩
  imod gAuth_update _ _ _ _ _ w $$ HA H with ⟨HA, H⟩
  imodintro
  iframe HA; iframe H; ipureintro; exact h

theorem gFdElem_insert (γ : GName) (m : GMap w64 V) (k : w64) (v : V) (h0 : 0 ≤ k.toInt)
    (h : m !! k = none) :
    ⊢ gAuth hL γ m ==∗ gAuth hL γ (<[k := v]> m) ∗ gFdElem hL γ k (DFrac.own 1) v := by
  unfold gFdElem
  iintro HA
  imod gAuth_insert _ _ _ _ v h $$ HA with ⟨HA, H⟩
  imodintro
  iframe HA; iframe H; ipureintro; exact h0

theorem gFdElem_delete (γ : GName) (m : GMap w64 V) (k : w64) (v : V) :
    ⊢ gAuth hL γ m -∗ gFdElem hL γ k (DFrac.own 1) v ==∗ gAuth hL γ (GMap.delete k m) := by
  unfold gFdElem
  iintro HA ⟨-, H⟩
  iapply gAuth_delete $$ HA H

theorem gFdElem_valid_2 (γ : GName) (k : w64) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢ gFdElem hL γ k dq1 v1 -∗ gFdElem hL γ k dq2 v2 -∗ ⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ := by
  unfold gFdElem
  iintro ⟨-, H1⟩ ⟨-, H2⟩
  iapply gElem_valid_2 $$ H1 H2

theorem gFdElem_split (γ : GName) (k : w64) (q1 q2 : Qp) (v : V) :
    gFdElem hL γ k (DFrac.own (q1 + q2)) v ⊣⊢
      gFdElem hL γ k (DFrac.own q1) v ∗ gFdElem hL γ k (DFrac.own q2) v := by
  unfold gFdElem
  constructor
  · iintro ⟨%h, H⟩
    icases (gElem_split _ _ _ _ _ _).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iframe H1; ipureintro; exact h
    · iframe H2; ipureintro; exact h
  · iintro ⟨⟨%h, H1⟩, ⟨-, H2⟩⟩
    isplitr
    · ipureintro; exact h
    · iapply (gElem_split _ _ _ _ _ _).2; isplitl [H1]; iexact H1; iexact H2

end fdElems

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
  ⟨fun b => if f.size ≤ b ∧ b < pageEnd f.size then some (f.cand b) else none,
   ⟨List.range (pageEnd f.size), fun k h => by
     by_cases hk : f.size ≤ k ∧ k < pageEnd f.size
     · exact List.mem_range.2 hk.2
     · simp [hk] at h⟩⟩

theorem tailMap_lookup (f : OsFile) (b : Nat) :
    tailMap f !! b = if f.size ≤ b ∧ b < pageEnd f.size then some (f.cand b) else none := rfl

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
  ⟨f.size, f.size, f.size, ∅, 0, 0, some (pageEnd f.size), tailMap f, none, 0, [], some [f.size]⟩

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

open Classical in
/-- **The key of a call on the path `p`**: the root `p` is in the tree of (unique for well-formed
roots: `root_of_isUnder`), or `[]` for a path under no root. A call's share of the call permission
is a share of its key's (`osCallPerm`). -/
noncomputable def callKey (R : Roots) (p : GoString) : GoString :=
  if h : ∃ rj ∈ R, IsUnder rj.1 p then h.choose.1 else []

/-- What the state interpretation holds, in the shared mode, of each call on a path in flight:
the fraction of its key's call permission its `CallBegin` took (the key of its path under the
roots `R`, `callKey`). -/
def callResS (hL : OsGS GF) (R : Roots) (Γc : GMap Nat CallV) : IProp GF :=
  iprop([∗map] _t ↦ x ∈ Γc, gElem hL hL.γperm (callKey R x.1.2) (DFrac.own x.2) ())

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

/-- The roots' part of the tree's coherence, under the ghost map `ρ` from directories to roots:
`RootTags` and the per-root `DirOpExcl` (`TreeCut.lean`, from the log's start), and every directory an
entry writes is one of the tree now (so a new directory's root can be set without changing an
entry's tag). -/
structure RootCoh (st : OsState) (ρ : Ino → GoString) : Prop where
  tags : RootTags ρ st.fs.roots st.fs.treeDur st.fs.metaLog 0
  dox : DirOpExcl ρ st.fs.metaLog 0
  wkeys : ∀ (x : Nat) (e : LogEntry), st.fs.metaLog[x]? = some e → ∀ j b, e.op.Writes j b → j ∈ st.tree

theorem RootCoh.congr {st st' : OsState} {ρ : Ino → GoString} (h : RootCoh st ρ)
    (hr : st'.fs.roots = st.fs.roots) (hd : st'.fs.treeDur = st.fs.treeDur)
    (hl : st'.fs.metaLog = st.fs.metaLog) : RootCoh st' ρ := by
  have ht : st'.tree = st.tree := by simp [OsState.tree, hd, hl]
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
  exact ⟨⟨hr ▸ h1, by rw [hd, hl]; exact h2, by rw [hl]; exact h3⟩, hl ▸ h4,
    by rw [hl, ht]; exact h5⟩

/-- The calls' part of the tree's coherence, per key, under the map `ρ` of `RootCoh` (an entry's
tag is its directory's root, `tagOf ρ`): a logging call holding its key's whole permission began
after every entry of its key; every logging call began after each directory operation of its key;
a logging call whose fraction and a guard's of the same key make the whole, the guard begun no
later, began after every entry of its key. -/
structure CallsK (st : OsState) (ρ : Ino → GoString) (Γc Γg : GMap Nat CallV) :
    Prop where
  whole : ∀ t x, Γc !! t = some x → x.2 = 1 → ∀ y (ey : LogEntry), x.1.1 ≤ y →
    st.fs.metaLog[y]? = some ey → tagOf ρ ey ≠ callKey st.fs.roots x.1.2
  after : ∀ t x, Γc !! t = some x → ∀ (y : Nat) (ey : LogEntry), st.fs.metaLog[y]? = some ey →
    (ey.op.IsDirOp ∧ tagOf ρ ey = callKey st.fs.roots x.1.2) → y < x.1.1
  pair : ∀ c x t g, Γc !! c = some x → Γg !! t = some g →
    callKey st.fs.roots g.1.2 = callKey st.fs.roots x.1.2 → x.2.val + g.2.val = 1 →
    g.1.1 ≤ x.1.1 → ∀ y (ey : LogEntry), x.1.1 ≤ y → st.fs.metaLog[y]? = some ey →
    tagOf ρ ey ≠ callKey st.fs.roots x.1.2

theorem CallsK.congr {st st' : OsState} {ρ : Ino → GoString} {Γc Γg : GMap Nat CallV}
    (h : CallsK st ρ Γc Γg) (hr : st'.fs.roots = st.fs.roots)
    (hl : st'.fs.metaLog = st.fs.metaLog) : CallsK st' ρ Γc Γg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hr, hl] <;> assumption

/-- `CallsK` for fewer calls. -/
theorem CallsK.mono {st : OsState} {ρ : Ino → GoString} {Γc Γg Γc' Γg' : GMap Nat CallV}
    (h : CallsK st ρ Γc Γg) (hc : ∀ t x, Γc' !! t = some x → Γc !! t = some x)
    (hg : ∀ t x, Γg' !! t = some x → Γg !! t = some x) : CallsK st ρ Γc' Γg' :=
  ⟨fun t x hx => h.whole t x (hc t x hx), fun t x hx => h.after t x (hc t x hx),
    fun c x t g hx hg' => h.pair c x t g (hc c x hx) (hg t g hg')⟩

theorem lookup_delete_some {α : Type} {m : GMap Nat α} {k t : Nat} {x : α}
    (h : (GMap.delete k m) !! t = some x) : m !! t = some x := by
  by_cases h0 : k = t
  · subst h0; simp at h
  · rwa [GMap.lookup_delete_ne _ h0] at h

/-- The tree's ghost state mirrors its state: the log's disciplines (`TreeCut.lean`, from the log's
start; the per-root ones under some map `ρ` of directories to roots, `RootCoh`), a ghost entry for
every directory fd, and for every call on a path in flight one in the logging calls `Γc` or in the
guard calls `Γg` (never both); a call began no later than now; per key (`CallsK`, under the same
`ρ`), a call holding its key's whole permission began after every entry of its key, every logging
call began after every directory operation of its key (guards are exempt: they never log), and a
logging call whose fraction and a guard's of its key make the whole, the guard begun no later,
began after every entry of its key. -/
structure TreeCohS (st : OsState) (Γdf : GMap w64 (Ino × DirPhS))
    (Γc Γg : GMap Nat CallV) : Prop where
  starts : Starts st.fs.metaLog
  pss : PerSlotSeq st.fs.metaLog
  rc : ∃ ρ, RootCoh st ρ ∧ CallsK st ρ Γc Γg
  valid : LogValid st.fs.treeDur st.fs.metaLog 0
  fds : ∀ fd, (Γdf !! fd).map (·.1) = (st.proc.dfds !! fd).map (·.ino)
  ph : ∀ fd x df, Γdf !! fd = some x → st.proc.dfds !! fd = some df → PhOkS st x.1 x.2 df.rd
  calls : ∀ t x, Γc !! t = some x → st.proc.calls !! t = some x.1
  callsLe : ∀ t x, Γc !! t = some x → x.1.1 ≤ st.fs.metaLog.length
  gcalls : ∀ t x, Γg !! t = some x → st.proc.calls !! t = some x.1
  gdisj : ∀ t x, Γg !! t = some x → Γc !! t = none
  cover : ∀ t s, st.proc.calls !! t = some s → Γc !! t ≠ none ∨ Γg !! t ≠ none

/-- **The interpretation of the tree of `st`**, a function of `st` up to the per-call and per-fd
annotations: the history's authority (the state's roots, durable tree and log), the directory fds,
the logging calls and the guard calls, with the call permission's fractions of the calls in flight,
and the committed prefix's bound. -/
def treeCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (Γdf : GMap w64 (Ino × DirPhS)) (Γc Γg : GMap Nat CallV),
    ⌜FsTreeWf st ∧ TreeCohS st Γdf Γc Γg⌝ ∗
    gAuth hL hL.γs (histMap (st.fs.roots, ((st.fs.treeDur, st.fs.metaLog) : Hist))) ∗
    gAuth hL hL.γdfS Γdf ∗ gAuth hL hL.γcS Γc ∗ callResS hL st.fs.roots Γc ∗
    gAuth hL hL.γg Γg ∗ callResS hL st.fs.roots Γg ∗ commitRes hL st)

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

/-- `TreeCohS` depends on the roots, the durable tree, the log, the directory fds and the calls only. -/
theorem TreeCohS.congr {st st' : OsState} {Γdf Γc Γg} (h : TreeCohS st Γdf Γc Γg)
    (hd : st'.fs.treeDur = st.fs.treeDur) (hl : st'.fs.metaLog = st.fs.metaLog)
    (hf : st'.proc.dfds = st.proc.dfds) (hc : st'.proc.calls = st.proc.calls)
    (hr : st'.fs.roots = st.fs.roots) :
    TreeCohS st' Γdf Γc Γg := by
  obtain ⟨h1, h2, h3, h4, h6, h7, h8, h9, h12, h13, h14⟩ := h
  refine ⟨hl ▸ h1, hl ▸ h2, h3.elim fun ρ h => ⟨ρ, h.1.congr hr hd hl, h.2.congr hr hl⟩,
    by rw [hd, hl]; exact h4, ?_, ?_, ?_, ?_, ?_, h13, ?_⟩
  · intro fd; rw [hf]; exact h6 fd
  · intro fd x df hx hdf; rw [hf] at hdf; exact (h7 fd x df hx hdf).congr hd hl
  · intro t x hx; rw [hc]; exact h8 t x hx
  · intro t x hx; rw [hl]; exact h9 t x hx
  · intro t x hx; rw [hc]; exact h12 t x hx
  · intro t s hs; rw [hc] at hs; exact h14 t s hs

/-- A step that leaves the tree alone keeps its interpretation. -/
theorem treeCtx_frame (hL : OsGS GF) {st st' : OsState} (h : TreeFrame st st') :
    treeCtx hL st ⊢ treeCtx hL st' := by
  unfold treeCtx
  iintro ⟨%Γdf, %Γc, %Γg, %hw, Has, Hadf, Hacs, Hcr, HAg, Hgr, Hcm⟩
  iexists Γdf, Γc, Γg
  rw [h.roots, h.treeDur, h.metaLog]
  iframe Has Hadf Hacs Hcr HAg Hgr
  isplitr [Hcm]
  · ipureintro
    exact ⟨h.wf hw.1, hw.2.congr h.treeDur h.metaLog h.dfds h.calls h.roots⟩
  · iapply commitRes_grow hL (commitGrows_of_eq h.committed) $$ Hcm

/-- The tree's interpretation without the committed prefix's bound (`treeCtx_eq`): the step proofs
close the two apart. -/
def treeCtxT (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (Γdf : GMap w64 (Ino × DirPhS)) (Γc Γg : GMap Nat CallV),
    ⌜FsTreeWf st ∧ TreeCohS st Γdf Γc Γg⌝ ∗
    gAuth hL hL.γs (histMap (st.fs.roots, ((st.fs.treeDur, st.fs.metaLog) : Hist))) ∗
    gAuth hL hL.γdfS Γdf ∗ gAuth hL hL.γcS Γc ∗ callResS hL st.fs.roots Γc ∗
    gAuth hL hL.γg Γg ∗ callResS hL st.fs.roots Γg)

theorem treeCtx_eq (hL : OsGS GF) (st : OsState) :
    treeCtx hL st ⊣⊢ treeCtxT hL st ∗ commitRes hL st := by
  unfold treeCtx treeCtxT
  constructor
  · iintro ⟨%Γdf, %Γc, %Γg, %h, H1, H2, H3, H4, H5, H6, H7⟩
    iframe H7
    iexists Γdf, Γc, Γg
    iframe
    ipureintro; exact h
  · iintro ⟨⟨%Γdf, %Γc, %Γg, %h, H1, H2, H3, H4, H5, H6⟩, H7⟩
    iexists Γdf, Γc, Γg
    iframe
    ipureintro; exact h

/-- **The tree's resources before its invariants are allocated** (`osSwitchKit_open`), for the roots
`R` and the history `V`: what the shared invariant holds (the history `(R, V)`, the claims'
authority, the log's length and map), the call permission of key `[]` (the dispenser's), every other
root's whole call permission, the log's lower bound, and a whole claim on all names of every
directory. -/
def osSwitchKitG (hL : OsGS GF) (R : Roots) (V : Hist) : IProp GF :=
  iprop(gElem hL hL.γs () (DFrac.own 1) (R, V) ∗
    gAuth hL hL.γn (claimsInit V (dirsOf V)) ∗ ⌜RootsOk R ∧ NamesCoh V (claimsInit V (dirsOf V))⌝ ∗
    (letI := hL.osAllG; monoNatAuthOwn hL.γlen 1 V.2.length) ∗ gAuth hL hL.γlog (logMap V.2) ∗
    gElem hL hL.γperm ([] : GoString) (DFrac.own 1) () ∗
    ([∗map] r ↦ u ∈ GMap.delete [] (permMap R), gElem hL hL.γperm r (DFrac.own 1) u) ∗
    (letI := hL.osAllG; monoNatLbOwn hL.γlen V.2.length) ∗
    [∗list] j ∈ dirsOf V, gElem hL hL.γn (j, NameSet.except []) (DFrac.own 1) (namesOf V j (.except [])))

/-- **The start resources of the tree**: its shared names, filled in for the state's tree with
nothing logged (`osSwitchKitG`). -/
def treeStart (hL : OsGS GF) (st : OsState) : IProp GF :=
  osSwitchKitG hL st.fs.roots (st.fs.treeDur, [])

/-- The interpretation of the files of `st`. -/
def osCtxF (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta)
      (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    ⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗ gAuth hL hL.γf Γf ∗ gAuth hL hL.γt Γt ∗
    tokRes hL Γt ∗
    gVar hL (1 : Qp).half (cellView st, GMap.size st.proc.inflight))

/-- The interpretation of the fds of directories outside the roots' trees: their authoritative map,
and no other fd has the number of one. -/
def ofdCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(⌜OfdDisj st⌝ ∗ gAuth hL hL.γo st.proc.ofds)

/-- A step other than `OutClose` keeps the outside fds' interpretation (a fresh fd's ghost entry,
when it opens one, is made and dropped: only `Open`'s outside case's own spec keeps it). -/
theorem ofdCtx_step [GooseExts] [GoGlobalContext] (hL : OsGS GF) {o : String} {v : val}
    {st st' : OsState} {e' : Expr} (h : IsFsStep o v st e' st') (ho : o ≠ "OutClose") :
    ofdCtx hL st ⊢ |==> ofdCtx hL st' := by
  unfold ofdCtx
  iintro ⟨%hd, Ha⟩
  obtain ⟨hd', hk | ⟨fd, hfree, hk⟩⟩ := isFsStep_ofd h ho hd
  · rw [hk]; imodintro; iframe Ha; ipureintro; exact hd'
  · rw [hk]
    imod gAuth_insert hL _ _ fd () hfree.2.2.2 $$ Ha with ⟨Ha, -⟩
    imodintro; iframe Ha; ipureintro; exact hd'

/-- `ofdCtx_step` for any step (`mmap`'s step to itself changes nothing). -/
theorem ofdCtx_stepF [GooseExts] [GoGlobalContext] (hL : OsGS GF) {o : String} {v : val}
    {h : GMap Loc (NonAtomic val)} {st st' : OsState} {e' : Expr} {h' : GMap Loc (NonAtomic val)}
    (hs : FsStep o v h st () e' h' st' ()) (ho : o ≠ "OutClose") :
    ofdCtx hL st ⊢ |==> ofdCtx hL st' := by
  rcases fsStep_cases hs with hs | rfl
  · exact ofdCtx_step hL hs ho
  · iintro H; imodintro; iexact H

/-- At most one description holds a lock of a kind on a file when one holds an exclusive lock of
that kind on it (what the lock rule keeps: `LockStep`). -/
def LockWf (st : OsState) : Prop :=
  ∀ k fd1 d1 fd2 d2, st.proc.fds !! fd1 = some d1 → st.proc.fds !! fd2 = some d2 → fd1 ≠ fd2 →
    d1.ino = d2.ino → d1.lk k = some true → d2.lk k = none

/-- The exclusive locks' ghost map `Λ` mirrors the state: `(k, i) ↦ fd` exactly when the fd `fd` holds
an exclusive lock of kind `k` on the file `i`. -/
def LockCoh (st : OsState) (Λ : GMap (LockKind × Ino) w64) : Prop :=
  ∀ k i fd, Λ !! (k, i) = some fd ↔ ∃ d, st.proc.fds !! fd = some d ∧ d.ino = i ∧ d.lk k = some true

/-- The interpretation of the locks: the exclusive locks' authoritative map. -/
def lockCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ Λ : GMap (LockKind × Ino) w64, ⌜LockWf st ∧ LockCoh st Λ⌝ ∗ gAuth hL hL.γlk Λ)

theorem lockCtx_frame (hL : OsGS GF) {st st' : OsState} (h : LockFrame st st') :
    lockCtx hL st ⊢ lockCtx hL st' := by
  unfold lockCtx
  iintro ⟨%Λ, %hw, Ha⟩
  iexists Λ
  iframe Ha
  ipureintro
  obtain ⟨hwf, hcoh⟩ := hw
  have nl : ∀ (d : OsFd) k, d.ofd = none ∧ d.flk = none → d.lk k = none := by
    intro d k hn; cases k
    · exact hn.1
    · exact hn.2
  have hl : ∀ fd d k, st'.proc.fds !! fd = some d → d.lk k ≠ none →
      st.proc.fds !! fd = some d := by
    intro fd d k hd hk
    rcases h fd with he | ⟨-, hn'⟩
    · rw [← he]; exact hd
    · exact absurd (nl d k (hn' d hd)) hk
  have hl' : ∀ fd d k, st.proc.fds !! fd = some d → d.lk k ≠ none →
      st'.proc.fds !! fd = some d := by
    intro fd d k hd hk
    rcases h fd with he | ⟨hn, -⟩
    · rw [he]; exact hd
    · exact absurd (nl d k (hn d hd)) hk
  refine ⟨fun k fd1 d1 fd2 d2 h1 h2 hne hino hk => ?_, fun k i fd => ?_⟩
  · have h1' := hl fd1 d1 k h1 (by rw [hk]; simp)
    rcases h fd2 with he | ⟨-, hn'⟩
    · exact hwf k fd1 d1 fd2 d2 h1' (by rw [← he]; exact h2) hne hino hk
    · exact nl d2 k (hn' d2 h2)
  · rw [hcoh k i fd]
    constructor
    · rintro ⟨d, hd, hi, hk⟩
      exact ⟨d, hl' fd d k hd (by rw [hk]; simp), hi, hk⟩
    · rintro ⟨d, hd, hi, hk⟩
      exact ⟨d, hl fd d k hd (by rw [hk]; simp), hi, hk⟩

/-- The interpretation of the state `st`: its files, its tree, the outside fds, and the locks. -/
def osCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(osCtxF hL st ∗ treeCtx hL st ∗ ofdCtx hL st ∗ lockCtx hL st)

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

theorem ofDisk_cand_past (img : Nat → w8) (sz b : Nat) (hb : pageEnd sz ≤ b) :
    (OsFile.ofDisk img sz).cand b = [(0, 0)] := by
  simp [OsFile.ofDisk, diskByte_past hb]

/-- `initMeta` says what is true of a file on disk. -/
theorem metaOk_ofDisk {st : OsState} {i : Ino} (img : Nat → w8) (sz : Nat)
    (hmaps : ∀ b m, st.proc.maps !! b = some m → m.ino ≠ i)
    (hinfl : ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ i) :
    MetaOk st i (initMeta (OsFile.ofDisk img sz)) (OsFile.ofDisk img sz) := by
  refine ⟨rfl, by simp [initMeta, OsFile.ofDisk], by simp [initMeta, OsFile.ofDisk], ?_, ?_, ?_, ?_,
    fun b c _ h => tailMap_cand _ b c h, fun b _ h => absurd h (by simp [initMeta]),
    fun s h => by simp [initMeta] at h, ?_, fun b hb => diskByte_past hb, ?_⟩
  · intro b len
    simp only [initMeta]
    constructor
    · intro h; simp at h
    · intro h; exact absurd rfl (hmaps b _ h)
  · intro t c ht hc; exact absurd hc (hinfl t c ht)
  · intro b hb _; exact ofDisk_cand_lt img sz b hb
  · intro z hz
    simp only [initMeta, Option.some.injEq] at hz; subst hz
    refine ⟨le_pageEnd _, fun b hb => ofDisk_cand_past img sz b hb⟩
  · intro z hz b hb
    simp only [initMeta, Option.some.injEq] at hz; subst hz
    exact diskByte_past hb
  · intro l hl x hx
    simp only [initMeta, Option.some.injEq] at hl; subst hl
    simp only [OsFile.CrashSz, OsFile.ofDisk] at hx
    simp only [List.mem_singleton]
    rcases hx with h | h | h <;> exact h

theorem osInit_wf_coh {st : OsState} (h : FsInit st) :
    OsWf st ∧ OsCoh st (bytesMap st) (metaMap st) ∅ ∅ := by
  obtain ⟨hproc, -, -, -, -, -, hdisk, -, -⟩ := h
  have hdisk' : ∀ i f, st.file i = some f → ∃ img sz, f = OsFile.ofDisk img sz :=
    fun i f hf => let ⟨img, sz, _, h⟩ := (hdisk i f hf).2; ⟨img, sz, h⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro fd d h; simp [hproc, ProcState.empty] at h
  · intro b m h; simp [hproc, ProcState.empty] at h
  · intro b1 m1 _ _ h; simp [hproc, ProcState.empty] at h
  · intro t c h; simp [hproc, ProcState.empty] at h
  · intro t1 c1 _ _ h; simp [hproc, ProcState.empty] at h
  · intro i f hf
    obtain ⟨img, sz, hsz, rfl⟩ := (hdisk i f hf).2; simp [OsFile.ofDisk, hsz]
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
  · intro t ti h; simp at h
  · intro i m c hm hc
    simp only [metaMap, GMap.lookup_fmap] at hm
    cases hfo : st.fs.files !! i with
    | none => simp [hfo] at hm
    | some f => simp [hfo] at hm; subst hm; simp [initMeta] at hc

/-! ## The tree's start -/

section treeAlloc
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The claims a switch allocates, from the empty authority. -/
theorem claims_alloc (V : Hist) : ∀ js : List Ino, js.Nodup →
    ⊢ gAuth hL hL.γn (∅ : GMap (Ino × NameSet) NamesH) ==∗
      gAuth hL hL.γn (claimsInit V js) ∗
      [∗list] j ∈ js, gElem hL hL.γn (j, NameSet.except []) (DFrac.own 1)
        (namesOf V j (.except []))
  | [], _ => by
    rw [show claimsInit V [] = ∅ from rfl]
    iintro H
    imodintro
    iframe H
    iapply BigSepL.bigSepL_nil.2; itrivial
  | j :: js, hnd => by
    have hj : j ∉ js := (List.nodup_cons.1 hnd).1
    iintro H
    imod claims_alloc V js (List.nodup_cons.1 hnd).2 $$ H with ⟨H, Hs⟩
    have hfresh : claimsInit V js !! (j, .except []) = none := by
      rw [claimsInit_lookup]; simp [hj]
    imod gAuth_insert hL _ _ _ (namesOf V j (.except [])) hfresh $$ H with ⟨H, Hj⟩
    imodintro
    rw [show claimsInit V (j :: js) =
      <[(j, NameSet.except []) := namesOf V j (.except [])]> (claimsInit V js) from rfl]
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- The log's map, from the empty authority. -/
theorem log_alloc (log : List LogEntry) :
    ⊢ gAuth hL hL.γlog (∅ : GMap Nat LogEntry) ==∗ gAuth hL hL.γlog (logMap log) := by
  unfold gAuth
  letI := hL.osAllG
  iintro H
  imod ghost_map_insert_big (logMap log) (fun k _ h => by simp at h) $$ H with ⟨H, -⟩
  have : logMap log ∪ (∅ : GMap Nat LogEntry) = logMap log := by
    apply GMap.ext; intro k; simp [gmap_lookup_union]
  rw [this]
  imodintro; iexact H

/-- The call permission of every key, from the empty authority. -/
theorem perm_alloc (R : Roots) :
    ⊢ gAuth hL hL.γperm (∅ : GMap GoString Unit) ==∗
      [∗map] r ↦ u ∈ permMap R, gElem hL hL.γperm r (DFrac.own 1) u := by
  unfold gAuth gElem
  letI := hL.osAllG
  iintro H
  imod ghost_map_insert_big (permMap R) (fun k _ h => by simp at h) $$ H with ⟨-, H⟩
  imodintro; iexact H

end treeAlloc

/-- An initial tree is well formed, and coherent with no fd and no call. -/
theorem fsInit_tree {st : OsState} (h : FsInit st) : FsTreeWf st ∧ TreeCohS st ∅ ∅ ∅ := by
  obtain ⟨hproc, hlog, -, hroots, hwf, hnamed, -, hfiles, hdirs⟩ := h
  have htw : FsTreeWf st := by
    refine ⟨hroots, fun n _ => ?_, ?_, ?_, hfiles⟩
    · rw [hlog]; simp only [List.take_nil, List.map_nil, replay, List.foldl_nil]
      refine ⟨hwf, fun i hi => ?_, hdirs⟩
      have := hnamed i hi
      cases hf : st.fs.files !! i with
      | none => exact absurd hf this
      | some f => exact ⟨f, rfl⟩
    · intro fd df h; simp [hproc, ProcState.empty] at h
    · intro fd _; simp [hproc, ProcState.empty]
  have htr : st.tree = st.fs.treeDur := by simp [OsState.tree, hlog, replay]
  obtain ⟨ρ, hρr, hρe⟩ := rootTags_exists hroots.2.1 (htr ▸ hwf)
  have hnil : ∀ (x : Nat) (e : LogEntry), st.fs.metaLog[x]? = some e → False := fun x e he => by
    simp [hlog] at he
  refine ⟨htw, ⟨fun x e he => (hnil x e he).elim,
    fun x y ex ey _ hx => (hnil x ex hx).elim,
    ⟨ρ, ⟨⟨hρr, fun t _ ht j b J he => ?_, fun x e _ he => (hnil x e he).elim⟩,
      fun x e he => (hnil x e he).elim, fun x e he => (hnil x e he).elim⟩,
      ⟨fun t x hx => by simp at hx, fun t x hx => by simp at hx, fun c x t g hx => by simp at hx⟩⟩,
    fun x e he => (hnil x e he).elim, fun fd => by simp [hproc, ProcState.empty],
    fun fd x df hx => by simp at hx, fun t x hx => by simp at hx, fun t x hx => by simp at hx,
    fun t x hx => by simp at hx, fun t x hx => by simp at hx,
    fun t s hs => by simp [hproc, ProcState.empty] at hs⟩⟩
  have ht0 : t = 0 := by rw [hlog] at ht; simpa using ht
  subst ht0
  simp only [prefTree, List.take_zero, List.map_nil, replay, List.foldl_nil] at he
  exact hρe j b J (by rw [htr]; exact he)

theorem os_local_init {GF : BundledGFunctors} (hPre : OsGpreS GF) (st : OsState) (h : FsInit st) :
    ⊢@{IProp GF} |==> ∃ hL : OsGS GF, osCtx hL st ∗ osStart hL st := by
  letI := hPre.osPreAllG
  obtain ⟨hwf, hcoh⟩ := osInit_wf_coh h
  obtain ⟨htw, htc⟩ := fsInit_tree h
  have hproc := h.1
  have hlog : st.fs.metaLog = [] := h.2.1
  imod ghost_map_alloc (GF := GF) (bytesMap st) with ⟨%γb, Hab, Hb⟩
  imod ghost_map_alloc (GF := GF) (metaMap st) with ⟨%γm, Ham, Hm⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 OsFd) with ⟨%γf, Haf, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat TokInfo) with ⟨%γt, Hat, -⟩
  imod ghostVar_alloc (GF := GF) ((∅ : GMap Loc (Option w8 × Bool)), 0) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcm, Hcm, -⟩
  imod ghost_map_alloc (GF := GF)
    (histMap (st.fs.roots, ((st.fs.treeDur, ([] : List LogEntry)) : Hist))) with ⟨%γs, Has, Hs⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 (Ino × DirPhS)) with ⟨%γdfS, Hadfs, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat CallV) with ⟨%γcS, Hacs, -⟩
  imod ghost_map_alloc (GF := GF) (permMap st.fs.roots) with ⟨%γperm, -, Hperm⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap (Ino × NameSet) NamesH) with ⟨%γn, Han, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γlen, Halen, Hlb⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat LogEntry) with ⟨%γlog, Halog, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat CallV) with ⟨%γg, Hag, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 Unit) with ⟨%γo, Hao, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap (LockKind × Ino) w64) with ⟨%γlk, Halk, -⟩
  let V : Hist := (st.fs.treeDur, [])
  ihave Han : gAuth (⟨hPre.osPreAllG, γb, γm, γf, γt, γv, γcm, γs, γdfS, γcS, γperm, γn, γlen,
    γlog, γg, γo, γlk⟩ : OsGS GF) γn (∅ : GMap (Ino × NameSet) NamesH) $$ [Han]
  · unfold gAuth; iexact Han
  imod claims_alloc (⟨hPre.osPreAllG, γb, γm, γf, γt, γv, γcm, γs, γdfS, γcS, γperm, γn, γlen,
    γlog, γg, γo, γlk⟩ : OsGS GF) V (dirsOf V) (GMap.toList_keys_nodup _) $$ Han with ⟨Han, Hcl⟩
  imodintro
  iexists (⟨hPre.osPreAllG, γb, γm, γf, γt, γv, γcm, γs, γdfS, γcS, γperm, γn, γlen,
    γlog, γg, γo, γlk⟩ : OsGS GF)
  isplitl [Hab Ham Haf Hat Hv1 Hcm Has Hadfs Hacs Hag Hao Halk]
  · unfold osCtx osCtxF treeCtx tokRes gAuth gVar commitRes gCommit ofdCtx lockCtx callResS
    isplitl [Hab Ham Haf Hat Hv1]
    · iexists (bytesMap st), (metaMap st), ∅, ∅
      rw [cellView_of_maps_empty (by rw [hproc]; rfl),
        show st.proc.inflight = ∅ by rw [hproc]; rfl, GMap.map_size_empty]
      iframe Hab Ham Haf Hat Hv1
      isplitr
      · ipureintro; exact ⟨hwf, hcoh⟩
      · iapply BigSepM.bigSepM_empty.2; itrivial
    · isplitl [Has Hadfs Hacs Hag Hcm]
      · iexists ∅, ∅, ∅
        rw [hlog]
        iframe Has Hadfs Hacs Hag
        isplitr
        · ipureintro; exact ⟨htw, htc⟩
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        iexists 0
        iframe Hcm
        ipureintro; intro y hy; exact absurd hy (Nat.not_lt_zero _)
      rw [show st.proc.ofds = ∅ by rw [hproc]; rfl]
      unfold gAuth
      iframe Hao
      isplitr
      · ipureintro; intro fd hfd; simp [hproc, ProcState.empty] at hfd
      iexists ∅
      iframe Halk
      ipureintro
      refine ⟨fun k fd1 d1 _ _ h1 => by simp [hproc, ProcState.empty] at h1, fun k i fd => ?_⟩
      simp [hproc, ProcState.empty]
  · unfold osStart osStartF treeStart osSwitchKitG
    iframe Han Hcl
    unfold gElem gAuth gVar histMap
    iframe Hb Hm Hv2
    ihave Hs := (show ([∗map] k ↦ v ∈ ({[() := (st.fs.roots,
          ((st.fs.treeDur, ([] : List LogEntry)) : Hist))]} : GMap Unit (Roots × Hist)),
          ghostMapElem (GF := GF) γs k (DFrac.own 1) v) ⊢
        ghostMapElem γs () (DFrac.own 1)
          ((st.fs.roots, ((st.fs.treeDur, ([] : List LogEntry)) : Hist)) : Roots × Hist) from
      (BigSepM.bigSepM_singleton (M := GMap Unit)
        (Φ := fun (k : Unit) (v : Roots × Hist) =>
          ghostMapElem (GF := GF) γs k (DFrac.own 1) v)).1) $$ Hs
    iframe Hs Halen Hlb
    icases (BigSepM.bigSepM_delete (M := GMap GoString)
      (Φ := fun (r' : GoString) (u : Unit) => ghostMapElem (GF := GF) γperm r' (DFrac.own 1) u)
      (permMap_lookup st.fs.roots [] (.inl rfl))).1 $$ Hperm with ⟨Hp0, Hperm⟩
    iframe Hp0 Hperm
    isplitr
    · ipureintro; exact ⟨htw.roots, namesCoh_init V (fun x e he => by simp [V] at he)⟩
    dsimp only
    rw [logMap_nil]
    iexact Halog

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

/-- The ghost state can be allocated for every initial state of the semantics (`fs_semantics`'s
`initLocal` is `fs_interp`'s `initP`, `FsInit`). -/
instance fs_init_compat : ExtInitCompat fsExt where
  initgP_of_init _ _ := trivial
  initP_of_init _ _ h := h

end Fs
end Perennial
