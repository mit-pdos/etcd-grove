/-
Crash-aware specs of `os` over a crash invariant generic in a predicate on the file's states:
the definitions (Lean-first, no Rocq counterpart).

`CrashFile.lean`'s invariant (`cfInv N p R γ Good`) holds half of every byte of the file at `p`
(of its inode) and half of the tree's history, and asks `CrashOk Good` of its state. A client such
as minibolt needs three things more:

* **Any predicate on states** (`csInv N p R γ Good Ok`): the specs move the state and ask the
  caller to show `Ok` of each state the call passes through; `Ok` is the caller's, so a premise on
  crashes (`FileOkS Q Good`, which uses the crash's facts `CrashSeenR`) or a predicate tracking
  more than what a crash leaves can be used. The tree's part stays the invariant's: every crash of
  the history leaves `p` naming nothing (then `Good none`) or the state's file (`TreeOkI`).
  `csInv_crash_keep` takes the tree and the file after a crash from the invariant's halves, given
  `FileOkS Q Good` of the state's file.
* **Bytes frozen at a discarded fraction**: the state's bytes `[fa, fb)` sit in the invariant
  as `osBytes ... DFrac.discard` (persistent: minibolt's committed pages, which readers hold too),
  and the others at a half each, the invariant's and the caller's. A write never touches the frozen
  bytes (`CSt.Wf`), and `cs_freeze` freezes more of them.
* **A truncate in flight** (`CBusy.trunc`), besides a `pwrite` (`CBusy.write`): the token holds the
  whole `OsMeta` (and, for a `pwrite`, the bytes it announced, which a crash sees through it).

Mappings are allowed (the state's `OsMeta` may have any): the specs pass the client's halves of the
mapped cells through (`mcellsAny`).

A state is the file's inode and `CSt` (or none at `p`). The caller's part is `csOwnF` of the file
(which the operations of `CrashStOps.lean` move) and its half of the history (`csOwn`). A crash
sees the file through `CSt.vmeta`, `CSt.vruns` (`CSt.runs`, one run per byte, empty for a byte a
write in flight took, and the token's bytes) and `CSt.toks`; `FileOkS` is `FileOkQ` (`CrashFileQ.lean`) of that view, and
`fileOkS_idle`/`fileOkS_write` reduce it to `FileOkQ` of the corresponding `CFile` file (the same
bytes at other fractions: what a crash sees does not depend on fractions, `RunsSub`).
-/
module

public import Proof.os.CrashOps
public import Proof.os.CrashFileQ

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-! ## The states -/

/-- The change in flight on a file: none, a `pwrite` of `data` at `off` (token `t`, change number
`n`), or a growing truncate to `sz` (token `t`, change number `n`). -/
inductive CBusy where
  | idle
  | write (t off : Nat) (data : List w8) (n : Nat)
  | trunc (t sz n : Nat)

/-- A file's state: its `OsMeta` `m` (as the token holds it, while a change is in flight), all its
bytes `bs`, the frozen bytes `[fa, fb)`, and the change in flight. -/
structure CSt where
  m : OsMeta
  bs : List ByteG
  fa : Nat
  fb : Nat
  busy : CBusy

/-- The change number `n` of a write of `data` at `off` from `m`, `bs` is later than every
candidate of the bytes it announces: those it takes below the size, those `m` knows past it. -/
def PwFresh (m : OsMeta) (bs : List ByteG) (off : Nat) (data : List w8) (n : Nat) : Prop :=
  (∀ x ∈ cfRange m bs off data.length, ∀ q ∈ x.2, q.2 < n) ∧
    (∀ b c, m.size ≤ b → m.pc b = some c → ∀ q ∈ c, q.2 < n) ∧ 0 < n

/-- The candidates `zs` a write reports of the bytes it grew the file over (from `m.size`) are
those `m` knew. -/
def ZsOk (m : OsMeta) (zs : List Cands) : Prop :=
  ∀ j c, m.pc (m.size + j) = some c → j < zs.length → zs[j]? = some c

/-- A file's state: absent, or its inode and `CSt`. -/
abbrev CState := Option (Ino × CSt)

/-- The inode of the state's file. -/
def sIno : CState → Option Ino
  | none => none
  | some (i, _) => some i

/-- What `p` names now: nothing, or the state's file. -/
def SPathOk (p : GoString) (R : Roots) (s : CState) (V : Hist) : Prop :=
  match s with
  | none => lookupH R V p = none
  | some (i, _) => lookupH R V p = some (.file i)

def CBusy.enc : CBusy → Option ((Nat × Nat × List w8 × Nat) ⊕ (Nat × Nat × Nat))
  | .idle => none
  | .write t off data n => some (.inl (t, off, data, n))
  | .trunc t sz n => some (.inr (t, sz, n))

instance CBusy.countable : Pos.Countable CBusy :=
  Pos.Countable.ofInjective (fun b => Pos.Countable.encode b.enc)
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [CBusy.enc])

instance CSt.countable : Pos.Countable CSt :=
  Pos.Countable.ofInjective (fun s => Pos.Countable.encode (s.m, s.bs, s.fa, s.fb, s.busy))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

namespace CSt

/-- Byte `k` is frozen. -/
def frozen (s : CSt) (k : Nat) : Bool := decide (s.fa ≤ k ∧ k < s.fb)

/-- Byte `k` is one a write in flight took. -/
def taken (s : CSt) (k : Nat) : Bool :=
  match s.busy with
  | .write _ off data _ => decide (cfLo s.m off ≤ k ∧ k < cfHi s.m off data.length)
  | _ => false

/-- The invariant's fraction of byte `k`. -/
def frac (s : CSt) (k : Nat) : DFrac :=
  if s.frozen k then DFrac.discard else DFrac.own (1 : Qp).half

/-- The `OsMeta` a crash sees: the token's while a change is in flight. -/
def vmeta (s : CSt) : OsMeta :=
  match s.busy with
  | .idle => s.m
  | .write _ off data _ => cfMeta s.m off data.length
  | .trunc _ sz _ => s.m.announce (min s.m.size sz) (max s.m.size sz) sz

/-- The runs of bytes a crash sees: one per byte, empty for a byte a write in flight took. -/
def runs (s : CSt) : List (Nat × DFrac × List ByteG) :=
  s.bs.zipIdx.map fun y => (y.2, s.frac y.2, if s.taken y.2 then [] else [y.1])

/-- The runs a crash sees: the bytes' own (`runs`), and the bytes a write in flight took, as its
token holds them (their candidates with the write's announced). -/
def vruns (s : CSt) : List (Nat × DFrac × List ByteG) :=
  match s.busy with
  | .write _ off data n =>
      (cfLo s.m off, DFrac.own 1, pwAnn data n (cfRange s.m s.bs off data.length)) :: s.runs
  | .trunc _ sz _ => (min s.m.size sz, DFrac.own 1, []) :: s.runs
  | .idle => s.runs

/-- The change in flight, as its token records it. -/
def toks (p : Ino) (s : CSt) : List (Nat × TokInfo) :=
  match s.busy with
  | .idle => []
  | .write t off data n => [(t, ⟨p, .write off data, n, s.m,
      pwAnn data n (cfRange s.m s.bs off data.length)⟩)]
  | .trunc t sz n => [(t, ⟨p, .truncate sz, n, s.m, rsAnn n []⟩)]

/-- What the specs keep of a state: all the bytes, the frozen ones inside, a write in flight
misses them (and so does what it appends, which starts at the size), a truncate grows. -/
def Wf (s : CSt) : Prop :=
  s.bs.length = s.m.size ∧ s.fa ≤ s.fb ∧ s.fb ≤ s.m.size ∧
  match s.busy with
  | .idle => True
  | .write _ off data _ => off + data.length ≤ s.fa ∨ s.fb ≤ off
  | .trunc _ sz _ => s.m.size ≤ sz

theorem frozen_out (s : CSt) (k : Nat) (h : k < s.fa ∨ s.fb ≤ k) : s.frozen k = false := by
  simp only [frozen, decide_eq_false_iff_not]; omega

theorem frozen_in (s : CSt) (k : Nat) (h1 : s.fa ≤ k) (h2 : k < s.fb) : s.frozen k = true := by
  simp only [frozen, decide_eq_true_eq]; omega

theorem frac_out (s : CSt) (k : Nat) (h : k < s.fa ∨ s.fb ≤ k) :
    s.frac k = DFrac.own (1 : Qp).half := by
  simp only [frac, frozen_out s k h, Bool.false_eq_true, if_false]

theorem frac_in (s : CSt) (k : Nat) (h1 : s.fa ≤ k) (h2 : k < s.fb) : s.frac k = DFrac.discard := by
  simp only [frac, frozen_in s k h1 h2, if_true]

theorem taken_out (s : CSt) (k : Nat)
    (h : ∀ t off data n, s.busy = .write t off data n → k < cfLo s.m off ∨ cfHi s.m off data.length ≤ k) :
    s.taken k = false := by
  unfold taken
  rcases hb : s.busy with _ | ⟨t, off, data, n⟩ | _ <;> dsimp only
  have := h t off data n hb
  simp only [decide_eq_false_iff_not]; omega

theorem taken_in (s : CSt) (k t off : Nat) (data : List w8) (n : Nat) (hb : s.busy = .write t off data n)
    (h1 : cfLo s.m off ≤ k) (h2 : k < cfHi s.m off data.length) : s.taken k = true := by
  unfold taken; rw [hb]; simp only [decide_eq_true_eq]; omega

end CSt

/-- Every file a crash under the premise `Q` may leave of the state `s` of the file of inode `i`
is `Good`, given the crash's facts. -/
def FileOkS (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (i : Ino) (s : CSt) :
    Prop :=
  ∀ f, FileCrashedR s.vmeta s.vruns (some f) → CrashSeenR Q i s.vmeta s.vruns (s.toks i) (some f) →
    Good (some f)

/-! ## What a crash sees does not depend on fractions -/

/-- Every byte of the runs `rs'` is one of `rs`. -/
def RunsSub (rs' rs : List (Nat × DFrac × List ByteG)) : Prop :=
  ∀ r' ∈ rs', ∀ k (hk : k < r'.2.2.length), ∃ r ∈ rs, ∃ k', ∃ hk' : k' < r.2.2.length,
    r.2.2[k'] = r'.2.2[k] ∧ r.1 + k' = r'.1 + k

theorem fileCrashedR_sub {m : OsMeta} {rs rs' : List (Nat × DFrac × List ByteG)}
    {fo : Option OsFile} (hs : RunsSub rs' rs) (h : FileCrashedR m rs fo) :
    FileCrashedR m rs' fo := by
  intro f hf
  obtain ⟨h0, h1, h2, h3, h4⟩ := h f hf
  refine ⟨h0, h1, h2, fun r' hr' k hk hkf => ?_, h4⟩
  obtain ⟨r, hr, k', hk', he, hpos⟩ := hs r' hr' k hk
  have := h3 r hr k' hk' (by rw [hpos]; exact hkf)
  rw [hpos, he] at this; exact this

theorem crashSeenR_sub {Q : OsState → OsState → Prop} {i : Ino} {m : OsMeta}
    {rs rs' : List (Nat × DFrac × List ByteG)} {ts : List (Nat × TokInfo)}
    {fo : Option OsFile} (hs : RunsSub rs' rs) (h : CrashSeenR Q i m rs ts fo) :
    CrashSeenR Q i m rs' ts fo := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hwfs, hcoh, hcr, hQ, hst', hm, hxs, hoth, hts⟩ := h
  refine ⟨st, st', Γb, Γm, Γf, Γt, hwfs, hcoh, hcr, hQ, hst', hm, fun r' hr' k hk => ?_, hoth, hts⟩
  obtain ⟨r, hr, k', hk', he, hpos⟩ := hs r' hr' k hk
  rw [← hpos, ← he]; exact hxs r hr k' hk'

theorem RunsSub.cons {rs' rs : List (Nat × DFrac × List ByteG)} (r : Nat × DFrac × List ByteG)
    (h : RunsSub rs' rs) : RunsSub (r :: rs') (r :: rs) := by
  intro r' hr' k hk
  rcases List.mem_cons.1 hr' with rfl | hr'
  · exact ⟨r', List.mem_cons_self, k, hk, rfl, rfl⟩
  · obtain ⟨r0, hr0, k', hk', he, hp⟩ := h r' hr' k hk
    exact ⟨r0, List.mem_cons_of_mem _ hr0, k', hk', he, hp⟩

theorem CSt.runs_getElem (s : CSt) (j : Nat) (hj : j < s.bs.length) :
    ∃ r ∈ s.runs, r = (j, s.frac j, if s.taken j then [] else [s.bs[j]]) := by
  refine ⟨_, List.getElem_mem (l := s.runs) (n := j) (by simp [CSt.runs, hj]), ?_⟩
  simp [CSt.runs, List.getElem_zipIdx]

/-- A byte a crash sees in a state's runs is one of its bytes, not taken. -/
theorem CSt.runsSub_of (s : CSt) (rs' : List (Nat × DFrac × List ByteG))
    (h : ∀ r' ∈ rs', ∀ k (hk : k < r'.2.2.length), ∃ hj : r'.1 + k < s.bs.length,
      s.bs[r'.1 + k] = r'.2.2[k] ∧ s.taken (r'.1 + k) = false) : RunsSub rs' s.runs := by
  intro r' hr' k hk
  obtain ⟨hj, he, ht⟩ := h r' hr' k hk
  obtain ⟨r, hr, rfl⟩ := s.runs_getElem _ hj
  exact ⟨_, hr, 0, by simp [ht], by simp [ht, he], rfl⟩

/-- All of a state's bytes, as one run, when no write in flight took any. -/
theorem CSt.runsSub_whole (s : CSt) (dq : DFrac) (ht : ∀ k, s.taken k = false) :
    RunsSub [(0, dq, s.bs)] s.runs := by
  refine s.runsSub_of _ fun r' hr' k hk => ?_
  simp only [List.mem_singleton] at hr'; subst hr'
  exact ⟨by simpa using hk, by simp, by simpa using ht k⟩

/-- **An idle state's crash obligation is the `CFile`'s** (`FileOkQ`, whose lemmas apply). -/
theorem fileOkS_idle {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {i : Ino}
    (s : CSt) (hb : s.busy = .idle) (h : FileOkQ Q Good i (s.m, s.bs, none)) :
    FileOkS Q Good i s := by
  have hsub : RunsSub [(0, DFrac.own (1 : Qp).half, s.bs)] s.vruns := by
    rw [show s.vruns = s.runs by simp [CSt.vruns, hb]]
    refine s.runsSub_of _ fun r' hr' k hk => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    refine ⟨by simpa using hk, by simp, ?_⟩
    simp [CSt.taken, hb]
  have hm : s.vmeta = s.m := by simp [CSt.vmeta, hb]
  have ht : s.toks i = [] := by simp [CSt.toks, hb]
  intro f hc hs
  rw [hm] at hc hs; rw [ht] at hs
  exact h f (fileCrashedR_sub hsub hc) (crashSeenR_sub hsub hs)

/-- **A writing state's crash obligation is the `CFile`'s.** -/
theorem fileOkS_write {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {i : Ino}
    (s : CSt) {t off : Nat} {data : List w8} {n : Nat} (hb : s.busy = .write t off data n)
    (hl : s.bs.length = s.m.size) (h : FileOkQ Q Good i (s.m, s.bs, some (t, off, data, n))) :
    FileOkS Q Good i s := by
  have hsub : RunsSub (fRuns (s.m, s.bs, some (t, off, data, n))) s.vruns := by
    rw [show s.vruns = (cfLo s.m off, DFrac.own 1, pwAnn data n (cfRange s.m s.bs off data.length))
      :: s.runs by simp [CSt.vruns, hb]]
    refine RunsSub.cons _ (s.runsSub_of _ fun r' hr' k hk => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · simp only [List.length_take] at hk
      refine ⟨by simp only; omega, by simp, ?_⟩
      simp only [CSt.taken, hb, decide_eq_false_iff_not]; omega
    · simp only [List.length_drop] at hk
      refine ⟨by simp only; omega, by simp, ?_⟩
      simp only [CSt.taken, hb, decide_eq_false_iff_not]; omega
  have hm : s.vmeta = cfMeta s.m off data.length := by simp [CSt.vmeta, hb]
  have ht : s.toks i = cToks i (s.m, s.bs, some (t, off, data, n)) := by
    simp [CSt.toks, cToks, hb]
  intro f hc hs
  rw [hm] at hc hs; rw [ht] at hs
  exact h f (fileCrashedR_sub hsub hc) (crashSeenR_sub hsub hs)

/-! ## The resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
/-- Byte `k` of the file `p` at the fraction `d k`, if `c k`. -/
def cByte (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (k : Nat) (x : ByteG) : IProp GF :=
  if c k then osByte (L := L) p k (d k) x else emp

/-- The bytes `l` from `off`, each as `cByte`. -/
def cBytes (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat) (l : List ByteG) :
    IProp GF :=
  [∗list] k ↦ x ∈ l, cByte (L := L) p d c (off + k) x

instance cBytes_timeless (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat)
    (l : List ByteG) : Timeless (cBytes (L := L) p d c off l) := by
  unfold cBytes cByte
  refine BigSepL.bigSepL_timeless ?_
  intro k x _
  split <;> infer_instance

theorem cBytes_append (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat)
    (l1 l2 : List ByteG) :
    cBytes (L := L) p d c off (l1 ++ l2) ⊣⊢
      cBytes (L := L) p d c off l1 ∗ cBytes (L := L) p d c (off + l1.length) l2 := by
  unfold cBytes
  refine BigSepL.bigSepL_append.trans ?_
  rw [BigSepL.bigSepL_eq_of_forall_eq (l := l2) (Ψ := fun k x => cByte (L := L) p d c (off + l1.length + k) x)
    (fun {k x} => by congr 1; omega)]
  exact .rfl

theorem cBytes_nil (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat) :
    cBytes (L := L) p d c off [] ⊣⊢ emp := .rfl

/-- Bytes all present at one fraction are a run. -/
theorem cBytes_full (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (dq : DFrac) :
    ∀ (off : Nat) (l : List ByteG), (∀ k < l.length, c (off + k) = true ∧ d (off + k) = dq) →
    cBytes (L := L) p d c off l ⊣⊢ osBytes (L := L) p off dq l
  | off, [], _ => by
    refine (cBytes_nil p d c off).trans (osBytes_nil' p off dq).symm
  | off, x :: l, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero] at h0
    have ih := cBytes_full p d c dq (off + 1) l (fun k hk => by
      have := h (k + 1) (by simp only [List.length_cons]; omega); rwa [show off + (k + 1) = off + 1 + k by omega] at this)
    unfold cBytes at ih ⊢
    refine BigSepL.bigSepL_cons.trans ?_
    unfold osBytes
    refine BiEntails.trans ?_ (bytesG_cons _ _ _ _ _ _).symm
    refine sep_congr ?_ ?_
    · unfold cByte; simp only [Nat.add_zero, h0.1, h0.2, if_true]; exact .rfl
    · rw [BigSepL.bigSepL_eq_of_forall_eq (l := l)
        (Ψ := fun k x => cByte (L := L) p d c (off + 1 + k) x) (fun {k x} => by congr 1; omega)]
      exact ih

/-- Bytes all absent are nothing. -/
theorem cBytes_none (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) :
    ∀ (off : Nat) (l : List ByteG), (∀ k < l.length, c (off + k) = false) →
    cBytes (L := L) p d c off l ⊣⊢ emp
  | off, [], _ => .rfl
  | off, x :: l, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero] at h0
    have ih := cBytes_none p d c (off + 1) l (fun k hk => by
      have := h (k + 1) (by simp only [List.length_cons]; omega); rwa [show off + (k + 1) = off + 1 + k by omega] at this)
    unfold cBytes at ih ⊢
    refine BigSepL.bigSepL_cons.trans ?_
    rw [BigSepL.bigSepL_eq_of_forall_eq (l := l)
      (Ψ := fun k x => cByte (L := L) p d c (off + 1 + k) x) (fun {k x} => by congr 1; omega)]
    refine (sep_congr (show cByte (L := L) p d c (off + 0) x ⊣⊢ emp by
      unfold cByte; simp only [Nat.add_zero, h0, Bool.false_eq_true, if_false]; exact .rfl) ih).trans ?_
    exact ⟨by iintro ⟨-, -⟩; iempintro, by iintro -; isplitl <;> iempintro⟩

/-- Bytes whose fractions and presence agree where they are. -/
theorem cBytes_congr (p : Ino) (d d' : Nat → DFrac) (c c' : Nat → Bool) :
    ∀ (off : Nat) (l : List ByteG),
    (∀ k < l.length, c (off + k) = c' (off + k) ∧ (c (off + k) = true → d (off + k) = d' (off + k))) →
    cBytes (L := L) p d c off l ⊣⊢ cBytes (L := L) p d' c' off l
  | off, [], _ => .rfl
  | off, x :: l, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero] at h0
    have ih := cBytes_congr p d d' c c' (off + 1) l (fun k hk => by
      have := h (k + 1) (by simp only [List.length_cons]; omega); rwa [show off + (k + 1) = off + 1 + k by omega] at this)
    unfold cBytes at ih ⊢
    refine BigSepL.bigSepL_cons.trans (BiEntails.trans ?_ BigSepL.bigSepL_cons.symm)
    rw [BigSepL.bigSepL_eq_of_forall_eq (l := l)
      (Ψ := fun k x => cByte (L := L) p d c (off + 1 + k) x) (fun {k x} => by congr 1; omega),
      BigSepL.bigSepL_eq_of_forall_eq (l := l) (Φ := fun k x => cByte (L := L) p d' c' (off + (k + 1)) x)
      (Ψ := fun k x => cByte (L := L) p d' c' (off + 1 + k) x) (fun {k x} => by congr 1; omega)]
    refine sep_congr ?_ ih
    unfold cByte
    simp only [Nat.add_zero, h0.1]
    split
    · rename_i hc; rw [h0.2 (h0.1.trans hc)]; exact .rfl
    · exact .rfl

/-- Bytes as two sets, pointwise. -/
theorem cBytes_sep (p : Ino) (d d1 d2 : Nat → DFrac) (c c1 c2 : Nat → Bool) (off : Nat)
    (l : List ByteG)
    (h : ∀ k x, l[k]? = some x →
      (cByte (L := L) p d c (off + k) x ⊣⊢ cByte (L := L) p d1 c1 (off + k) x ∗
        cByte (L := L) p d2 c2 (off + k) x)) :
    cBytes (L := L) p d c off l ⊣⊢ cBytes (L := L) p d1 c1 off l ∗ cBytes (L := L) p d2 c2 off l := by
  unfold cBytes
  refine BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  constructor
  · exact BigSepL.bigSepL_mono fun {k x} hk => (h k x hk).1
  · exact BigSepL.bigSepL_mono fun {k x} hk => (h k x hk).2

/-- One byte at two halves is the byte whole. -/
theorem osByte_halves (p : Ino) (k : Nat) (x : ByteG) :
    osByte (L := L) p k (DFrac.own 1) x ⊣⊢
      osByte (L := L) p k (DFrac.own (1 : Qp).half) x ∗ osByte (L := L) p k (DFrac.own (1 : Qp).half) x := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (p, k) (1 : Qp).half (1 : Qp).half x
  rw [Qp.half_add_half] at h
  exact h

/-- The state's bytes the invariant holds: the frozen ones discarded, the others but those a write
in flight took at a half. -/
def invBytes (p : Ino) (s : CSt) : IProp GF :=
  cBytes (L := L) p s.frac (fun k => !s.taken k) 0 s.bs

/-- The state's bytes the caller holds: a half of each but the frozen ones and those a write in
flight took. -/
def thrBytes (p : Ino) (s : CSt) : IProp GF :=
  cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half) (fun k => !s.taken k && !s.frozen k) 0 s.bs

theorem invBytes_runs (p : Ino) (s : CSt) :
    invBytes (L := L) p s ⊣⊢ [∗list] r ∈ s.runs, osBytes (L := L) p r.1 r.2.1 r.2.2 := by
  unfold CSt.runs
  rw [BigSepL.bigSepL_map]
  refine BiEntails.trans ?_ BigSepL.bigSepL_zip_seq.symm
  unfold invBytes cBytes
  have h : ∀ k x, cByte (L := L) p s.frac (fun k => !s.taken k) (0 + k) x ⊣⊢
      osBytes (L := L) p (0 + k) (s.frac (0 + k)) (if s.taken (0 + k) then [] else [x]) := by
    intro k x
    unfold cByte
    by_cases ht : s.taken (0 + k) = true
    · simp only [ht, Bool.not_true, Bool.false_eq_true, if_false, if_true]
      exact ⟨(osBytes_nil' (L := L) _ _ _).2, (osBytes_nil' (L := L) _ _ _).1⟩
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.not_false, if_true, Bool.false_eq_true, if_false]
      unfold osBytes osByte
      refine BiEntails.trans ?_ (bytesG_cons _ _ _ _ _ _).symm
      exact ⟨by iintro H; iframe; iapply (bytesG_nil _ _ _ _).2; iempintro,
        by iintro ⟨H, -⟩; iexact H⟩
  constructor
  · exact BigSepL.bigSepL_mono_of_forall fun {k x} => (h k x).1
  · exact BigSepL.bigSepL_mono_of_forall fun {k x} => (h k x).2

/-- What the invariant holds of a state's `OsMeta`: half of it, or the token of the change in
flight. -/
def metaRes (p : Ino) (s : CSt) : IProp GF :=
  match s.busy with
  | .idle => osMeta (L := L) p (DFrac.own (1 : Qp).half) s.m
  | .write t off data n => pwTok (L := L) t p off data s.m (cfRange s.m s.bs off data.length) n
  | .trunc t sz n => rsTok (L := L) t p sz s.m [] n

/-- What the invariant holds of a state. -/
def invResS : CState → IProp GF
  | none => iprop(emp)
  | some (i, s) => iprop(metaRes (L := L) i s ∗ invBytes (L := L) i s)

/-- What the caller holds of a state: the other half of the `OsMeta`, while no change is in
flight, and its half of the bytes. -/
def thrResS : CState → IProp GF
  | none => iprop(emp)
  | some (i, s) => iprop((match s.busy with
      | .idle => osMeta (L := L) i (DFrac.own (1 : Qp).half) s.m
      | _ => emp) ∗ thrBytes (L := L) i s)

instance invResS_timeless (s : CState) : Timeless (invResS (L := L) s) := by
  rcases s with _ | ⟨i, s⟩
  · unfold invResS; infer_instance
  · rcases s with ⟨m, bs, fa, fb, _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩⟩ <;>
      unfold invResS invBytes metaRes <;> dsimp only
    · infer_instance
    · unfold pwTok osTok; infer_instance
    · unfold rsTok osTok; infer_instance

/-- The crash invariant of the file at `p` (the roots `R`): its state `s` (named by `γ`), the
invariant's part of it, half of the tree's history `V`, `Ok s`, and that every crash of the
history leaves `p` naming nothing (then `Good none`) or the state's file (`TreeOkI`). -/
def csInv (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (Ok : CState → Prop) : IProp GF :=
  inv N iprop(∃ (s : CState) (V : Hist), ghostVar γ (1 : Qp).half s ∗ invResS (L := L) s ∗
    osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜Ok s ∧ TreeOkI Good p R (sIno s) V⌝)

instance csInv_persistent (N : Namespace) (p : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) :
    Persistent (csInv (L := L) N p R γ Good Ok) := by unfold csInv; infer_instance

/-- What the specs keep of a state. -/
def CsWf : CState → Prop
  | none => True
  | some (_, s) => s.Wf

/-- The caller's part of the file in the state `s`, without the tree. -/
def csOwnF (γ : GName) (s : CState) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half s ∗ thrResS (L := L) s ∗ ⌜CsWf s⌝)

/-- The caller's part of the file at `p` in the state `s`, the history being `V`. -/
def csOwn (p : GoString) (R : Roots) (γ : GName) (s : CState) (V : Hist) : IProp GF :=
  iprop(csOwnF (L := L) γ s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜SPathOk p R s V⌝)

/-- The state of the file `i` a generation starts with, as `osFileStart` gives it, nothing
frozen. -/
def csStart (i : Ino) (f : OsFile) : CState :=
  some (i, ⟨initMeta f, f.contents.map durB, 0, 0, .idle⟩)

theorem csStart_wf (i : Ino) (f : OsFile) : CsWf (csStart i f) :=
  ⟨by simp [initMeta, contents_length], Nat.le_refl _, Nat.zero_le _, trivial⟩

/-- What a generation's start gives of an idle state with nothing frozen: nothing, or its file
whole. -/
def csStartRes : CState → IProp GF
  | none => iprop(emp)
  | some (i, s) => iprop(osMeta (L := L) i (DFrac.own 1) s.m ∗ osBytes (L := L) i 0 (DFrac.own 1) s.bs)

/-- An idle state's bytes, invariant's and caller's together, nothing frozen: the whole run. -/
theorem idleBytes_whole (p : Ino) (s : CSt) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) :
    osBytes (L := L) p 0 (DFrac.own 1) s.bs ⊣⊢ invBytes (L := L) p s ∗ thrBytes (L := L) p s := by
  have hfr : ∀ k, s.frozen k = false := fun k => by simp only [CSt.frozen]; simp; omega
  have hta : ∀ k, s.taken k = false := fun k => by simp [CSt.taken, hb]
  unfold invBytes thrBytes
  refine BiEntails.trans ?_ (cBytes_sep p (fun _ => DFrac.own 1) _ _ (fun _ => true) _ _ 0 s.bs
    fun k x _ => ?_)
  · exact (cBytes_full p _ _ _ 0 s.bs fun _ _ => ⟨rfl, rfl⟩).symm
  · unfold cByte; simp only [hfr, hta, Bool.not_false, Bool.and_self, if_true, CSt.frac,
      Bool.false_eq_true, if_false]
    exact osByte_halves p _ x

theorem csStartRes_split (s : CState) (hs : ∀ i x, s = some (i, x) → x.busy = .idle ∧ x.fb ≤ x.fa) :
    csStartRes (L := L) s ⊢ invResS (L := L) s ∗ thrResS (L := L) s := by
  rcases s with _ | ⟨i, x⟩
  · iintro -; isplitl [] <;> iempintro
  obtain ⟨hb, hf⟩ := hs i x rfl
  rcases x with ⟨m, bs, fa, fb, busy⟩
  dsimp only at hb hf; subst hb
  dsimp only [csStartRes, invResS, thrResS, metaRes]
  iintro ⟨Hm, Hb⟩
  icases (osMeta_halves i m).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (idleBytes_whole i ⟨m, bs, fa, fb, .idle⟩ rfl hf).1 $$ Hb with ⟨Hb1, Hb2⟩
  iframe

/-- **The file at `p` and the history, in an invariant**, if `Ok` of the state and a crash of the
history is `Good`. -/
theorem csInv_alloc (N : Namespace) (p : GoString) (R : Roots) (V : Hist)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (s : CState)
    (hs : ∀ i x, s = some (i, x) → x.busy = .idle ∧ x.fb ≤ x.fa) (hok : Ok s)
    (htr : TreeOkI Good p R (sIno s) V) (hwf : CsWf s) (hp : SPathOk p R s V) :
    ⊢ osTree (L := L) (DFrac.own 1) R V -∗ csStartRes (L := L) s ={⊤}=∗ ∃ γ,
      csInv (L := L) N p R γ Good Ok ∗ csOwn (L := L) p R γ s V := by
  iintro Ht Hf
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (A := CState) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (osTree_halves R V).1 $$ Ht with ⟨Ht1, Ht2⟩
  icases csStartRes_split s hs $$ Hf with ⟨Hi, Hth⟩
  imod inv_alloc N ⊤ (iprop(∃ (s : CState) (V : Hist), ghostVar γ (1 : Qp).half s ∗
      invResS (L := L) s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗
      ⌜Ok s ∧ TreeOkI Good p R (sIno s) V⌝)) $$ [Hv1 Hi Ht1] with #Hinv
  · inext; iexists s, V; iframe; ipureintro; exact ⟨hok, htr⟩
  imodintro
  iexists γ
  unfold csInv csOwn csOwnF
  iframe Hinv Hv2 Hth Ht2
  ipureintro; exact ⟨hwf, hp⟩

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- What a crash may leave of the file `i`, from what the invariant holds of it. -/
theorem metaRes_take (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (i : Ino) (hi : i ∉ D) (x : CSt) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V' -∗ metaRes (L := L) i x -∗
      ([∗list] r ∈ x.runs, osBytes (L := L) i r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR x.vmeta x.vruns fo ∧ (Named V'.now i → fo.isSome) ∧
          CrashSeenR Q i x.vmeta x.vruns (x.toks i) fo⌝ ∗ osFileStartO (L := L') i fo ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (i :: D) true V' ∗
        metaRes (L := L) i x ∗ ([∗list] r ∈ x.runs, osBytes (L := L) i r.1 r.2.1 r.2.2) := by
  iintro Hr Hm Hb
  rcases x with ⟨m, bs, fa, fb, _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩⟩
  · dsimp only [metaRes]
    icases osCrash_take_runs_keep Q L L' D true V' i hi _ m _ $$ Hr Hm Hb
      with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
    iexists fo; iframe; ipureintro; exact h
  · dsimp only [metaRes, pwTok]
    icases Hm with ⟨Ht, %hgap⟩
    icases osCrash_take_tok_keep Q L L' D true V' t _ hi _ $$ Hr Ht Hb
      with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
    iexists fo; iframe; isplitr
    · ipureintro; exact h
    ipureintro; exact hgap
  · dsimp only [metaRes, rsTok]
    icases Hm with ⟨Ht, %hlen⟩
    icases osCrash_take_tok_keep Q L L' D true V' t _ hi _ $$ Hr Ht Hb
      with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
    iexists fo; iframe; isplitr
    · ipureintro; exact h
    ipureintro; exact hlen

/-- **The tree and the file after a crash under the premise `Q`**, from the invariant's part of
the old generation's state `s` and its half of the history `V`: the new generation's history,
whole, and the file at `p` in it, `Good` (by `TreeOkI`, and by `FileOkS` of the state's file);
the old parts come back, so that the invariant can be closed again. -/
theorem csInv_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (p : GoString) (R : Roots) (Good : Option OsFile → Prop) (s : CState) (V : Hist)
    (hD : ∀ i, sIno s = some i → i ∉ D) (htr : TreeOkI Good p R (sIno s) V)
    (hok : ∀ i x, s = some (i, x) → FileOkS Q Good i x) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' -∗ invResS (L := L) s -∗
      osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗
      ∃ fo, ⌜Good fo ∧ TreeCrashed V V'⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗ startAt L' p R V' fo ∗
        (∃ D', crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D' true V') ∗
        invResS (L := L) s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V := by
  iintro Hr Hs Ht
  icases osTreeCrash_take Q L L' D V' _ R V $$ Hr Ht with ⟨%htc, Ht', Hr, Ht⟩
  have hto := htr V' htc
  rcases s with _ | ⟨i, x⟩
  · -- no file at `p`: `p` names nothing after the crash
    rcases hto with ⟨hn, hg⟩ | ⟨i, hi, -⟩
    · iexists none
      iframe Ht' Hs Ht
      isplitr
      · ipureintro; exact ⟨hg, htc⟩
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      iexists D; iexact Hr
    · cases hi
  dsimp only [invResS]
  icases Hs with ⟨Hm, Hb⟩
  icases (invBytes_runs (L := L) i x).1 $$ Hb with Hb
  icases metaRes_take Q L L' D V' i (hD i rfl) x $$ Hr Hm Hb with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
  ihave Hb := (invBytes_runs (L := L) i x).2 $$ Hb
  obtain ⟨hfc, hnm, hseen⟩ := hfo
  rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
  · iexists none
    iframe Ht' Ht Hm Hb
    isplitr
    · ipureintro; exact ⟨hg, htc⟩
    isplitr
    · unfold startAt; rw [hn]; ipureintro; rfl
    iexists (i :: D); iexact Hr
  · cases hi
    obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm (named_of_lookup hl))
    iexists (some f)
    iframe Ht' Ht Hm Hb
    isplitr
    · ipureintro; exact ⟨hok i x rfl f hfc hseen, htc⟩
    isplitl [Hf]
    · unfold startAt; rw [hl]; iexists f; isplitr
      · ipureintro; rfl
      unfold osFileStartO; iexact Hf
    iexists (i :: D); iexact Hr

end crash

end Perennial
