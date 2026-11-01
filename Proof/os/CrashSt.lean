/-
Crash-aware specs of `os` over a crash invariant generic in a predicate on the file's states:
the definitions (Lean-first, no Rocq counterpart).

`CrashFile.lean`'s invariant (`cfInv N p γ Good`) holds half of every byte of the file and asks
`CrashOk Good` of its state. A client such as minibolt needs three things more:

* **Any predicate on states** (`csInv N p γ Ok`): the specs move the state and ask the caller to
  show `Ok` of each state the call passes through; `Ok` is the caller's, so a premise on crashes
  (`CrashOkS Q p Good`, which uses the crash's facts `CrashSeenR`) or a predicate tracking more
  than what a crash leaves can be used. `csInv_crash_keep` takes the file after a crash from the
  invariant's half, given `Ok s → CrashOkS Q p Good s`.
* **Bytes frozen at a discarded fraction**: the state's bytes `[fa, fb)` sit in the invariant
  as `osBytes ... DFrac.discard` (persistent: minibolt's committed pages, which readers hold too),
  and the others at a half each, the invariant's and the caller's. A write never touches the frozen
  bytes (`CSt.Wf`), and `cs_freeze` freezes more of them.
* **A truncate in flight** (`CBusy.trunc`), besides a `pwrite` (`CBusy.write`): the token holds the
  whole `OsMeta`.

Mappings are allowed (the state's `OsMeta` may have any): the specs pass the client's halves of the
mapped cells through (`mcellsAny`).

A crash sees the state through `sMeta`, `sRuns` (one run per byte, empty for a byte a write in
flight took) and `sToks`; `CrashOkS` is `CrashOkQ` (`CrashFileQ.lean`) of that view, and
`crashOkS_idle`/`crashOkS_write` reduce it to `CrashOkQ` of the corresponding `CFile` (the same
bytes at other fractions: what a crash sees does not depend on fractions, `RunsSub`).
-/
module

public import Proof.os.CrashOps
public import Proof.os.CrashFileQ

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The states -/

/-- The change in flight on a file: none, a `pwrite` of `data` at `off` (token `t`), or a
growing truncate to `sz` (token `t`). -/
inductive CBusy where
  | idle
  | write (t off : Nat) (data : List w8)
  | trunc (t sz : Nat)

/-- A file's state: its `OsMeta` `m` (as the token holds it, while a change is in flight), all its
bytes `bs`, the frozen bytes `[fa, fb)`, and the change in flight. -/
structure CSt where
  m : OsMeta
  bs : List (w8 × Bool)
  fa : Nat
  fb : Nat
  busy : CBusy

/-- A file's state: absent, or `CSt`. -/
abbrev CState := Option CSt

def CBusy.enc : CBusy → Option ((Nat × Nat × List w8) ⊕ (Nat × Nat))
  | .idle => none
  | .write t off data => some (.inl (t, off, data))
  | .trunc t sz => some (.inr (t, sz))

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
  | .write _ off data => decide (cfLo s.m off ≤ k ∧ k < cfHi s.m off data.length)
  | _ => false

/-- The invariant's fraction of byte `k`. -/
def frac (s : CSt) (k : Nat) : DFrac :=
  if s.frozen k then DFrac.discard else DFrac.own (1 : Qp).half

/-- The `OsMeta` a crash sees: the token's while a change is in flight. -/
def vmeta (s : CSt) : OsMeta :=
  match s.busy with
  | .idle => s.m
  | .write _ off data => pwMeta s.m off data.length
  | .trunc _ sz => ftMeta s.m sz

/-- The runs of bytes a crash sees: one per byte, empty for a byte a write in flight took. -/
def runs (s : CSt) : List (Nat × DFrac × List (w8 × Bool)) :=
  s.bs.zipIdx.map fun y => (y.2, s.frac y.2, if s.taken y.2 then [] else [y.1])

/-- The change in flight, as its token records it. -/
def toks (p : GoString) (s : CSt) : List (Nat × TokInfo) :=
  match s.busy with
  | .idle => []
  | .write t off data => [(t, ⟨⟨p, .write off data⟩, 1,
      (cfRange s.m s.bs off data.length).map Prod.fst, pwMeta s.m off data.length⟩)]
  | .trunc t sz => [(t, ⟨⟨p, .truncate sz⟩, 1, [], ftMeta s.m sz⟩)]

/-- What the specs keep of a state: all the bytes, the frozen ones inside, a write in flight
misses them (and so does what it appends, which starts at the size), a truncate grows. -/
def Wf (s : CSt) : Prop :=
  s.bs.length = s.m.size ∧ s.fa ≤ s.fb ∧ s.fb ≤ s.m.size ∧
  match s.busy with
  | .idle => True
  | .write _ off data => off + data.length ≤ s.fa ∨ s.fb ≤ off
  | .trunc _ sz => s.m.size ≤ sz

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
    (h : ∀ t off data, s.busy = .write t off data → k < cfLo s.m off ∨ cfHi s.m off data.length ≤ k) :
    s.taken k = false := by
  unfold taken
  rcases hb : s.busy with _ | ⟨t, off, data⟩ | _ <;> dsimp only
  have := h t off data hb
  simp only [decide_eq_false_iff_not]; omega

theorem taken_in (s : CSt) (k t off : Nat) (data : List w8) (hb : s.busy = .write t off data)
    (h1 : cfLo s.m off ≤ k) (h2 : k < cfHi s.m off data.length) : s.taken k = true := by
  unfold taken; rw [hb]; simp only [decide_eq_true_eq]; omega

end CSt

/-- What a crash sees of a state: its `OsMeta`... -/
def sMeta : CState → Option OsMeta
  | none => none
  | some s => some s.vmeta

/-- ... the runs of bytes... -/
def sRuns : CState → List (Nat × DFrac × List (w8 × Bool))
  | none => []
  | some s => s.runs

/-- ... and the change in flight. -/
def sToks (p : GoString) : CState → List (Nat × TokInfo)
  | none => []
  | some s => s.toks p

/-- Every file a crash under the premise `Q` may leave of the state `s` of the file at `p` is
`Good`, given the crash's facts. -/
def CrashOkS (Q : OsState → OsState → Prop) (p : GoString) (Good : Option OsFile → Prop)
    (s : CState) : Prop :=
  ∀ fo, FileCrashedR (sMeta s) (sRuns s) fo → CrashSeenR Q p (sMeta s) (sRuns s) (sToks p s) fo →
    Good fo

/-! ## What a crash sees does not depend on fractions -/

/-- Every byte of the runs `rs'` is one of `rs`. -/
def RunsSub (rs' rs : List (Nat × DFrac × List (w8 × Bool))) : Prop :=
  ∀ r' ∈ rs', ∀ k (hk : k < r'.2.2.length), ∃ r ∈ rs, ∃ k', ∃ hk' : k' < r.2.2.length,
    r.2.2[k'] = r'.2.2[k] ∧ r.1 + k' = r'.1 + k

theorem fileCrashedR_sub {mo : Option OsMeta} {rs rs' : List (Nat × DFrac × List (w8 × Bool))}
    {fo : Option OsFile} (hs : RunsSub rs' rs) (h : FileCrashedR mo rs fo) :
    FileCrashedR mo rs' fo := by
  rcases mo with _ | m
  · exact h
  rcases h with h | ⟨img, h1, h2, h3, h4⟩
  · exact Or.inl h
  refine Or.inr ⟨img, h1, h2, h3, fun r' hr' k x hk hc => ?_⟩
  obtain ⟨hkl, rfl⟩ := List.getElem?_eq_some_iff.1 hk
  obtain ⟨r, hr, k', hk', he, hpos⟩ := hs r' hr' k hkl
  rw [← hpos]
  exact h4 r hr k' _ (by rw [List.getElem?_eq_getElem hk', he]) hc

theorem crashSeenR_sub {Q : OsState → OsState → Prop} {p : GoString} {mo : Option OsMeta}
    {rs rs' : List (Nat × DFrac × List (w8 × Bool))} {ts : List (Nat × TokInfo)}
    {fo : Option OsFile} (hs : RunsSub rs' rs) (h : CrashSeenR Q p mo rs ts fo) :
    CrashSeenR Q p mo rs' ts fo := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hst', hm, hxs, hts, hoth⟩ := h
  refine ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hst', hm, fun r' hr' k hk => ?_, hts,
    fun t ti hti hp => ?_⟩
  · obtain ⟨r, hr, k', hk', he, hpos⟩ := hs r' hr' k hk
    rw [← hpos, ← he]; exact hxs r hr k' hk'
  · rcases hoth t ti hti hp with h | ⟨hq, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨hq, fun r' hr' k hk => ?_⟩
      obtain ⟨r, hr, k', hk', -, hpos⟩ := hs r' hr' k hk
      rw [← hpos]; exact h r hr k' hk'

theorem CSt.runs_getElem (s : CSt) (j : Nat) (hj : j < s.bs.length) :
    ∃ r ∈ s.runs, r = (j, s.frac j, if s.taken j then [] else [s.bs[j]]) := by
  refine ⟨_, List.getElem_mem (l := s.runs) (n := j) (by simp [CSt.runs, hj]), ?_⟩
  simp [CSt.runs, List.getElem_zipIdx]

/-- A byte a crash sees in a state's runs is one of its bytes, not taken. -/
theorem CSt.runsSub_of (s : CSt) (rs' : List (Nat × DFrac × List (w8 × Bool)))
    (h : ∀ r' ∈ rs', ∀ k (hk : k < r'.2.2.length), ∃ hj : r'.1 + k < s.bs.length,
      s.bs[r'.1 + k] = r'.2.2[k] ∧ s.taken (r'.1 + k) = false) : RunsSub rs' s.runs := by
  intro r' hr' k hk
  obtain ⟨hj, he, ht⟩ := h r' hr' k hk
  obtain ⟨r, hr, rfl⟩ := s.runs_getElem _ hj
  exact ⟨_, hr, 0, by simp [ht], by simp [ht, he], rfl⟩

/-- **An idle state's crash obligation is the `CFile`'s** (`CrashOkQ`, whose lemmas apply). -/
theorem crashOkS_idle {Q : OsState → OsState → Prop} {p : GoString} {Good : Option OsFile → Prop}
    (s : CSt) (hb : s.busy = .idle) (h : CrashOkQ Q p Good (some (s.m, s.bs, none))) :
    CrashOkS Q p Good (some s) := by
  have hsub : RunsSub [(0, DFrac.own (1 : Qp).half, s.bs)] s.runs := by
    refine s.runsSub_of _ fun r' hr' k hk => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    refine ⟨by simpa using hk, by simp, ?_⟩
    simp [CSt.taken, hb]
  have hm : s.vmeta = s.m := by simp [CSt.vmeta, hb]
  have ht : s.toks p = [] := by simp [CSt.toks, hb]
  intro fo hc hs
  simp only [sMeta, sRuns, sToks, hm, ht] at hc hs
  exact h fo (fileCrashedR_sub hsub hc) (crashSeenR_sub hsub hs)

/-- **A writing state's crash obligation is the `CFile`'s.** -/
theorem crashOkS_write {Q : OsState → OsState → Prop} {p : GoString} {Good : Option OsFile → Prop}
    (s : CSt) {t off : Nat} {data : List w8} (hb : s.busy = .write t off data)
    (hl : s.bs.length = s.m.size) (h : CrashOkQ Q p Good (some (s.m, s.bs, some (t, off, data)))) :
    CrashOkS Q p Good (some s) := by
  have hsub : RunsSub (cRuns (some (s.m, s.bs, some (t, off, data)))) s.runs := by
    refine s.runsSub_of _ fun r' hr' k hk => ?_
    simp only [cRuns, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · simp only [List.length_take] at hk
      refine ⟨by simp only; omega, by simp, ?_⟩
      simp only [CSt.taken, hb, decide_eq_false_iff_not]; omega
    · simp only [List.length_drop] at hk
      refine ⟨by simp only; omega, by simp, ?_⟩
      simp only [CSt.taken, hb, decide_eq_false_iff_not]; omega
  have hm : s.vmeta = pwMeta s.m off data.length := by simp [CSt.vmeta, hb]
  have ht : s.toks p = cToks p (some (s.m, s.bs, some (t, off, data))) := by
    simp [CSt.toks, cToks, hb]
  intro fo hc hs
  simp only [sMeta, sRuns, sToks, hm, ht] at hc hs
  exact h fo (fileCrashedR_sub hsub hc) (crashSeenR_sub hsub hs)

/-! ## The resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- Byte `k` of the file `p` at the fraction `d k`, if `c k`. -/
def cByte (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (k : Nat) (x : w8 × Bool) : IProp GF :=
  if c k then osByte (L := L) p k (d k) x else emp

/-- The bytes `l` from `off`, each as `cByte`. -/
def cBytes (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat) (l : List (w8 × Bool)) :
    IProp GF :=
  [∗list] k ↦ x ∈ l, cByte (L := L) p d c (off + k) x

instance cBytes_timeless (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat)
    (l : List (w8 × Bool)) : Timeless (cBytes (L := L) p d c off l) := by
  unfold cBytes cByte
  refine BigSepL.bigSepL_timeless ?_
  intro k x _
  split <;> infer_instance

theorem cBytes_append (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat)
    (l1 l2 : List (w8 × Bool)) :
    cBytes (L := L) p d c off (l1 ++ l2) ⊣⊢
      cBytes (L := L) p d c off l1 ∗ cBytes (L := L) p d c (off + l1.length) l2 := by
  unfold cBytes
  refine BigSepL.bigSepL_append.trans ?_
  rw [BigSepL.bigSepL_eq_of_forall_eq (l := l2) (Ψ := fun k x => cByte (L := L) p d c (off + l1.length + k) x)
    (fun {k x} => by congr 1; omega)]
  exact .rfl

theorem cBytes_nil (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat) :
    cBytes (L := L) p d c off [] ⊣⊢ emp := .rfl

/-- Bytes all present at one fraction are a run. -/
theorem cBytes_full (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (dq : DFrac) :
    ∀ (off : Nat) (l : List (w8 × Bool)), (∀ k < l.length, c (off + k) = true ∧ d (off + k) = dq) →
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
theorem cBytes_none (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) :
    ∀ (off : Nat) (l : List (w8 × Bool)), (∀ k < l.length, c (off + k) = false) →
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
theorem cBytes_congr (p : GoString) (d d' : Nat → DFrac) (c c' : Nat → Bool) :
    ∀ (off : Nat) (l : List (w8 × Bool)),
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
theorem cBytes_sep (p : GoString) (d d1 d2 : Nat → DFrac) (c c1 c2 : Nat → Bool) (off : Nat)
    (l : List (w8 × Bool))
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
theorem osByte_halves (p : GoString) (k : Nat) (x : w8 × Bool) :
    osByte (L := L) p k (DFrac.own 1) x ⊣⊢
      osByte (L := L) p k (DFrac.own (1 : Qp).half) x ∗ osByte (L := L) p k (DFrac.own (1 : Qp).half) x := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (p, k) (1 : Qp).half (1 : Qp).half x
  rw [Qp.half_add_half] at h
  exact h

/-- The state's bytes the invariant holds: the frozen ones discarded, the others but those a write
in flight took at a half. -/
def invBytes (p : GoString) (s : CSt) : IProp GF :=
  cBytes (L := L) p s.frac (fun k => !s.taken k) 0 s.bs

/-- The state's bytes the caller holds: a half of each but the frozen ones and those a write in
flight took. -/
def thrBytes (p : GoString) (s : CSt) : IProp GF :=
  cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half) (fun k => !s.taken k && !s.frozen k) 0 s.bs

theorem invBytes_runs (p : GoString) (s : CSt) :
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
def metaRes (p : GoString) (s : CSt) : IProp GF :=
  match s.busy with
  | .idle => osMeta (L := L) p (DFrac.own (1 : Qp).half) (some s.m)
  | .write t off data => pwTok (L := L) t p off data 1 s.m (cfRange s.m s.bs off data.length)
  | .trunc t sz => ftTok (L := L) t p sz s.m

/-- What the invariant holds of a state. -/
def invResS (p : GoString) : CState → IProp GF
  | none => osMeta (L := L) p (DFrac.own (1 : Qp).half) none
  | some s => iprop(metaRes (L := L) p s ∗ invBytes (L := L) p s)

/-- What the caller holds of a state: the other half of the `OsMeta`, while no change is in
flight, and its half of the bytes. -/
def thrResS (p : GoString) : CState → IProp GF
  | none => osMeta (L := L) p (DFrac.own (1 : Qp).half) none
  | some s => iprop((match s.busy with
      | .idle => osMeta (L := L) p (DFrac.own (1 : Qp).half) (some s.m)
      | _ => emp) ∗ thrBytes (L := L) p s)

instance invResS_timeless (p : GoString) (s : CState) : Timeless (invResS (L := L) p s) := by
  rcases s with _ | s
  · unfold invResS osMeta; infer_instance
  · rcases s with ⟨m, bs, fa, fb, _ | ⟨t, off, data⟩ | ⟨t, sz⟩⟩ <;>
      unfold invResS invBytes metaRes <;> dsimp only
    · unfold osMeta; infer_instance
    · unfold pwTok osTok; infer_instance
    · unfold ftTok osTok; infer_instance

/-- The crash invariant of the file at `p`: its state `s` (named by `γ`), the invariant's part of
it, and `Ok s`. -/
def csInv (N : Namespace) (p : GoString) (γ : GName) (Ok : CState → Prop) : IProp GF :=
  inv N iprop(∃ s : CState, ghostVar γ (1 : Qp).half s ∗ invResS (L := L) p s ∗ ⌜Ok s⌝)

instance csInv_persistent (N : Namespace) (p : GoString) (γ : GName) (Ok : CState → Prop) :
    Persistent (csInv (L := L) N p γ Ok) := by unfold csInv; infer_instance

/-- What the specs keep of a state. -/
def CsWf : CState → Prop
  | none => True
  | some s => s.Wf

/-- The caller's part of the file at `p` in the state `s`. -/
def csOwn (p : GoString) (γ : GName) (s : CState) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half s ∗ thrResS (L := L) p s ∗ ⌜CsWf s⌝)

/-- The state a generation starts with: the file as `osFileStart` gives it, nothing frozen. -/
def csStart : Option OsFile → CState
  | none => none
  | some f => some ⟨initMeta f, f.cur.map (·, true), 0, 0, .idle⟩

theorem csStart_wf (fo : Option OsFile) : CsWf (csStart fo) := by
  rcases fo with _ | f
  · trivial
  · exact ⟨by simp [initMeta], Nat.le_refl _, Nat.zero_le _, trivial⟩

/-- An idle state's bytes, invariant's and caller's together, nothing frozen: the whole run. -/
theorem idleBytes_whole (p : GoString) (s : CSt) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) :
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

theorem csStart_res (p : GoString) (fo : Option OsFile) :
    osFileStart (L := L) p fo ⊣⊢ invResS (L := L) p (csStart fo) ∗ thrResS (L := L) p (csStart fo) := by
  rcases fo with _ | f
  · exact osMeta_halves p none
  · dsimp only [osFileStart, csStart, invResS, thrResS, metaRes]
    refine (sep_congr (osMeta_halves p _) (idleBytes_whole p ⟨initMeta f, f.cur.map (·, true), 0, 0, .idle⟩ rfl (Nat.le_refl 0))).trans ?_
    exact ⟨by iintro ⟨⟨H1, H2⟩, H3, H4⟩; iframe, by iintro ⟨⟨H1, H3⟩, H2, H4⟩; iframe⟩

/-- A file a generation starts with, in an invariant, if `Ok` of its start state. -/
theorem csInv_alloc (N : Namespace) (p : GoString) (Ok : CState → Prop) (fo : Option OsFile)
    (hok : Ok (csStart fo)) :
    ⊢ osFileStart (L := L) p fo ={⊤}=∗ ∃ γ, csInv (L := L) N p γ Ok ∗ csOwn (L := L) p γ (csStart fo) := by
  iintro Hf
  imod ghostVar_alloc (GF := GF) (csStart fo) with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (A := CState) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (csStart_res p fo).1 $$ Hf with ⟨Hi, Ht⟩
  imod inv_alloc N ⊤ (iprop(∃ s : CState, ghostVar γ (1 : Qp).half s ∗ invResS (L := L) p s ∗
      ⌜Ok s⌝)) $$ [Hv1 Hi] with #Hinv
  · inext; iexists (csStart fo); iframe; ipureintro; exact hok
  imodintro
  iexists γ
  unfold csInv csOwn
  iframe Hinv Hv2 Ht
  ipureintro; exact csStart_wf fo

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The file after a crash under the premise `Q`**, from the invariant's part of the old
generation's state `s`: the new generation's file, `Good` if `CrashOkS` of `s`; the invariant's
part comes back, so that the invariant can be closed again. -/
theorem csInv_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List GoString) (p : GoString) (hp : p ∉ D) (Good : Option OsFile → Prop) (s : CState)
    (hok : CrashOkS Q p Good s) :
    ⊢ crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D -∗ invResS (L := L) p s -∗
      ∃ fo, ⌜Good fo⌝ ∗ osFileStart (L := L') p fo ∗
        crashRestQT Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (p :: D) ∗
        invResS (L := L) p s := by
  iintro Hr Hs
  rcases s with _ | s
  · dsimp only [invResS]
    icases osCrashQT_take_runs_keep Q L L' D p hp _ none [] $$ Hr Hs []
      with ⟨%fo, %h, Hf, Hr, Hs, -⟩
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iexists fo; iframe; ipureintro; exact hok fo h.1 h.2
  dsimp only [invResS]
  icases Hs with ⟨Hm, Hb⟩
  icases (invBytes_runs (L := L) p s).1 $$ Hb with Hb
  rcases hbz : s.busy with _ | ⟨t, off, data⟩ | ⟨t, sz⟩
  · have hm : s.vmeta = s.m := by simp [CSt.vmeta, hbz]
    have ht : s.toks p = [] := by simp [CSt.toks, hbz]
    ihave Hm := (show metaRes (L := L) p s ⊢ osMeta (L := L) p (DFrac.own (1 : Qp).half) (some s.m) by
      unfold metaRes; rw [hbz]) $$ Hm
    icases osCrashQT_take_runs_keep Q L L' D p hp _ (some s.m) s.runs $$ Hr Hm Hb
      with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
    iexists fo; iframe Hf Hr
    isplitr
    · ipureintro; have hk := hok fo; simp only [sMeta, sRuns, sToks, hm, ht] at hk; exact hk h.1 h.2
    isplitl [Hm]
    · unfold metaRes; rw [hbz]; iexact Hm
    iapply (invBytes_runs (L := L) p s).2; iexact Hb
  · ihave Ht := (show metaRes (L := L) p s ⊢ osTok (L := L) t ⟨⟨p, .write off data⟩, 1,
        (cfRange s.m s.bs off data.length).map Prod.fst, pwMeta s.m off data.length⟩ by
      unfold metaRes pwTok; rw [hbz]) $$ Hm
    icases osCrashQT_take_tok_keep Q L L' D t _ hp s.runs $$ Hr Ht Hb
      with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
    iexists fo; iframe Hf Hr
    isplitr
    · ipureintro
      have hk := hok fo; simp only [sMeta, sRuns, sToks, CSt.vmeta, CSt.toks, hbz] at hk
      exact hk h.1 h.2
    isplitl [Ht]
    · unfold metaRes pwTok; rw [hbz]; iexact Ht
    iapply (invBytes_runs (L := L) p s).2; iexact Hb
  · ihave Ht := (show metaRes (L := L) p s ⊢ osTok (L := L) t ⟨⟨p, .truncate sz⟩, 1, [],
        ftMeta s.m sz⟩ by
      unfold metaRes ftTok; rw [hbz]) $$ Hm
    icases osCrashQT_take_tok_keep Q L L' D t _ hp s.runs $$ Hr Ht Hb
      with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
    iexists fo; iframe Hf Hr
    isplitr
    · ipureintro
      have hk := hok fo; simp only [sMeta, sRuns, sToks, CSt.vmeta, CSt.toks, hbz] at hk
      exact hk h.1 h.2
    isplitl [Ht]
    · unfold metaRes ftTok; rw [hbz]; iexact Ht
    iapply (invBytes_runs (L := L) p s).2; iexact Hb

end crash

end Perennial
