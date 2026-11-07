/-
Crash-aware specs of `os` (this repository's, project `bboltfs`): the shared definitions.

A crash proof takes the old generation's files and tree after a crash from what an invariant holds
(`GooseLang/Ext/Fs/CrashTok.lean`'s `osCrash_take_runs_keep`, `osTreeCrash_take`), so a file's
ghost resources (`osMeta`, `osBytes`) and the tree's history must be in an invariant at every step,
including the steps inside an `os` call. The crash-aware specs (`Spec/os/Crash.lean`) keep the file
at the path `p` and half of the tree's history in an invariant `cfInv N p R γ Good` and open it
around each of the extension's steps:

* The file's state is `CFile`: no file at `p` (`none`), idle (`some (i, m, bs, none)`: its inode,
  `OsMeta` `m` and all its bytes `bs`), or with a `pwrite` in flight (`some (i, m, bs, some (t, off,
  data))`: the token `t` holds `m` and the bytes it changes).
* The invariant holds a ghost variable `γ` naming the state, half of the file's resources (all of
  what a change in flight holds, its token), half of the history `V`, and `CrashOk Good p R s V`:
  every crash of the history leaves `p` naming nothing (then `Good none`) or the state's file
  (`TreeOk`), and every file a crash may leave of the state is `Good` (`FileOk`). The caller holds
  the other halves (`cfOwn`), so it knows the state and the history exactly.
* A crash-aware spec moves the state; the caller shows `FileOk Good` of the states the call passes
  through (the tree's part is the spec's: only a create changes the history).
* After a crash, `cfInv_crash_keep` takes the tree and the file from the invariant's halves: the new
  generation's history, whole, and the file at `p` in it, `Good`.

`Good` is a predicate of what a crash leaves at `p`, so the specs are the same for any crash
invariant of a single file; mappings are not covered (`CfWf` asks for none).
-/
module

public import Proof.os.Base
public import GooseLang.Ext.Fs.CrashKept
public import GooseLang.Ext.Fs.TreeSpecsOpen

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-! ## The extension's operations are atomic -/

section atomic
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]

/-- Every step of an operation of the extension ends in a value. -/
theorem fsStep_val {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} {st' : OsState}
    (hs : FsStep o v h st () e' h' st' ()) : (toVal e').isSome := by
  obtain ⟨hs, -, -⟩ := hs
  unfold IsFsStep at hs
  split at hs
  · obtain ⟨_, _, _, _, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, _, _, -, -, -, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, -, -, -, -, hs⟩ := hs
    rcases hs with rfl | ⟨_, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, _, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, -, -, -, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  -- the tree's operations
  · obtain ⟨_, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, -, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨_, -, -, rfl⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, -, -, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, _, -, ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩⟩ | ⟨-, -, -, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, _, _, -, -, ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, _, _, -, -, ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨_, _, -, -, ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, -, -, -, hs⟩ := hs
    rcases hs with ⟨-, rfl⟩ | ⟨_, -, rfl, -⟩ <;> rfl
  · obtain ⟨_, _, _, _, _, -, -, -, -, -, -, rfl⟩ := hs; rfl
  · obtain ⟨_, _, _, _, -, -, -, rfl⟩ := hs; rfl
  · exact hs.elim

/-- An operation of the extension is atomic: it takes one step, to a value. -/
instance fsOp_atomic (a : Language.Atomicity) (o : String) (v : val) :
    Language.Atomic a (ExternalOp fsExt.name o (Val v)) :=
  goose_atomic a (fun _ _ e' _ _ hb => by
      cases hb with
      | ExternalOpS _ _ _ _ _ _ hst =>
        obtain ⟨_, _, _, hst', rfl⟩ := (extStep_named _ _ _ _ _).1 hst
        exact fsStep_val ((HasExt.step_iff ..).1 hst'))
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

end atomic

/-! ## The file's state and what a crash leaves of it -/

/-- A file as the crash-aware specs track it: none at the path (`none`); its inode, `OsMeta` and
all its bytes (`some (i, m, bs, none)`); or with a `pwrite` of `data` at `off` in flight, whose
token `t` holds `m` and the bytes it changes (`some (i, m, bs, some (t, off, data))`, `bs` the
bytes before it). -/
abbrev CFile := Option (Ino × OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8))

/-- The inode of the state's file. -/
def cIno : CFile → Option Ino
  | none => none
  | some (i, _) => some i

/-- The first byte a write at `off` takes of a file of size `m.size`. -/
def cfLo (m : OsMeta) (off : Nat) : Nat := min off m.size

/-- The end of the bytes a write of `n` bytes at `off` takes of a file of size `m.size`. -/
def cfHi (m : OsMeta) (off n : Nat) : Nat := min (off + n) m.size

/-- The bytes such a write takes. -/
def cfRange (m : OsMeta) (bs : List (w8 × Bool)) (off n : Nat) : List (w8 × Bool) :=
  (bs.drop (cfLo m off)).take (cfHi m off n - cfLo m off)

/-- What the old generation knows of an existing file for a crash, without its inode: its
`OsMeta` (the token's, with the size bound of the write, while a write is in flight)... -/
def fMeta : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) → OsMeta
  | (m, _, none) => m
  | (m, _, some (_, off, data)) => pwMeta m off data.length

/-- ... and the runs of bytes it holds. -/
def fRuns : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) →
    List (Nat × DFrac × List (w8 × Bool))
  | (_, bs, none) => [(0, DFrac.own (1 : Qp).half, bs)]
  | (m, bs, some (_, off, data)) =>
      [(0, DFrac.own (1 : Qp).half, bs.take (cfLo m off)),
       (cfHi m off data.length, DFrac.own (1 : Qp).half, bs.drop (cfHi m off data.length))]

/-- What a crash leaves past the old size of an existing file `x`: clean bytes, or, with a write in
flight, the bytes it writes there. -/
def TailOk : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) → OsFile → Prop
  | (m, _, none), f => ∀ b, m.size ≤ b → b < f.size → CleanPhys f b
  | (m, _, some (_, off, data)), f => ∀ b, m.size ≤ b → b < f.size → CleanPhys f b ∨
      (off ≤ b ∧ b < off + data.length ∧ f.contents[b]? = data[b - off]?)

/-- What a crash leaves of the bytes under a write in flight (`x`'s bytes `cfRange` from `off`):
each the write's byte, or its old byte (clean if it was), or a clean byte (a machine crash puts it
on disk). -/
def TokOk : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) → OsFile → Prop
  | (_, _, none), _ => True
  | (m, bs, some (_, off, data)), f => ∀ j x, (cfRange m bs off data.length)[j]? = some x →
      off + j < f.size →
      f.contents[off + j]? = data[j]? ∨
      (f.contents[off + j]? = some x.1 ∧ (x.2 = true → CleanPhys f (off + j))) ∨
      CleanPhys f (off + j)

/-- Every file a crash may leave of an existing file `x` is `Good`: its clean bytes kept
(`FileCrashedR`), every byte of its runs clean (`RunsKept`: a crashed file is on disk), and past
the old size clean bytes or a write's data (`TailOk`), and under a write in flight its byte or the
old one or a clean one (`TokOk`). Not of its inode. -/
def FileOk (Good : Option OsFile → Prop) (x : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8)) :
    Prop :=
  ∀ f, FileCrashedR (fMeta x) (fRuns x) (some f) → RunsKept (fRuns x) (some f) → TailOk x f →
    TokOk x f → Good (some f)

/-- Every crash of the history `V` leaves `p` naming nothing (and then `Good none`) or the file
`io`, if any. -/
def TreeOkI (Good : Option OsFile → Prop) (p : GoString) (R : Roots) (io : Option Ino) (V : Hist) :
    Prop :=
  ∀ V', TreeCrashed V V' →
    (lookupH R V' p = none ∧ Good none) ∨ ∃ i, io = some i ∧ lookupH R V' p = some (.file i)

/-- Every crash of the history `V` leaves `p` naming nothing (and then `Good none`) or the state's
file. -/
abbrev TreeOk (Good : Option OsFile → Prop) (p : GoString) (R : Roots) (s : CFile) (V : Hist) :
    Prop :=
  TreeOkI Good p R (cIno s) V

/-- What a crash may leave of the state `s` and the history `V` is `Good` at `p`. -/
def CrashOk (Good : Option OsFile → Prop) (p : GoString) (R : Roots) (s : CFile) (V : Hist) :
    Prop :=
  TreeOk Good p R s V ∧ ∀ i x, s = some (i, x) → FileOk Good x

/-- The state of a write of `data` at `off` in flight, from the file `m`, `bs` (the token's number
does not matter to a crash). -/
abbrev cfWriting (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8) :
    OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8) :=
  (m, bs, some (0, off, data))

/-- What the specs keep of a state: all of the file's bytes, and no mapping. -/
def CfWf : CFile → Prop
  | none => True
  | some (_, m, bs, _) => bs.length = m.size ∧ m.maps = ∅

/-- What `p` names now: nothing, or the state's file. -/
def PathOk (p : GoString) (R : Roots) (s : CFile) (V : Hist) : Prop :=
  match s with
  | none => lookupH R V p = none
  | some (i, _) => lookupH R V p = some (.file i)

/-- A crash view is narrower than another: a crash may leave fewer files of it. -/
theorem fileCrashedR_mono {m0 m1 : OsMeta} {rs0 rs1 : List (Nat × DFrac × List (w8 × Bool))}
    {fo : Option OsFile} (hlo : m0.lo ≤ m1.lo) (hhi : m1.hi ≤ m0.hi)
    (hcov : ∀ r ∈ rs0, ∀ k x, r.2.2[k]? = some x → x.2 = true →
      ∃ r' ∈ rs1, ∃ k', r'.2.2[k']? = some x ∧ r'.1 + k' = r.1 + k)
    (h : FileCrashedR m1 rs1 fo) : FileCrashedR m0 rs0 fo := by
  intro f hf
  obtain ⟨h1, h2, h3⟩ := h f hf
  refine ⟨by omega, by omega, fun r hr k x hk hc => ?_⟩
  obtain ⟨r', hr', k', hk', he⟩ := hcov r hr k x hk hc
  rw [← he]; exact h3 r' hr' k' x hk' hc

/-- What `p` names depends on the tree now only. -/
theorem lookupH_congr {R : Roots} {V W : Hist} (p : GoString) (h : V.now = W.now) :
    lookupH R V p = lookupH R W p := by
  have ht : (Hist.st R V).tree = (Hist.st R W).tree := h
  unfold lookupH OsState.lookup
  rw [ht]
  rfl

/-- A crash of a history with one more entry: a crash of the old one, or the new tree. -/
theorem treeCrashed_push {V V' : Hist} {e : LogEntry} (h : TreeCrashed (V.push e) V') :
    TreeCrashed V V' ∨ V'.now = (V.push e).now := by
  obtain ⟨n, hn, rfl⟩ := h
  by_cases hn' : n ≤ V.2.length
  · left
    refine ⟨n, hn', ?_⟩
    show (replay (((V.2 ++ [e]).take n).map (·.op)) V.1, ([] : List LogEntry)) = _
    rw [List.take_append_of_le_length hn']
  · right
    have : n = V.2.length + 1 := by simp [Hist.push] at hn; omega
    subst this
    show replay [] (replay (((V.2 ++ [e]).take (V.2.length + 1)).map (·.op)) V.1) =
      replay ((V.2 ++ [e]).map (·.op)) V.1
    rw [List.take_of_length_le (by simp)]
    rfl

/-- A crash may keep the tree now: `PathOk`'s `p`. -/
theorem treeCrashed_refl (V : Hist) : TreeCrashed V (V.now, []) := treeCrashed_self V

/-! ## The invariant -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- What the invariant holds of the state: half of the `OsMeta` and of the bytes, or, while a
write is in flight, its token and half of the bytes around it. -/
def invRes : CFile → IProp GF
  | none => iprop(emp)
  | some (i, m, bs, none) => iprop(osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) bs)
  | some (i, m, bs, some (t, off, data)) => iprop(
      pwTok (L := L) t i off data 1 m (cfRange m bs off data.length) ∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) i (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)))

/-- What the caller holds of the state: the other halves. -/
def thrRes : CFile → IProp GF
  | none => iprop(emp)
  | some (i, m, bs, none) => iprop(osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) bs)
  | some (i, m, bs, some (_, off, data)) => iprop(
      osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) i (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)))

/-- The invariant of the file at `p` (the roots `R`): its state `s` (named by `γ`), the
invariant's half of it and of the history `V`, and what a crash may leave of them is `Good`. -/
def cfInv (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop) :
    IProp GF :=
  inv N iprop(∃ (s : CFile) (V : Hist), ghostVar γ (1 : Qp).half s ∗ invRes (L := L) s ∗
    osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜CrashOk Good p R s V⌝)

instance cfInv_persistent (N : Namespace) (p : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) : Persistent (cfInv (L := L) N p R γ Good) := by
  unfold cfInv; infer_instance

/-- The caller's part of the file at `p` in the state `s`, the history being `V`. -/
def cfOwn (p : GoString) (R : Roots) (γ : GName) (s : CFile) (V : Hist) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half s ∗ thrRes (L := L) s ∗
    osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜CfWf s ∧ PathOk p R s V⌝)

theorem osMeta_halves (i : Ino) (m : OsMeta) :
    osMeta (L := L) i (DFrac.own 1) m ⊣⊢
      osMeta (L := L) i (DFrac.own (1 : Qp).half) m ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) m := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm i (1 : Qp).half (1 : Qp).half m
  rw [Qp.half_add_half] at h
  exact h

theorem osBytes_halves (i : Ino) (off : Nat) (xs : List (w8 × Bool)) :
    osBytes (L := L) i off (DFrac.own 1) xs ⊣⊢
      osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (L := L) i off (DFrac.own (1 : Qp).half) xs := by
  unfold osBytes bytesG
  refine BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  constructor
  · apply BigSepL.bigSepL_mono_of_forall; intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.1
  · apply BigSepL.bigSepL_mono_of_forall; intro k x
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off + k)
      (1 : Qp).half (1 : Qp).half x
    rw [Qp.half_add_half] at h
    exact h.2

theorem osTree_halves (R : Roots) (V : Hist) :
    osTree (L := L) (DFrac.own 1) R V ⊣⊢
      osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () (1 : Qp).half (1 : Qp).half
    (R, V)
  rw [Qp.half_add_half] at h
  exact h

theorem osTree_agree (dq1 dq2 : DFrac) (R R' : Roots) (V V' : Hist) :
    ⊢ osTree (L := L) dq1 R V -∗ osTree (L := L) dq2 R' V' -∗ ⌜R = R' ∧ V = V'⌝ := by
  unfold osTree; iintro A B
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ A B with %hv
  ipureintro
  obtain ⟨-, h⟩ := hv
  cases h; exact ⟨rfl, rfl⟩

/-- The file at `p` as a generation starts with it, as a state: none, or the start's file. -/
def startState (i : Ino) (f : OsFile) : CFile := some (i, metaOf f, bytesOf f, none)

theorem startState_wf (i : Ino) (f : OsFile) (hm : (metaOf f).maps = ∅) :
    CfWf (startState i f) :=
  ⟨by simp [startState, bytesOf_length, metaOf], hm⟩

/-- What the generation's start gives of the state `s`: nothing, or its file whole. -/
def startRes : CFile → IProp GF
  | none => iprop(emp)
  | some (i, m, bs, _) => iprop(osMeta (L := L) i (DFrac.own 1) m ∗ osBytes (L := L) i 0 (DFrac.own 1) bs)

/-- **The file at `p` and the history, in an invariant**, if a crash of them is `Good`. -/
theorem cfInv_alloc (N : Namespace) (p : GoString) (R : Roots) (V : Hist)
    (Good : Option OsFile → Prop) (s : CFile) (hs : ∀ i m bs x, s ≠ some (i, m, bs, some x))
    (hok : CrashOk Good p R s V) (hwf : CfWf s) (hp : PathOk p R s V) :
    ⊢ osTree (L := L) (DFrac.own 1) R V -∗ startRes (L := L) s ={⊤}=∗ ∃ γ,
      cfInv (L := L) N p R γ Good ∗ cfOwn (L := L) p R γ s V := by
  iintro Ht Hf
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (A := CFile) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (osTree_halves R V).1 $$ Ht with ⟨Ht1, Ht2⟩
  ihave ⟨Hi, Hth⟩ := (show startRes (L := L) s ⊢ invRes (L := L) s ∗ thrRes (L := L) s by
    rcases s with _ | ⟨i, m, bs, _ | x⟩
    · iintro -; isplitl [] <;> iempintro
    · dsimp only [startRes, invRes, thrRes]
      iintro ⟨Hm, Hb⟩
      icases (osMeta_halves i m).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves i 0 bs).1 $$ Hb with ⟨Hb1, Hb2⟩
      iframe
    · exact absurd rfl (hs i m bs x)) $$ Hf
  imod inv_alloc N ⊤ (iprop(∃ (s : CFile) (V : Hist), ghostVar γ (1 : Qp).half s ∗
      invRes (L := L) s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗
      ⌜CrashOk Good p R s V⌝)) $$ [Hv1 Hi Ht1] with #Hinv
  · inext; iexists s, V; iframe; ipureintro; exact hok
  imodintro
  iexists γ
  unfold cfInv cfOwn
  iframe Hinv Hv2 Hth Ht2
  ipureintro; exact ⟨hwf, hp⟩

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The new generation's file at `p`, in the history `V'`: none, or the file of the inode `p`
names, whole, as the crash left it: on disk, all of it clean (`osFileStart`); never a directory. -/
def startAt (L' : GooseLocalGS GF) (p : GoString) (R : Roots) (V' : Hist) (fo : Option OsFile) :
    IProp GF :=
  match lookupH R V' p with
  | some (.file i) => iprop(∃ f, ⌜fo = some f⌝ ∗ osFileStart (L := L') i f)
  | none => iprop(⌜fo = none⌝)
  | some (.dir _) => iprop(False)

/-- What a crash of the old generation's state `s` leaves: the file's crash, through the runs, if
there is a file. -/
def CrashFileR : CFile → Option OsFile → Prop
  | none, _ => True
  | some (_, x), fo => FileCrashedR (fMeta x) (fRuns x) fo

/-- **The tree and the file after a crash**, from the invariant's halves of the old generation's
state `s` and history `V`: the new generation's history, whole, and the file at `p` in it, `Good`;
the old halves come back, so that the invariant can be closed again. -/
theorem cfInv_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (p : GoString) (R : Roots) (Good : Option OsFile → Prop) (s : CFile) (V : Hist)
    (hD : ∀ i, cIno s = some i → i ∉ D) (hok : CrashOk Good p R s V) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' -∗ invRes (L := L) s -∗
      osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗
      ∃ fo, ⌜TreeCrashed V V' ∧ Good fo⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗
        startAt L' p R V' fo ∗
        (∃ D', crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D' true V') ∗
        invRes (L := L) s ∗ osTree (L := L) (DFrac.own (1 : Qp).half) R V := by
  iintro Hr Hs Ht
  icases osTreeCrash_take Q L L' D V' _ R V $$ Hr Ht with ⟨%htc, Ht', Hr, Ht⟩
  have hto := hok.1 V' htc
  rcases s with _ | ⟨i, m, bs, _ | ⟨t, off, data⟩⟩
  · -- no file at `p`: `p` names nothing after the crash
    rcases hto with ⟨hn, hg⟩ | ⟨i, hi, -⟩
    · iexists none
      iframe Ht' Hs Ht
      isplitr
      · ipureintro; exact ⟨htc, hg⟩
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      iexists D; iexact Hr
    · cases hi
  · -- idle
    dsimp only [invRes]
    icases Hs with ⟨Hm, Hb⟩
    icases osCrash_take_runs_keep Q L L' D true V' i (hD i rfl) _ m [(0, DFrac.own (1 : Qp).half, bs)]
      $$ Hr Hm [Hb] with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    obtain ⟨hfc, hnm, hseen⟩ := hfo
    have hrk : RunsKept [(0, DFrac.own (1 : Qp).half, bs)] fo :=
      crashSeen_runsKept hseen (fun x hx => by cases hx)
    have htk := crashSeen_tailKept hseen (fun x hx => by cases hx)
    rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
    · iexists none
      iframe Ht' Hm Hb Ht
      isplitr
      · ipureintro; exact ⟨htc, hg⟩
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      iexists (i :: D); iexact Hr
    · cases hi
      obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm (named_of_lookup hl))
      iexists (some f)
      iframe Ht' Hm Hb Ht
      isplitr
      · ipureintro
        exact ⟨htc, hok.2 i _ rfl f hfc hrk (fun b h1 h2 => htk f rfl b h1 h2) trivial⟩
      isplitl [Hf]
      · unfold startAt; rw [hl]; iexists f; isplitr
        · ipureintro; rfl
        obtain ⟨vs, sz, rfl⟩ := crashSeen_ofDisk hseen
        iapply (osFileStartG_ofDisk (L := L') _ vs sz).1
        iapply (show osFileStartO (L := L') _ (some (OsFile.ofDisk vs sz)) ⊢
            osFileStartG (L := L') _ (OsFile.ofDisk vs sz) from BIBase.Entails.rfl) $$ Hf
      iexists (i :: D); iexact Hr
  · -- a write in flight
    dsimp only [invRes]
    icases Hs with ⟨Ht0, Hb1, Hb2⟩
    dsimp only [pwTok]
    icases Ht0 with ⟨Ht0, %hgap⟩
    icases osCrash_take_tok_keep Q L L' D true V' t _ (hD i rfl)
      (fRuns (m, bs, some (t, off, data))) $$ Hr Ht0 [Hb1 Hb2] with ⟨%fo, %hfo, Hf, Hr, Ht0, Hbs⟩
    · unfold fRuns
      iapply BigSepL.bigSepL_cons.2; iframe Hb1
      iapply BigSepL.bigSepL_singleton.2; iexact Hb2
    unfold fRuns
    icases BigSepL.bigSepL_cons.1 $$ Hbs with ⟨Hb1, Hbs⟩
    icases BigSepL.bigSepL_singleton.1 $$ Hbs with Hb2
    obtain ⟨hfc, hnm, hseen⟩ := hfo
    have hrk : RunsKept (fRuns (m, bs, some (t, off, data))) fo := by
      refine crashSeen_runsKept hseen (fun x hx => ⟨off, data, ?_, fun r hr k hk hkm => ?_⟩)
      · rw [List.mem_singleton] at hx; rw [hx]
      · simp only [fRuns, List.mem_cons, List.not_mem_nil, or_false] at hr
        have hsz : (pwMeta m off data.length).size = m.size := rfl
        rw [hsz] at hkm
        rcases hr with rfl | rfl
        · left; simp only [List.length_take] at hk; unfold cfLo at hk; dsimp only; omega
        · right; dsimp only; unfold cfHi at hkm ⊢; omega
    have htk := crashSeen_tailKept hseen (fun x hx => ⟨off, data, by
      rw [List.mem_singleton] at hx; rw [hx], hgap⟩)
    rcases hto with ⟨hn, hg⟩ | ⟨i', hi, hl⟩
    · iexists none
      iframe Ht' Ht
      isplitr
      · ipureintro; exact ⟨htc, hg⟩
      isplitr
      · unfold startAt; rw [hn]; ipureintro; rfl
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap
    · cases hi
      obtain ⟨f, rfl⟩ := Option.isSome_iff_exists.1 (hnm (named_of_lookup hl))
      iexists (some f)
      iframe Ht' Ht
      isplitr
      · ipureintro
        refine ⟨htc, hok.2 i _ rfl f hfc hrk (fun b h1 h2 => ?_) (fun j x hx hj => ?_)⟩
        rotate_left
        · exact .inr (.inr (crashSeen_tokKept hseen List.mem_cons_self rfl rfl hgap f rfl j x.1
            (by simp [List.getElem?_map, hx]) hj))
        exact .inl (htk f rfl b h1 h2)
      isplitl [Hf]
      · unfold startAt; rw [hl]; iexists f; isplitr
        · ipureintro; rfl
        obtain ⟨vs, sz, rfl⟩ := crashSeen_ofDisk hseen
        iapply (osFileStartG_ofDisk (L := L') _ vs sz).1
        iapply (show osFileStartO (L := L') _ (some (OsFile.ofDisk vs sz)) ⊢
            osFileStartG (L := L') _ (OsFile.ofDisk vs sz) from BIBase.Entails.rfl) $$ Hf
      isplitl [Hr]
      · iexists _; iexact Hr
      iframe; ipureintro; exact hgap

end crash

end Perennial
