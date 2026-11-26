/-
The database's file as bbolt's invariants hold it (W1 of `plans/bbolt-crash-plan.md` §7; Lean-first,
no Rocq counterpart).

`BFile` is the file's record: its path, its inode, and its **crash names** `cs`: `none` while the
file is outside a crash invariant (bbolt holds every byte whole, as before W1), `some c` once
`Open` put it in the inode-keyed crash invariant `csInvI c.N p.ino c.g c.ga c.gc bCsOk`
(`Proof/os/CrashStI.lean`), which holds half of the file's `OsMeta` and of each byte.

bbolt's invariants hold the file through two resources whose laws do not depend on `cs`:
* `bBytes p off dq xs`: the bytes from `off` at `dq` of bbolt's share, that is `osBytes` at `dq`
  (`cs = none`) or at half of `dq` (`cs = some _`: bbolt's share is the caller's half of the
  crash invariant). `bBytes p off (own 1) xs` is all of bbolt's share of the range;
* `bMeta p C L m`: the writer's whole share of the `OsMeta`: `osMeta 1` (`cs = none`), or half of
  the `OsMeta` and the caller's token of the invariant's state (whose bytes are
  `m`'s file's, all of them; the client value `a` idle at the committed state `C`).

`bCsOk a s := FsNoErr → BDur a s` is the invariant's obligation (`Crash/Dur.lean`): every state of the
file the invariant holds is durable for the abstract state `a` if the file system does not fail.
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Dur
public import Proof.os.CrashStI
public import GooseLang.Ext.Fs.FsNoErr
public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI

/-! ## The crash invariant's value -/

instance BPhase.countable : Pos.Countable BPhase :=
  countableOfLeftInverse
    (fun p => match p with | .idle => (0 : Nat) | .committing => 1 | .init => 2)
    (fun n => if n = 0 then .idle else if n = 1 then .committing else .init)
    (fun p => by cases p <;> rfl)

instance BAbs.countable : Pos.Countable BAbs :=
  countableOfLeftInverse (fun a : BAbs => (a.cur, a.prev, a.xcur, a.xprev, a.phase))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

/-- **The crash invariant's obligation** on bbolt's file: durable for the abstract state `a` unless
the file system fails. -/
def bCsOk [GooseExts] [ExtSemantics fsExt] (a : BAbs) (s : CSt) : Prop := FsNoErr → BDur a s

/-! ## The file's record -/

/-- The names of a file's crash invariant: its state (`g`), its value (`ga`), its closing token
(`gc`, bbolt's `B.bq`), its namespace (`N`, `crashN γ.ns`), and the bytes' exclusivity tokens
(`ex`: `ghostMap Nat Unit`, a fragment per byte of the file, at bbolt's fraction of it; the
authority in `bMeta`, for the bytes a truncate adds). -/
structure CsN where
  g : GName
  ga : GName
  gc : GName
  N : Namespace
  ex : GName
  deriving Inhabited, DecidableEq

/-- **The database's file** (the port onto the per-byte extension, 2026-11-12): its path (`db.path`,
the `*os.File`'s name, `fileOwn`), its inode (every file resource: `osMeta`, `osBytes`, `osFd`) and its
crash names (W1: `none` outside a crash invariant). One record, so that the invariants keep one file
parameter. -/
structure BFile where
  path : GoString
  ino : Ino
  cs : Option CsN := none
deriving Inhabited

/-- Half of a fraction. -/
def dhalf : DFrac → DFrac
  | .own q => .own q.half
  | .discard => .discard
  | .ownDiscard q => .ownDiscard q.half

/-- The fraction of `osBytes` that bbolt's share `dq` of the file `p`'s bytes is. -/
def BFile.dq (p : BFile) (dq : DFrac) : DFrac :=
  match p.cs with
  | none => dq
  | some _ => dhalf dq

theorem BFile.dq_none {p : BFile} (h : p.cs = none) (dq : DFrac) : p.dq dq = dq := by
  unfold BFile.dq; rw [h]

theorem BFile.dq_own_add (p : BFile) (q1 q2 : Qp) :
    p.dq (DFrac.own (q1 + q2)) = DFrac.own ((match p.cs with | none => q1 | some _ => q1.half) +
      (match p.cs with | none => q2 | some _ => q2.half)) := by
  unfold BFile.dq
  cases p.cs with
  | none => rfl
  | some _ =>
    simp only [dhalf]; congr 1; apply Subtype.ext
    simp only [Qp.val_half, Qp.val_add]; grind

theorem BFile.dq_own (p : BFile) (q : Qp) :
    p.dq (DFrac.own q) = DFrac.own (match p.cs with | none => q | some _ => q.half) := by
  unfold BFile.dq; cases p.cs <;> rfl

/-- The crash invariant's namespace, if any, is disjoint from OsFs's (`isBoltCoreP`'s
`↑N ## ↑osN`, `c.N = crashN N`). -/
def bNsOk (p : BFile) : Prop := ∀ c, p.cs = some c → ↑osN ⊆ (⊤ : CoPset) \ ↑c.N

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-! ## bbolt's share of the bytes -/

/-- The exclusivity tokens of `n` bytes of `p` from `off` at `dq` (none outside a crash
invariant, where the bytes are whole). -/
def bGhost (p : BFile) (off : Nat) (dq : DFrac) (n : Nat) : IProp GF :=
  match p.cs with
  | none => iprop(emp)
  | some c => iprop([∗list] k ∈ List.range' off n, ghostMapElem (K := Nat) (V := Unit) c.ex k dq ())

/-- **bbolt's share `dq` of the bytes of `p` from `off`** (see the file header): the extension's
bytes at `p.dq dq`, with their exclusivity tokens. -/
def bBytes (p : BFile) (off : Nat) (dq : DFrac) (xs : List ByteG) : IProp GF :=
  iprop(osBytes p.ino off (p.dq dq) xs ∗ bGhost p off dq xs.length)

/-- The share of one byte. -/
def bByte (p : BFile) (off : Nat) (dq : DFrac) (x : ByteG) : IProp GF :=
  iprop(osByte p.ino off (p.dq dq) x ∗ bGhost p off dq 1)

omit go_gctx in
instance bGhost_timeless (p : BFile) (off : Nat) (dq : DFrac) (n : Nat) :
    Timeless (bGhost (GF := GF) p off dq n) := by
  unfold bGhost; cases p.cs with
  | none => dsimp only; infer_instance
  | some c => dsimp only; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

omit go_gctx in
instance bBytes_timeless (p : BFile) (off : Nat) (dq : DFrac) (xs : List ByteG) :
    Timeless (bBytes (GF := GF) p off dq xs) := by
  have : Timeless (osBytes (GF := GF) p.ino off (p.dq dq) xs) := by
    unfold osBytes bytesG; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
  unfold bBytes; infer_instance

omit go_gctx in
instance bByte_timeless (p : BFile) (off : Nat) (dq : DFrac) (x : ByteG) :
    Timeless (bByte (GF := GF) p off dq x) := by
  have : Timeless (osByte (GF := GF) p.ino off (p.dq dq) x) := by unfold osByte; infer_instance
  unfold bByte; infer_instance

omit go_gctx in
theorem bGhost_none {p : BFile} (h : p.cs = none) (off : Nat) (dq : DFrac) (n : Nat) :
    bGhost (GF := GF) p off dq n = iprop(emp) := by
  unfold bGhost; rw [h]

omit go_gctx in
theorem bGhost_add (p : BFile) (off : Nat) (dq : DFrac) (n1 n2 : Nat) :
    bGhost (GF := GF) p off dq (n1 + n2) ⊣⊢ bGhost p off dq n1 ∗ bGhost p (off + n1) dq n2 := by
  unfold bGhost; cases p.cs with
  | none => exact emp_sep.symm
  | some c => dsimp only; rw [← List.range'_append_1]; exact BigSepL.bigSepL_append

omit go_gctx in
theorem bGhost_zero (p : BFile) (off : Nat) (dq : DFrac) :
    bGhost (GF := GF) p off dq 0 ⊣⊢ emp := by
  unfold bGhost; cases p.cs with
  | none => exact .rfl
  | some c => dsimp only; exact BigSepL.bigSepL_nil

omit go_gctx in
theorem bGhost_frac (p : BFile) (off : Nat) (q1 q2 : Qp) (n : Nat) :
    bGhost (GF := GF) p off (DFrac.own (q1 + q2)) n ⊣⊢
      bGhost p off (DFrac.own q1) n ∗ bGhost p off (DFrac.own q2) n := by
  unfold bGhost; cases p.cs with
  | none => exact emp_sep.symm
  | some c =>
    dsimp only
    refine BIBase.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
    exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ _} =>
        ((ghostMapElem_fractional (K := Nat) (V := Unit) _ c.ex ()).fractional q1 q2).1),
      BigSepL.bigSepL_mono_of_forall (fun {_ _} =>
        ((ghostMapElem_fractional (K := Nat) (V := Unit) _ c.ex ()).fractional q1 q2).2)⟩

omit go_gctx in
/-- **The extension's bytes of bbolt's share**, and back for any bytes of the same length (the
tokens are of positions only). -/
theorem bBytes_os (p : BFile) (off : Nat) (dq : DFrac) (xs : List ByteG) :
    bBytes (GF := GF) p off dq xs ⊣⊢ osBytes p.ino off (p.dq dq) xs ∗ bGhost p off dq xs.length :=
  .rfl

omit go_gctx in
theorem bBytes_none {p : BFile} (h : p.cs = none) (off : Nat) (dq : DFrac) (xs : List ByteG) :
    bBytes (GF := GF) p off dq xs ⊣⊢ osBytes p.ino off dq xs := by
  unfold bBytes; rw [BFile.dq_none h, bGhost_none h]; exact sep_emp

omit go_gctx in
theorem bByte_none {p : BFile} (h : p.cs = none) (off : Nat) (dq : DFrac) (x : ByteG) :
    bByte (GF := GF) p off dq x ⊣⊢ osByte p.ino off dq x := by
  unfold bByte; rw [BFile.dq_none h, bGhost_none h]; exact sep_emp

omit go_gctx in
theorem bBytes_nil (p : BFile) (off : Nat) (dq : DFrac) :
    bBytes (GF := GF) p off dq [] ⊣⊢ emp := by
  unfold bBytes osBytes
  refine (sep_congr (bytesG_nil _ _ _ _) (bGhost_zero p off dq)).trans emp_sep

omit go_gctx in
theorem bBytes_nil' (p : BFile) (off : Nat) (dq : DFrac) :
    ⊢ bBytes (GF := GF) p off dq [] := (bBytes_nil p off dq).2

omit go_gctx in
theorem bBytes_cons (p : BFile) (off : Nat) (dq : DFrac) (x : ByteG) (xs : List ByteG) :
    bBytes (GF := GF) p off dq (x :: xs) ⊣⊢ bByte p off dq x ∗ bBytes p (off + 1) dq xs := by
  unfold bBytes bByte osBytes osByte
  rw [List.length_cons, Nat.add_comm xs.length 1]
  refine (sep_congr (bytesG_cons _ _ _ _ _ _) (bGhost_add p off dq 1 xs.length)).trans ?_
  exact ⟨by iintro ⟨⟨H1, H2⟩, H3, H4⟩; iframe, by iintro ⟨⟨H1, H3⟩, H2, H4⟩; iframe⟩

omit go_gctx in
theorem bBytes_append (p : BFile) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    bBytes (GF := GF) p off dq (xs ++ ys) ⊣⊢
      bBytes p off dq xs ∗ bBytes p (off + xs.length) dq ys := by
  unfold bBytes osBytes
  rw [List.length_append]
  refine (sep_congr (bytesG_append _ _ _ _ _ _) (bGhost_add p off dq xs.length ys.length)).trans ?_
  exact ⟨by iintro ⟨⟨H1, H2⟩, H3, H4⟩; iframe, by iintro ⟨⟨H1, H3⟩, H2, H4⟩; iframe⟩

omit go_gctx in
theorem bBytes_take_drop (p : BFile) (lo : Nat) (dq : DFrac) (ys : List ByteG) (a : Nat)
    (ha : a ≤ ys.length) :
    bBytes (GF := GF) p lo dq ys ⊣⊢ bBytes p lo dq (ys.take a) ∗ bBytes p (lo + a) dq (ys.drop a) := by
  conv => lhs; rw [← List.take_append_drop a ys]
  refine (bBytes_append _ _ _ _ _).trans ?_
  rw [List.length_take, Nat.min_eq_left ha]
  exact .rfl

omit go_gctx in
/-- `osBytes_frac` (`GooseLang/Ext/Fs/Zeros.lean`) without its section's instances. -/
theorem osBytes_frac_b (i : Ino) (off : Nat) (q1 q2 : Qp) (xs : List ByteG) :
    osBytes (GF := GF) i off (DFrac.own (q1 + q2)) xs ⊣⊢
      osBytes i off (DFrac.own q1) xs ∗ osBytes i off (DFrac.own q2) xs := by
  unfold osBytes bytesG
  refine BIBase.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ _} => (gElem_split _ _ _ _ _ _).1),
    BigSepL.bigSepL_mono_of_forall (fun {_ _} => (gElem_split _ _ _ _ _ _).2)⟩

omit go_gctx in
/-- Fractions of bbolt's share. -/
theorem bBytes_frac (p : BFile) (off : Nat) (q1 q2 : Qp) (xs : List ByteG) :
    bBytes (GF := GF) p off (DFrac.own (q1 + q2)) xs ⊣⊢
      bBytes p off (DFrac.own q1) xs ∗ bBytes p off (DFrac.own q2) xs := by
  unfold bBytes
  have e := osBytes_frac_b (GF := GF) p.ino off
    (match p.cs with | none => q1 | some _ => q1.half)
    (match p.cs with | none => q2 | some _ => q2.half) xs
  rw [← BFile.dq_own, ← BFile.dq_own, ← BFile.dq_own_add] at e
  refine (sep_congr e (bGhost_frac p off q1 q2 xs.length)).trans ?_
  exact ⟨by iintro ⟨⟨H1, H2⟩, H3, H4⟩; iframe, by iintro ⟨⟨H1, H3⟩, H2, H4⟩; iframe⟩

omit go_gctx in
theorem bBytes_halves (p : BFile) (off : Nat) (xs : List ByteG) :
    bBytes (GF := GF) p off (DFrac.own 1) xs ⊣⊢
      bBytes p off (DFrac.own (1 : Qp).half) xs ∗ bBytes p off (DFrac.own (1 : Qp).half) xs := by
  have h := bBytes_frac (GF := GF) p off (1 : Qp).half (1 : Qp).half xs
  rw [Qp.half_add_half] at h
  exact h

omit go_gctx in
theorem bBytes_halves_q (p : BFile) (off : Nat) (q : Qp) (xs : List ByteG) :
    bBytes (GF := GF) p off (DFrac.own q) xs ⊣⊢
      bBytes p off (DFrac.own q.half) xs ∗ bBytes p off (DFrac.own q.half) xs := by
  have h := bBytes_frac (GF := GF) p off q.half q.half xs
  rw [Qp.half_add_half] at h
  exact h

omit go_gctx in
/-- **Two whole shares of a byte are not both held.** -/
theorem bByte_excl (p : BFile) (off : Nat) (x y : ByteG) :
    bByte (GF := GF) p off (DFrac.own 1) x ∗ bByte p off (DFrac.own 1) y ⊢ False := by
  unfold bByte
  cases h : p.cs with
  | none =>
    rw [BFile.dq_none h]
    iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
    unfold osByte
    icases gElem_valid_2 _ _ _ _ _ x y $$ H1 H2 with %Hv
    exact (dfrac_own_one_op_invalid _ Hv.1).elim
  | some c =>
    unfold bGhost; rw [h]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
    simp only [List.range'_one]
    icases BigSepL.bigSepL_singleton.1 $$ H1 with H1
    icases BigSepL.bigSepL_singleton.1 $$ H2 with H2
    icases ghostMapElem_valid_2 (K := Nat) (V := Unit) _ c.ex _ _ () () $$ H1 H2 with %Hv
    exact (dfrac_own_one_op_invalid _ Hv.1).elim

omit go_gctx in
/-- **Two shares of the same bytes agree.** -/
theorem bBytes_agree (p : BFile) (dq1 dq2 : DFrac) :
    ∀ (xs ys : List ByteG) (off : Nat), xs.length = ys.length →
    bBytes (GF := GF) p off dq1 xs ∗ bBytes p off dq2 ys ⊢
      bBytes p off dq1 xs ∗ bBytes p off dq2 ys ∗ ⌜xs = ys⌝
  | [], [], _, _ => by iintro ⟨H1, H2⟩; iframe; ipureintro; rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, off, h => by
    iintro ⟨H1, H2⟩
    icases (bBytes_cons p off dq1 x xs).1 $$ H1 with ⟨Hx, H1⟩
    icases (bBytes_cons p off dq2 y ys).1 $$ H2 with ⟨Hy, H2⟩
    iunfold bByte at Hx
    iunfold bByte at Hy
    icases Hx with ⟨Hx, Gx⟩
    icases Hy with ⟨Hy, Gy⟩
    unfold osByte
    ihave %hxy := gElem_valid_2 _ _ _ _ _ x y $$ Hx Hy
    obtain ⟨-, rfl⟩ := hxy
    icases bBytes_agree p dq1 dq2 xs ys (off + 1) (by simpa using h) $$ [H1 H2] with
      ⟨H1, H2, %he⟩
    · iframe
    subst he
    isplitl [Hx Gx H1]
    · iapply (bBytes_cons p off dq1 x xs).2; unfold bByte osByte; iframe
    isplitl [Hy Gy H2]
    · iapply (bBytes_cons p off dq2 x xs).2; unfold bByte osByte; iframe
    ipureintro; rfl

/-! ## The writer's share of the `OsMeta` -/

/-- **The file's crash invariant**, if any (persistent; `isBoltCoreP` holds it). -/
def bCsInv (p : BFile) : IProp GF :=
  match p.cs with
  | none => iprop(True)
  | some c => csInvI c.N p.ino c.g c.ga c.gc bCsOk

omit go_gctx in
instance bCsInv_persistent (p : BFile) : Persistent (bCsInv (GF := GF) p) := by
  unfold bCsInv; cases p.cs <;> dsimp only <;> infer_instance

theorem bCsInv_none {p : BFile} (h : p.cs = none) : ⊢ bCsInv (GF := GF) p := by
  unfold bCsInv; rw [h]; exact true_intro

theorem bNsOk_none {p : BFile} (h : p.cs = none) : bNsOk p := fun c hc => by rw [h] at hc; cases hc

/-- Every byte of `bs` outside the ranges `L` (`(offset, length)`: what was written or grown since
the last successful sync) is durable: one candidate, its value. -/
def DurOut (L : List (Nat × Nat)) (bs : List ByteG) : Prop :=
  ∀ k x, bs[k]? = some x → (∀ r ∈ L, k < r.1 ∨ r.1 + r.2 ≤ k) → x = durB x.1

/-- The exclusivity tokens' keys of a file of `n` bytes. -/
def exMap : Nat → GMap Nat Unit
  | 0 => ∅
  | n + 1 => (exMap n).insert n ()

/-- **The writer's whole share of the file's `OsMeta` `m`, the committed state being `C`** (see the
file header): `osMeta 1`, or (in the crash invariant) the invariant, half of the `OsMeta` and the
caller's token of the invariant's state `⟨m, bs, 0, 0, .idle⟩` (the file's bytes `bs`, nothing
frozen), the authority of the bytes' exclusivity tokens (`bGhost`) and value `a`, idle at `C`; the
bytes outside the ranges `L` written since the last successful sync are durable (`DurOut`; between
the writer's operations `L = []`), the file system does not fail (`FsNoErr`: crash mode is chosen
only then, so every error arm of a call in crash mode is refuted), and the crash sizes the
`OsMeta` knows are the size alone (`XsOne`: a sync leaves it, a write inside the file and a failed
truncate keep it, `DB.grow`'s truncate adds its target until its sync; `lh`, see `bMeta`/`bMetaT`)
(the invariant itself is `bCsInv p`). -/
def bMetaG (lh : Bool) (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) : IProp GF :=
  match p.cs with
  | none => osMeta p.ino (DFrac.own 1) m
  | some c => iprop(osMeta p.ino (DFrac.own (1 : Qp).half) m ∗
      ghostMapAuth (K := Nat) (V := Unit) c.ex 1 (exMap m.size) ∗
      ∃ (bs : List ByteG) (a : BAbs), csTokI c.g c.ga a (⟨m, bs, 0, 0, .idle⟩ : CSt) ∗
        ⌜(⟨m, bs, 0, 0, .idle⟩ : CSt).Wf ∧ a.phase = .idle ∧ a.cur = C ∧ DurOut L bs ∧
          FsNoErr ∧ (lh = true → XsOne m)⌝)

/-- **The writer's whole share of the file's `OsMeta` `m`** (`bMetaG`, the crash sizes the size
alone: what the writer's state holds and every operation but `DB.grow`'s truncate keeps; a write in
flight needs it, `bDur_write_idle`). -/
def bMeta (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) : IProp GF :=
  bMetaG true p C L m

/-- **The share right after a growing truncate**, before its sync (`bMetaG`, the crash sizes not
the size alone: a crash may leave the old size or the new one, so no write may start). -/
def bMetaT (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) : IProp GF :=
  bMetaG false p C L m

omit go_gctx in
instance bMeta_timeless (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    Timeless (bMeta (GF := GF) p C L m) := by
  unfold bMeta bMetaG
  cases p.cs with
  | none => dsimp only; unfold osMeta; infer_instance
  | some c => dsimp only; unfold osMeta csTokI; infer_instance

omit go_gctx in
theorem bMeta_none {p : BFile} (h : p.cs = none) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    bMeta (GF := GF) p C L m = osMeta p.ino (DFrac.own 1) m := by
  unfold bMeta bMetaG; rw [h]

omit go_gctx in
theorem bMeta_to_os {p : BFile} (h : p.cs = none) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) : bMeta (GF := GF) p C L m ⊢ osMeta p.ino (DFrac.own 1) m := by
  rw [bMeta_none h]

omit go_gctx in
theorem bMeta_of_os {p : BFile} (h : p.cs = none) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) : osMeta (GF := GF) p.ino (DFrac.own 1) m ⊢ bMeta p C L m := by
  rw [bMeta_none h]

omit go_gctx in
/-- **After a failure, any committed state and ranges**: the file system can fail (`¬ FsNoErr`), so
the file is not in a crash invariant (crash mode records `FsNoErr`), and `bMeta` is `osMeta 1`. -/
theorem bMeta_err (p : BFile) (C C' : CommitSt) (L L' : List (Nat × Nat)) (m : OsMeta)
    (hne : ¬ FsNoErr) : bMeta (GF := GF) p C L m ⊢ bMeta p C' L' m := by
  unfold bMeta bMetaG
  cases p.cs with
  | none => exact .rfl
  | some c =>
    dsimp only
    iintro ⟨-, -, %bs, %a, -, %Hf⟩
    iexfalso; ipureintro; exact hne Hf.2.2.2.2.1

/-- A fraction of the writer's share of the `OsMeta`, at any fraction of the extension's (for the
crash-free specs that take any fraction: `Stat`, the mapped cells' reads). -/
theorem bMeta_osMeta (p : BFile) (C : CommitSt) (L : List (Nat × Nat)) (m : OsMeta) :
    bMeta (GF := GF) p C L m ⊢ ∃ q : Qp, osMeta p.ino (DFrac.own q) m ∗
      (osMeta p.ino (DFrac.own q) m -∗ bMeta p C L m) := by
  unfold bMeta bMetaG
  cases p.cs with
  | none =>
    dsimp only
    iintro Hm
    iexists 1; iframe; iintro H; iexact H
  | some c =>
    dsimp only
    iintro ⟨Hm, Ha, Ht⟩
    iexists (1 : Qp).half; iframe Hm
    iintro Hm; iframe

end res

end bbolt
end EtcdGrove
end Perennial
