/-
**A local caller's part** of a file in a crash invariant (Lean-first, no Rocq counterpart): for a
client that holds its half of the file's bytes spread over its own invariants (bbolt: the store
slots in `pagesInv`, the writer's slots, the meta slots), not in one hand, as `csOwnG`
(`CrashSt.lean`) asks.

`csOwnL Tok i s` is the token `Tok s`, the caller's half of the `OsMeta` and what the specs keep of
`s` (idle, nothing frozen); the caller's half of the bytes is not in it: each operation takes, as
`osBytes` at the fraction `½`, only the bytes it needs (a write its range, a sync the bytes it may
make durable), and gives back those it changed. The invariant's half of every byte stays the
invariant's (`invBytes_whole`: `osBytes ... 0 ½ s.bs` of an idle state with nothing frozen).

* `csOwnIL i γ γa s a`: `csOwnL` over `csInvI`'s token `csTokI γ γa a`; `csOwnI_split` is
  `csOwnI` as `csOwnIL` and the caller's half of every byte.
* `csInvI_alloc_c`/`csInvI_alloc_c_start`: `csInvI_alloc` with an existing closing name `γc` (the
  client keeps `csDone γc` where it wants it: bbolt's `boltState`'s validity token).
* `csOwnIL_ok`, `csOwnIL_agree`, `csOwnIL_setA`: `Ok` of the current state, the caller's bytes agree
  with the state's, a new value.
* The steps, over any `CsAcc`: `wp_osPWriteStart_L`/`wp_osPWriteFinish_L` (a write inside the
  file, of the bytes the caller passes), `wp_osFtruncateStart_L`/`wp_osFtruncateFinish_L` (the new
  bytes' half to the caller), `wp_osFsync_L` (the caller's half of the bytes of a mask `c`, every
  byte not yet durable outside it durable in the state: `wp_osFsyncC`, `FsyncMask.lean`),
  `wp_osMmap_L`, `wp_osMunmap_L`. The Go-level loops are in
  `CrashStILSpec.lean`.
-/
module

public import Proof.os.CrashStIOps
public import Proof.os.FsyncMask
public import GooseLang.Ext.Fs.FsNoErr
public import GooseLang.Ext.Fs.NoErrSpecsOpen
public import GooseLang.Ext.Fs.NoIoErrResize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {A : Type} [Pos.Countable A]

/-- What the local caller's part keeps of a state: what the specs keep (`CSt.Wf`), idle, nothing
frozen. -/
def CSt.LocOk (s : CSt) : Prop := s.Wf ∧ s.busy = .idle ∧ s.fa = 0 ∧ s.fb = 0

/-- **The local caller's part of the file `i` in the state `s`**, its token `Tok s`: the token, the
caller's half of the `OsMeta`, and `CSt.LocOk`; no bytes. -/
abbrev csOwnL (Tok : CSt → IProp GF) (i : Ino) (s : CSt) : IProp GF :=
  iprop(Tok s ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) s.m ∗ ⌜s.LocOk⌝)

/-- `csOwnL` over `csInvI`'s token. -/
abbrev csOwnIL (i : Ino) (γ γa : GName) (s : CSt) (a : A) : IProp GF :=
  csOwnL (L := L) (csTokI γ γa a) i s

instance csOwnIL_timeless (i : Ino) (γ γa : GName) (s : CSt) (a : A) :
    Timeless (csOwnIL (L := L) i γ γa s a) := by
  unfold csOwnIL csOwnL csTokI; infer_instance

/-- Making the local caller's part, its `OsMeta` given as `m`. -/
theorem csOwnL_intro (Tok : CSt → IProp GF) (i : Ino) (s : CSt) (m : OsMeta) (hm : s.m = m)
    (h : s.LocOk) :
    Tok s ∗ osMeta (L := L) i (DFrac.own (1 : Qp).half) m ⊢ csOwnL (L := L) Tok i s := by
  subst hm
  unfold csOwnL; iintro ⟨Ht, Hm⟩; iframe; ipureintro; exact h

theorem csOwnL_locOk (Tok : CSt → IProp GF) (i : Ino) (s : CSt) :
    csOwnL (L := L) Tok i s ⊢ ⌜s.LocOk⌝ := by
  unfold csOwnL; iintro ⟨-, -, %h⟩; ipureintro; exact h

/-- The invariant's bytes of a state no write in flight took any of, nothing frozen: half of
each. -/
theorem invBytes_whole (p : Ino) (s : CSt) (ht : ∀ k, s.taken k = false) (hf : s.fb ≤ s.fa) :
    invBytes (L := L) p s ⊣⊢ osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) s.bs := by
  unfold invBytes
  exact cBytes_full p _ _ _ 0 s.bs fun k _ =>
    ⟨by simp [ht], CSt.frac_out _ _ (by omega)⟩

theorem taken_idle (s : CSt) (hb : s.busy = .idle) (k : Nat) : s.taken k = false := by
  simp [CSt.taken, hb]

theorem taken_trunc (s : CSt) (t sz n : Nat) (hb : s.busy = .trunc t sz n) (k : Nat) :
    s.taken k = false := by
  simp [CSt.taken, hb]

/-- **`csOwnI` is the local part and the caller's half of every byte.** -/
theorem csOwnI_split (i : Ino) (γ γa : GName) (s : CSt) (a : A) (hb : s.busy = .idle)
    (hfa : s.fa = 0) (hfb : s.fb = 0) :
    csOwnI (L := L) i γ γa s a ⊣⊢
      csOwnIL (L := L) i γ γa s a ∗ osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) s.bs := by
  refine (csOwnI_idle i γ γa s a hb (by omega)).trans ?_
  unfold csOwnIL csOwnL CSt.LocOk
  constructor
  · iintro ⟨Ht, ⟨Hm, Hb⟩, %Hwf⟩
    iframe; ipureintro; exact ⟨Hwf, hb, hfa, hfb⟩
  · iintro ⟨⟨Ht, Hm, %Hwf⟩, Hb⟩
    iframe; ipureintro; exact Hwf.1

/-- Bytes of a file, one first. -/
theorem osBytes_consL (i : Ino) (off : Nat) (dq : DFrac) (x : ByteG) (xs : List ByteG) :
    osBytes (L := L) i off dq (x :: xs) ⊣⊢ osByte (L := L) i off dq x ∗ osBytes (L := L) i (off + 1) dq xs := by
  unfold osBytes osByte; exact bytesG_cons _ _ _ _ _ _

/-- Bytes of a file end to end. -/
theorem osBytes_appendL (i : Ino) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    osBytes (L := L) i off dq (xs ++ ys) ⊣⊢
      osBytes (L := L) i off dq xs ∗ osBytes (L := L) i (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

/-- Two shares of the same bytes, of the same length, agree. -/
theorem osBytes_agreeL (i : Ino) :
    ∀ (xs ys : List ByteG) (off : Nat) (dq1 dq2 : DFrac), xs.length = ys.length →
    osBytes (L := L) i off dq1 xs ∗ osBytes (L := L) i off dq2 ys ⊢
      osBytes (L := L) i off dq1 xs ∗ osBytes (L := L) i off dq2 ys ∗ ⌜xs = ys⌝
  | [], [], _, _, _, _ => by iintro ⟨H1, H2⟩; iframe; ipureintro; rfl
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: xs, y :: ys, off, dq1, dq2, h => by
    iintro ⟨H1, H2⟩
    icases (osBytes_consL i off dq1 x xs).1 $$ H1 with ⟨Hx, H1⟩
    icases (osBytes_consL i off dq2 y ys).1 $$ H2 with ⟨Hy, H2⟩
    unfold osByte
    ihave %hxy := gElem_valid_2 _ _ _ _ _ x y $$ Hx Hy
    obtain ⟨-, rfl⟩ := hxy
    icases osBytes_agreeL i xs ys (off + 1) dq1 dq2 (by simpa using h) $$ [H1 H2] with
      ⟨H1, H2, %he⟩
    · iframe
    subst he
    isplitl [Hx H1]
    · iapply (osBytes_consL i off dq1 x xs).2; unfold osByte; iframe
    isplitl [Hy H2]
    · iapply (osBytes_consL i off dq2 x xs).2; unfold osByte; iframe
    ipureintro; rfl

/-- The bytes of a list, around a range `[off, off + n)` inside it. -/
theorem osBytes_around (i : Ino) (dq : DFrac) (bs : List ByteG) (off n : Nat)
    (h : off + n ≤ bs.length) :
    osBytes (L := L) i 0 dq bs ⊣⊢ osBytes (L := L) i 0 dq (bs.take off) ∗
      osBytes (L := L) i off dq ((bs.drop off).take n) ∗
      osBytes (L := L) i (off + n) dq (bs.drop (off + n)) := by
  have e : bs = bs.take off ++ ((bs.drop off).take n ++ bs.drop (off + n)) := by
    conv => lhs; rw [← List.take_append_drop off bs]
    congr 1
    rw [← List.drop_drop, List.take_append_drop]
  have hl1 : 0 + (bs.take off).length = off := by simp only [List.length_take]; omega
  have hl2 : off + ((bs.drop off).take n).length = off + n := by
    simp only [List.length_take, List.length_drop]; omega
  have A1 := osBytes_appendL (L := L) i 0 dq (bs.take off) ((bs.drop off).take n ++ bs.drop (off + n))
  rw [hl1] at A1
  have A2 := osBytes_appendL (L := L) i off dq ((bs.drop off).take n) (bs.drop (off + n))
  rw [hl2] at A2
  conv => lhs; rw [e]
  exact A1.trans (sep_congr .rfl A2)

/-- **A file whole and idle, nothing frozen, in a `csInvI` whose closing name `γc` the caller
has** (it keeps `csDone γc` elsewhere): the caller's part. -/
theorem csInvI_alloc_c (N : Namespace) (i : Ino) (γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) (hwf : s.Wf)
    (hcut : s.m.cut = none) (hok : Ok a s) :
    ⊢ osMeta (L := L) i (DFrac.own 1) s.m -∗ osBytes (L := L) i 0 (DFrac.own 1) s.bs ={E}=∗
      ∃ γ γa, csInvI (L := L) N i γ γa γc Ok ∗ csOwnI (L := L) i γ γa s a := by
  iintro Hm Hb
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  imod ghostVar_alloc (GF := GF) a with ⟨%γa, Ha⟩
  icases (ghostVar_split_half (A := CSt) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (ghostVar_split_half (A := A) γa 1 _).1 $$ Ha with ⟨Ha1, Ha2⟩
  icases csStartRes_split (L := L) (some (i, s)) (fun _ _ h => by cases h; exact ⟨hb, hf⟩)
    $$ [Hm Hb] with ⟨Hi, Hth⟩
  · dsimp only [csStartRes]; iframe
  imod inv_alloc N E (csInvIBody (L := L) i γ γa γc Ok) $$ [Hv1 Ha1 Hi] with #Hinv
  · inext; unfold csInvIBody; ileft; iexists s, a; iframe; ipureintro; exact ⟨hok, hcut⟩
  imodintro
  iexists γ, γa
  unfold csInvI csOwnI csOwnG csTokI
  iframe Hinv Hv2 Ha2 Hth
  ipureintro; exact hwf

/-- `csInvI_alloc_c` for the file `f` as a generation starts with it (`osFileStart`). -/
theorem csInvI_alloc_c_start (N : Namespace) (i : Ino) (γc : GName) (Ok : A → CSt → Prop)
    (f : OsFile) (a : A) (E : CoPset) (hok : Ok a (csStartI f)) :
    ⊢ osFileStart (L := L) i f ={E}=∗
      ∃ γ γa, csInvI (L := L) N i γ γa γc Ok ∗ csOwnI (L := L) i γ γa (csStartI f) a := by
  show ⊢ osMeta (L := L) i (DFrac.own 1) (csStartI f).m ∗
    osBytes (L := L) i 0 (DFrac.own 1) (csStartI f).bs ={E}=∗ _
  iintro ⟨Hm, Hb⟩
  iapply csInvI_alloc_c N i γc Ok (csStartI f) a E rfl (Nat.le_refl _) (csStart_wf i f)
    (csStart_cut i f) hok $$ Hm Hb

/-- **`Ok` of the caller's state**, opening the invariant. -/
theorem csOwnIL_ok (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ csOwnIL (L := L) i γ γa s a ={E}=∗
      csOwnIL (L := L) i γ γa s a ∗ ⌜Ok a s ∧ s.m.cut = none⌝ := by
  unfold csOwnIL csOwnL csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Hm, %Hl⟩
  imod csInvI_open N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, %Hok, Hclose⟩
  imod Hclose $$ [Hv' Ha' Hr] with -
  · inext; unfold csInvIBody; ileft; iexists s, a; iframe; ipureintro; exact Hok
  imodintro
  iframe
  ipureintro; exact ⟨Hl, Hok⟩

/-- **The caller's bytes are the state's**, inside the file (opening the invariant, whose half of
every byte agrees with them). -/
theorem csOwnIL_agree (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) (off : Nat) (dq : DFrac) (xs : List ByteG)
    (hl : off + xs.length ≤ s.bs.length) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ csOwnIL (L := L) i γ γa s a -∗ osBytes (L := L) i off dq xs ={E}=∗
      csOwnIL (L := L) i γ γa s a ∗ osBytes (L := L) i off dq xs ∗
        ⌜xs = (s.bs.drop off).take xs.length⌝ := by
  unfold csOwnIL csOwnL csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Hm, %Hl⟩ Hx
  obtain ⟨hwf0, hb, hfa, hfb⟩ := Hl
  imod csInvI_open N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, %Hok, Hclose⟩
  icases (invResS_idle _ _ hb).1 $$ Hr with ⟨Hm2, Hb2⟩
  icases (invBytes_whole i s (taken_idle s hb) (by omega)).1 $$ Hb2 with Hb2
  icases (osBytes_around i _ s.bs off xs.length hl).1 $$ Hb2 with ⟨H1, H2, H3⟩
  icases osBytes_agreeL i xs ((s.bs.drop off).take xs.length) off dq _
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hx H2] with ⟨Hx, H2, %he⟩
  · iframe
  ihave Hb2 := (osBytes_around i _ s.bs off xs.length hl).2 $$ [H1 H2 H3]
  · iframe
  ihave Hb2 := (invBytes_whole i s (taken_idle s hb) (by omega)).2 $$ Hb2
  imod Hclose $$ [Hv' Ha' Hm2 Hb2] with -
  · inext; unfold csInvIBody; ileft; iexists s, a; iframe
    isplitl
    · iapply (invResS_idle _ _ hb).2; iframe
    ipureintro; exact Hok
  imodintro
  iframe
  ipureintro; exact ⟨⟨hwf0, hb, hfa, hfb⟩, he⟩

/-- **A new value** `a'` for the local caller's part, of which the caller shows `Ok` of its
state. -/
theorem csOwnIL_setA (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a a' : A) (E : CoPset) (hE : ↑N ⊆ E) (hok : Ok a' s) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ csOwnIL (L := L) i γ γa s a ={E}=∗
      csOwnIL (L := L) i γ γa s a' := by
  unfold csOwnIL csOwnL csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Hm, %Hl⟩
  imod csInvI_open N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, %Hok, Hclose⟩
  imod ghostVar_update_halves a' γa _ _ $$ Ha Ha' with ⟨Ha, Ha'⟩
  imod Hclose $$ [Hv' Ha' Hr] with -
  · inext; unfold csInvIBody; ileft; iexists s, a'; iframe; ipureintro; exact ⟨hok, Hok.2⟩
  imodintro
  iframe
  ipureintro; exact Hl

/-- Bytes of a mask, all of a list's, as those of `c` and those not. -/
theorem cBytes_split2 (p : Ino) (dq : DFrac) (c : Nat → Bool) (off : Nat) (l : List ByteG) :
    cBytes (L := L) p (fun _ => dq) (fun _ => true) off l ⊣⊢
      cBytes (L := L) p (fun _ => dq) c off l ∗ cBytes (L := L) p (fun _ => dq) (fun k => !c k) off l := by
  refine cBytes_sep p _ _ _ _ _ _ off l fun k x _ => ?_
  unfold cByte
  dsimp only
  rcases Bool.eq_false_or_eq_true (c (off + k)) with hc | hc <;>
    simp only [hc, Bool.not_false, Bool.not_true, if_true, Bool.false_eq_true, if_false,
      eq_self_iff_true]
  · exact sep_emp.symm
  · exact emp_sep.symm

/-- Bytes of a mask, whole, as two halves. -/
theorem cBytes_halvesC (p : Ino) (c : Nat → Bool) (off : Nat) (l : List ByteG) :
    cBytes (L := L) p (fun _ => DFrac.own 1) c off l ⊣⊢
      cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half) c off l ∗
        cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half) c off l := by
  refine cBytes_sep p _ _ _ _ _ _ off l fun k x _ => ?_
  unfold cByte
  dsimp only
  rcases Bool.eq_false_or_eq_true (c (off + k)) with hc | hc <;>
    simp only [hc, if_true, Bool.false_eq_true, if_false, eq_self_iff_true]
  · exact osByte_halves p _ x
  · exact emp_sep.symm

/-- Bytes of a mask with the same values where it holds. -/
theorem cBytes_vals (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) :
    ∀ (off : Nat) (xs ys : List ByteG), xs.length = ys.length →
    (∀ k (h1 : k < xs.length) (h2 : k < ys.length), c (off + k) = true → xs[k] = ys[k]) →
    cBytes (L := L) p d c off xs ⊣⊢ cBytes (L := L) p d c off ys
  | _, [], [], _, _ => .rfl
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h
  | off, x :: xs, y :: ys, hl, h => by
    refine (cBytes_consC p d c off x xs).trans (BiEntails.trans ?_ (cBytes_consC p d c off y ys).symm)
    refine sep_congr ?_ (cBytes_vals p d c (off + 1) xs ys (by simpa using hl) fun k h1 h2 hc =>
      by have := h (k + 1) (by simp; omega) (by simp; omega)
           (by rw [show off + (k + 1) = off + 1 + k by omega]; exact hc); simpa using this)
    unfold cByte
    by_cases hc : c off = true
    · have := h 0 (by simp) (by simp) (by simpa using hc)
      simp only [List.getElem_cons_zero] at this
      rw [this]
      try exact .rfl
    · rw [if_neg hc, if_neg hc]
      try exact .rfl

/-- **A run as a mask**: the bytes `[lo, lo + n)` of a list, as `cBytes` over the whole list (for
`wp_osFsync_L`'s mask, made of the caller's runs with `cBytes_or`). -/
theorem cBytes_range (p : Ino) (dq : DFrac) (bs : List ByteG) (lo n : Nat) (h : lo + n ≤ bs.length) :
    cBytes (L := L) p (fun _ => dq) (fun k => decide (lo ≤ k ∧ k < lo + n)) 0 bs ⊣⊢
      osBytes (L := L) p lo dq ((bs.drop lo).take n) := by
  refine (cBytes_split3 p _ _ lo (lo + n) bs (by omega) h).trans ?_
  rw [show lo + n - lo = n by omega]
  refine (sep_congr (cBytes_none p _ _ 0 _ fun k hk => ?_) (sep_congr
    (cBytes_full p _ _ dq lo _ fun k hk => ⟨?_, rfl⟩) (cBytes_none p _ _ (lo + n) _ fun k hk => ?_))).trans ?_
  · simp only [List.length_take] at hk; simp only [decide_eq_false_iff_not]; omega
  · simp only [List.length_take, List.length_drop] at hk; simp only [decide_eq_true_eq]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · exact ⟨by iintro ⟨-, H, -⟩; iexact H,
      by iintro H; isplitl []; · iempintro
         isplitl [H]; · iexact H
         iempintro⟩

/-- **Two disjoint masks together.** -/
theorem cBytes_or (p : Ino) (d : Nat → DFrac) (c1 c2 : Nat → Bool) (off : Nat) (l : List ByteG)
    (hd : ∀ k, c1 k = true → c2 k = false) :
    cBytes (L := L) p d (fun k => c1 k || c2 k) off l ⊣⊢
      cBytes (L := L) p d c1 off l ∗ cBytes (L := L) p d c2 off l := by
  refine cBytes_sep p _ _ _ _ _ _ off l fun k x _ => ?_
  unfold cByte
  dsimp only
  rcases Bool.eq_false_or_eq_true (c1 (off + k)) with h1 | h1
  · simp only [h1, hd _ h1, Bool.true_or, if_true, if_false, Bool.false_eq_true, eq_self_iff_true]
    exact sep_emp.symm
  · rcases Bool.eq_false_or_eq_true (c2 (off + k)) with h2 | h2 <;>
      simp only [h1, h2, Bool.false_or, if_true, if_false, Bool.false_eq_true, eq_self_iff_true]
    · exact emp_sep.symm
    · exact emp_sep.symm

end res

/-! ## The steps -/

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **A fact of a step's result under a condition `P`** (`FsNoErr`), from the step-level fact under
`P` (`wp_ext_post` of a `*_noErr` lemma). -/
theorem wp_post_cond {s : Stuckness} {E : CoPset} {o : String} {v : val} (P : Prop)
    (Ψ : val → Prop) (Φ : val → IProp GF)
    (hpost : P → (WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ r, ⌜Ψ r⌝ -∗ Φ r }} ⊢
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }})) :
    WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ r, ⌜P → Ψ r⌝ -∗ Φ r }} ⊢
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  by_cases hP : P
  · refine BIBase.Entails.trans ?_ (hpost hP)
    iintro H
    iapply wp_wand $$ H
    iintro %r H %hr
    iapply H; ipureintro; exact fun _ => hr
  · iintro H
    iapply wp_wand $$ H
    iintro %r H
    iapply H; ipureintro; exact fun h => absurd h hP

/-- `wp_post_cond` with a resource `W` the step-level fact reads the state from (`wp_ext_postS`). -/
theorem wp_post_condS {s : Stuckness} {E : CoPset} {o : String} {v : val} (P : Prop) (W : IProp GF)
    (Ψ : val → Prop) (Φ : val → IProp GF)
    (hpost : P → ⊢ W -∗ (W -∗ WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ r, ⌜Ψ r⌝ -∗ Φ r }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }}) :
    ⊢ W -∗ (W -∗ WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ r, ⌜P → Ψ r⌝ -∗ Φ r }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  by_cases hP : P
  · iintro HW H
    iapply (hpost hP) $$ HW
    iintro HW
    iapply wp_wand $$ [HW H]
    · iapply H $$ HW
    iintro %r H %hr
    iapply H; ipureintro; exact fun _ => hr
  · iintro HW H
    iapply wp_wand $$ [HW H]
    · iapply H $$ HW
    iintro %r H
    iapply H; ipureintro; exact fun h => absurd h hP

/-- A write inside the file takes the bytes of its range. -/
theorem cfRange_in (m : OsMeta) (bs : List ByteG) (off n : Nat) (h : off + n ≤ m.size) :
    cfRange m bs off n = (bs.drop off).take n := by
  unfold cfRange cfLo cfHi
  rw [Nat.min_eq_left (show off ≤ m.size by omega), Nat.min_eq_left h,
    show off + n - off = n by omega]

/-- `pwrite`'s first step on a file in a crash invariant, from the local caller's part, the
write inside the file: the caller passes its half of the range (`xs`, which is the state's); the
write is in flight, which the caller shows `Ok`; the token is the caller's. -/
theorem wp_osPWriteStart_L (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok d.ino) (m : OsMeta) (bs xs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hin : off.toNat + data.length ≤ m.size) (hd : data ≠ []) (hxl : xs.length = data.length)
    (hok : ∀ t n, PwFresh m bs off.toNat data n → Ok ⟨m, bs, 0, 0, .write t off.toNat data n⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ osFd (L := L) fd dq d -∗
      csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩ -∗
      osBytes (L := L) d.ino off.toNat (DFrac.own (1 : Qp).half) xs -∗
      mcellsAny (L := L) m.maps off.toNat (off.toNat + data.length) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜PwFresh m bs off.toNat data n ∧ xs = (bs.drop off.toNat).take data.length⌝ -∗
        osFd (L := L) fd dq d -∗ Tok ⟨m, bs, 0, 0, .write t off.toNat data n⟩ -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd ⟨Hv, Hm1, %Hl⟩ Hx Hc HΦ
  obtain ⟨⟨hl, -, -, -⟩, -, -, -⟩ := Hl
  dsimp only at hl
  have hlo : cfLo m off.toNat = off.toNat := Nat.min_eq_left (by omega)
  have hr : cfRange m bs off.toNat data.length = (bs.drop off.toNat).take data.length :=
    cfRange_in m bs _ _ hin
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (write_invBytes d.ino m bs 0 0 0 off.toNat data 0 hl (Nat.zero_le _)
    (.inr (Nat.zero_le _))).1 $$ Hb2 with ⟨Hb2, Hr2⟩
  ihave Hr2 := (show osBytes (L := L) d.ino (cfLo m off.toNat) (DFrac.own (1 : Qp).half)
      (cfRange m bs off.toNat data.length) ⊢ osBytes (L := L) d.ino off.toNat
      (DFrac.own (1 : Qp).half) ((bs.drop off.toNat).take data.length) by rw [hlo, hr]) $$ Hr2
  icases osBytes_agreeL d.ino xs ((bs.drop off.toNat).take data.length) off.toNat _ _
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hx Hr2] with ⟨Hx, Hr2, %hxs⟩
  · iframe
  subst hxs
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hx Hr2]
  · iframe
  imodintro
  iapply wp_osPWriteStart fd off data dq d m ((bs.drop off.toNat).take data.length) hN hwr hoff
    (by omega) hd (by simp only [List.length_take, List.length_drop]; omega)
    $$ Hos Hfd Hm Hrg Hc
  iintro %t %n %hfr Hfd Ht
  have hfr' : PwFresh m bs off.toNat data n := by
    refine ⟨?_, hfr.2⟩
    rw [hr]; exact hfr.1
  imod Hclose $$ %(⟨m, bs, 0, 0, .write t off.toNat data n⟩ : CSt) %(And.intro (hok t n hfr') hcut)
    [Ht Hb2] with Hv
  · dsimp only [invResS, metaRes]; isplitl [Ht]
    · rw [hr]; iexact Ht
    · iapply (show invBytes (L := L) d.ino ⟨m, bs, 0, 0, .write 0 off.toNat data 0⟩ ⊢
        invBytes (L := L) d.ino ⟨m, bs, 0, 0, .write t off.toNat data n⟩ from .rfl)
      iexact Hb2
  imodintro
  have hP : PwFresh m bs off.toNat data n ∧
      (bs.drop off.toNat).take data.length = (bs.drop off.toNat).take data.length := ⟨hfr', rfl⟩
  iapply HΦ $$ %t %n %hP Hfd Hv

/-- `pwrite`'s second step on a file in a crash invariant, the write inside the file: idle again,
as the write of the first `k` bytes left it, which the caller shows `Ok`; the caller gets back its
half of the range, as written. -/
theorem wp_osPWriteFinish_L (t : Nat) (p : Ino) (off : Nat) (data : List w8) (n : Nat)
    (N : Namespace) (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok p) (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hl : bs.length = m.size) (hin : off + data.length ≤ m.size)
    (hmax : off < maxBytes)
    (hok : ∀ k, k ≤ data.length →
      Ok ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ Tok ⟨m, bs, 0, 0, .write t off data n⟩ -∗
      (∀ (k : Nat) (e : w64),
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          ZsOk m [] ∧ pwSize m.size off k = m.size ∧ (e ≠ 0 → ¬ FsNoErr)⌝ -∗
        csOwnL (L := L) Tok p ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩ -∗
        osBytes (L := L) p off (DFrac.own (1 : Qp).half)
          (pwBytes m.size off data k n (cfRange m bs off data.length) []) -∗
        mcells (L := L) m.maps off (off + data.length)
          (pwCell m.size off data k (cfRange m bs off data.length)) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hv HΦ
  have hgap : off ≤ m.size := by omega
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  dsimp only [invResS, metaRes]
  icases Hr with ⟨Ht, Hb2⟩
  have hlo : cfLo m off = off := Nat.min_eq_left hgap
  imodintro
  iapply (wp_post_condS FsNoErr (pwTok (L := L) t p off data m (cfRange m bs off data.length) n)
    (fun r => ∃ r0, r = PairV r0 (#(0 : w64))) _ (fun hno => by
      obtain ⟨Sio, hi, h1, -, -⟩ := hno
      haveI := h1
      exact wp_ext_postS "PWriteFinish" (osTokV t) (by simp [val.isPanic]) _ _
        (pwTok_inflight t p off data m _ n) _
        (fun h st g e' h' st' g' ⟨c, hc, hk⟩ hs => pwFinish_noErr (Sio := Sio) hi t c off data hmax
          h st g e' h' st' g' ⟨hc, hk⟩ hs) _)) $$ Ht
  iintro Ht
  iapply wp_osPWriteFinishK true t p off data m (cfRange m bs off data.length) n hN $$ Hos Ht
  iintro %k %e %zs %hke %hzt %- Hm Hrg Hc %hne
  have hfe : e ≠ 0 → ¬ FsNoErr := fun he hno => by
    obtain ⟨r0, hr⟩ := hne hno
    exact he (go.intoVal_inj (val.PairV.inj hr).2)
  have hk := hke.1
  have hps : pwSize m.size off k = m.size := by unfold pwSize; split <;> omega
  have hz : zs = [] := List.eq_nil_of_length_eq_zero (by rw [hke.2.2.1, hps]; omega)
  subst hz
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  ihave Hr2 := (show osBytes (L := L) p off (DFrac.own (1 : Qp).half)
      (pwBytes m.size off data k n (cfRange m bs off data.length) []) ⊢
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half)
      (pwBytes m.size off data k n (cfRange m bs off data.length) []) by rw [hlo]) $$ Hr2
  have hout : ∀ j, (j < cfLo m off ∨ cfHi m off data.length ≤ j) →
      CSt.taken ⟨m, bs, 0, 0, .write t off data n⟩ j = false := fun j hj =>
    CSt.taken_out _ j (fun t' o d' n' h => by cases h; omega)
  ihave Hb2 := (show invBytes (L := L) p ⟨m, bs, 0, 0, .write t off data n⟩ ⊢
      cBytes (L := L) p (CSt.frac ⟨m, bs, 0, 0, .write t off data n⟩)
      (fun j => !CSt.taken ⟨m, bs, 0, 0, .write t off data n⟩ j) 0 bs from .rfl) $$ Hb2
  ihave Hb2 := cBytes_fin (L := L) p (CSt.frac ⟨m, bs, 0, 0, .write t off data n⟩)
    (CSt.frac ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩)
    (fun j => !CSt.taken ⟨m, bs, 0, 0, .write t off data n⟩ j)
    (fun j => !CSt.taken ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩ j)
    (DFrac.own (1 : Qp).half) m bs off data k n [] hl
    (fun j hj => ⟨by rw [hout j (.inl hj)]; rfl, fun _ => rfl⟩)
    (fun j hj => ⟨by rw [hout j (.inr hj)]; rfl, fun _ => rfl⟩)
    (fun j h1 h2 => by rw [CSt.taken_in _ j t off data n rfl h1 h2]; rfl)
    (fun j h1 h2 => ⟨rfl, CSt.frac_out _ _ (by dsimp only; omega)⟩) $$ [Hb2 Hr2]
  · iframe
  ihave Hb2 := (show cBytes (L := L) p
      (CSt.frac ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩)
      (fun j => !CSt.taken ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩ j) 0
      (finBytes m bs off data k n []) ⊢
      invBytes (L := L) p ⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩
      from .rfl) $$ Hb2
  imod Hclose $$ %(⟨pwPostK true m off data k n, finBytes m bs off data k n [], 0, 0, .idle⟩ : CSt)
    %(And.intro (hok k hk) (by simp [hcut, OsMeta.announce, pwPostK, pwPost])) [Hm2 Hb2]
    with Hv
  · dsimp only; iframe
  imodintro
  have hP : k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
      ZsOk m [] ∧ pwSize m.size off k = m.size ∧ (e ≠ 0 → ¬ FsNoErr) := ⟨hk, hke.2.1, hzt, hps, hfe⟩
  iapply HΦ $$ %k %e %hP [Hv Hm1] Hr1 Hc
  unfold csOwnL
  iframe
  ipureintro
  refine ⟨⟨by rw [finBytes_length hl hgap hk]; rfl, Nat.le_refl _, Nat.zero_le _, trivial⟩,
    rfl, rfl, rfl⟩

/-- A growing truncate's first step on a file in a crash invariant, from the local caller's part,
with the client's halves of the mapped cells of the bytes it grows the file over: the truncate is in
flight, which the caller shows `Ok`; the token is the caller's. -/
theorem wp_osFtruncateStart_L (fd sz : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok d.ino) (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt)
    (hgrow : m.size ≤ sz.toNat)
    (hok : ∀ t n, Ok ⟨m, bs, 0, 0, .trunc t sz.toNat n⟩) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ osFd (L := L) fd dq d -∗
      csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩ -∗
      mcellsAny (L := L) m.maps m.size (rsHi true m.size sz.toNat) -∗
      (∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗
        Tok ⟨m, bs, 0, 0, .trunc t sz.toNat n⟩ -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd ⟨Hv, Hm1, %Hl⟩ Hc HΦ
  have hmin : min m.size sz.toNat = m.size := Nat.min_eq_left hgrow
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osFtruncateStart fd sz dq d m [] hN hwr hsz0 (by simp; omega) $$ Hos Hfd Hm [] [Hc]
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  · rw [hmin]; iexact Hc
  iintro %t %n %- Hfd Ht
  imod Hclose $$ %(⟨m, bs, 0, 0, .trunc t sz.toNat n⟩ : CSt) %(And.intro (hok t n) (hcut)) [Ht Hb2]
    with Hv
  · dsimp only [invResS, metaRes]; isplitl [Ht]
    · iexact Ht
    · iapply (show invBytes (L := L) d.ino ⟨m, bs, 0, 0, .idle⟩ ⊢
        invBytes (L := L) d.ino ⟨m, bs, 0, 0, .trunc t sz.toNat n⟩ from .rfl)
      iexact Hb2
  imodintro
  iapply HΦ $$ %t %n Hfd Hv

/-- The bytes a growing truncate adds: zeros, with the candidates `zs` they had, then the zero
announced as change `n`. -/
abbrev grownBytes (zs : List Cands) (n : Nat) : List ByteG :=
  zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))

/-- The local caller's part after a truncate grew the file to `sz`: the grown state, the caller's
half of the new bytes, and the mapped cells of the new bytes. -/
def csGrownL (Tok : CSt → IProp GF) (p : Ino) (m : OsMeta) (bs : List ByteG) (sz n : Nat) :
    IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = sz - m.size ∧
      ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ ∗
    csOwnL (L := L) Tok p ⟨rsPost true m sz sz, bs ++ grownBytes zs n, 0, 0, .idle⟩ ∗
    osBytes (L := L) p m.size (DFrac.own (1 : Qp).half) (grownBytes zs n) ∗
    mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsCell sz))

/-- A growing truncate's second step on a file in a crash invariant: grown, or, on failure, maybe
not (its `OsMeta` as the first step announced it), each of which the caller shows `Ok`. -/
theorem wp_osFtruncateFinish_L (t : Nat) (p : Ino) (sz n : Nat) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok p) (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hl : bs.length = m.size) (hgrow : m.size ≤ sz)
    (hmax : sz ≤ maxBytes)
    (hokG : ∀ zs : List Cands, zs.length = sz - m.size →
      Ok ⟨rsPost true m sz sz, bs ++ grownBytes zs n, 0, 0, .idle⟩)
    (hokF : Ok ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, 0, 0, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ Tok ⟨m, bs, 0, 0, .trunc t sz n⟩ -∗
      (∀ e : w64, ⌜e ≠ 0 → ¬ FsNoErr⌝ -∗
        ((⌜e = 0⌝ ∗ csGrownL (L := L) Tok p m bs sz n) ∨
         (⌜e ≠ 0⌝ ∗ (csGrownL (L := L) Tok p m bs sz n ∨
           (csOwnL (L := L) Tok p ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, 0, 0,
              .idle⟩ ∗
             mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []))))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hv HΦ
  have hmin : min m.size sz = m.size := Nat.min_eq_left hgrow
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (show invResS (L := L) (some (p, ⟨m, bs, 0, 0, .trunc t sz n⟩)) ⊢ rsTok (L := L) true t p sz m [] n ∗
    invBytes (L := L) p ⟨m, bs, 0, 0, .trunc t sz n⟩ from .rfl) $$ Hr with ⟨Ht, Hb2⟩
  icases (invBytes_whole p ⟨m, bs, 0, 0, .trunc t sz n⟩ (taken_trunc _ t sz n rfl)
    (Nat.le_refl _)).1 $$ Hb2 with Hb2
  imodintro
  iapply (wp_post_condS FsNoErr (rsTok (L := L) true t p sz m [] n) (· = #(0 : w64)) _ (fun hno => by
      obtain ⟨Sio, hi, h1, -, -⟩ := hno
      haveI := h1
      exact wp_ext_postS "FtruncateFinish" (osTokV t) (by simp [val.isPanic]) _ _
        (rsTok_inflight true t p sz m [] n) _
        (fun h st g e' h' st' g' ⟨c, hc, hk, htc⟩ hs => ftFinish_noErr (Sio := Sio) hi t c sz
          h st g e' h' st' g' ⟨hc, by simpa [rsKind] using hk, htc ▸ hmax⟩ hs) _)) $$ Ht
  iintro Ht
  iapply wp_osFtruncateFinish t p sz m [] n hN $$ Hos Ht
  iintro %e Hres %hne
  have hfe : e ≠ 0 → ¬ FsNoErr := fun he hno => he (go.intoVal_inj (hne hno))
  have hG : ∀ (Q : IProp GF), (csGrownL (L := L) Tok p m bs sz n -∗ Q) ⊢
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) bs -∗
      rsDone (L := L) true p sz sz m n -∗
      (∀ s' : CSt, ⌜Ok s' ∧ s'.m.cut = none⌝ -∗ invResS (L := L) (some (p, s')) ={(⊤ : CoPset) \ ↑N, ⊤}=∗
        Tok s') -∗
      |={(⊤ : CoPset) \ ↑N, ⊤}=> Q := by
    intro Q
    iintro HQ Hb2 Hg Hclose
    unfold rsDone
    icases Hg with ⟨%zs, %hzs, Hm, Hz, Hc⟩
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hz with ⟨Hz1, Hz2⟩
    ihave Hb2 := (osBytes_appendL p 0 _ bs (grownBytes zs n)).2 $$ [Hb2 Hz2]
    · iframe Hb2; rw [Nat.zero_add, hl]; iexact Hz2
    imod Hclose $$ %(⟨rsPost true m sz sz, bs ++ grownBytes zs n, 0, 0, .idle⟩ : CSt)
      %(And.intro (hokG zs hzs.1) (by simp [hcut, OsMeta.announce, rsPost])) [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe Hm2
      iapply (invBytes_whole p _ (taken_idle _ rfl) (Nat.le_refl _)).2; iexact Hb2
    imodintro
    iapply HQ
    unfold csGrownL
    iexists zs
    ihave Hc := (show mcells (L := L) m.maps (min m.size sz) (rsHi true m.size sz) (rsCell sz) ⊢
      mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsCell sz) by rw [hmin]) $$ Hc
    iframe Hc Hz1
    isplitr
    · ipureintro; exact ⟨hzs.1, hzs.2.1⟩
    have hgl : (bs ++ grownBytes zs n).length = sz := by
      simp only [grownBytes, List.length_append, List.length_map, hl, hzs.1]; omega
    iapply (csOwnL_intro Tok p _ _ rfl ⟨⟨hgl, Nat.le_refl _, Nat.zero_le _, trivial⟩, rfl, rfl, rfl⟩)
    iframe
  unfold rsUndone
  icases Hres with (⟨%he, Hg⟩ | ⟨%he, (Hg | ⟨Hm, -, Hc⟩)⟩)
  · iapply (hG _) $$ [HΦ] Hb2 Hg Hclose
    iintro H; iapply HΦ $$ %e %hfe; ileft; iframe; ipureintro; exact he
  · iapply (hG _) $$ [HΦ] Hb2 Hg Hclose
    iintro H; iapply HΦ $$ %e %hfe; iright; isplitr; · ipureintro; exact he
    ileft; iexact H
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ %(⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, 0, 0, .idle⟩ : CSt)
      %(And.intro (hokF) (by simp [hcut, OsMeta.announce])) [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe Hm2
      iapply (invBytes_whole p _ (taken_idle _ rfl) (Nat.le_refl _)).2; iexact Hb2
    imodintro
    iapply HΦ $$ %e %hfe; iright; isplitr; · ipureintro; exact he
    iright
    ihave Hc := (show mcells (L := L) m.maps (min m.size sz) (rsHi true m.size sz)
        (rsOld m.size (min m.size sz) []) ⊢
      mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []) by rw [hmin]) $$ Hc
    iframe Hc
    unfold csOwnL
    iframe Hv Hm1
    ipureintro
    exact ⟨⟨by rw [announce_size]; exact hl, Nat.le_refl _, Nat.zero_le _, trivial⟩, rfl, rfl, rfl⟩

/-- `mmap` of a file in a crash invariant, from the local caller's part: a new mapping (its cells
the client's halves, any values of the file's size) or, on failure, nothing, each of which the
caller shows `Ok`. -/
theorem wp_osMmap_L (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok d.ino) (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hrd : d.readable = true) (hoff : off = 0)
    (hlen : 0 < len.toInt) (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE)
    (hok : ∀ base : Loc, Ok ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ osFd (L := L) fd dq d -∗
      csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩ -∗
      (∀ base : Loc, ∀ e : w64,
        ((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            csOwnL (L := L) Tok d.ino ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩ ∗
            ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null ∧ ¬ FsNoErr⌝ ∗ csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩)) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#e))) -∗
      WP (ExternalOp fsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown HΦ
  have hN' : ↑N ⊆ (⊤ : CoPset) \ ↑osN := fun x hx =>
    Std.LawfulSet.mem_diff.2 ⟨CoPset.subseteq_top x hx,
      fun ho => (Std.LawfulSet.mem_diff.1 (hN x ho)).2 hx⟩
  iapply wp_osMmapG fd off len prot fl dq d m (((⊤ : CoPset) \ ↑osN) \ ↑N) CoPset.subseteq_top
    hrd hoff hlen hprot hfl (fun _ => ¬ FsNoErr)
    (fun h st e h' st' hfd hs he hno => by
      obtain ⟨Sio, hi, -, h2, -⟩ := hno
      haveI := h2
      exact mmap_noFail hi fd off len prot fl d hrd hoff hlen hprot hfl h st e h' st' hfd hs he)
    (csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩)
    (fun base e =>
      iprop((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            csOwnL (L := L) Tok d.ino ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩ ∗
            ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null ∧ ¬ FsNoErr⌝ ∗ csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩)))
    Φ $$ Hos [] HΦ Hfd Hown
  imodintro
  iintro ⟨Hv, Hm1, %Hl⟩
  imod hacc ((⊤ : CoPset) \ ↑osN) _ hN' $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iframe Hm
  iintro %r Hres
  rcases r with _ | ⟨base, e⟩
  · dsimp only [mmapRes, mmapPost]
    icases (osMeta_halves _ _).1 $$ Hres with ⟨Hm1, Hm2⟩
    imod Hclose $$ %(⟨m, bs, 0, 0, .idle⟩ : CSt) %Hok' [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe
    imodintro
    iapply (csOwnL_intro Tok d.ino _ _ rfl Hl)
    iframe
  dsimp only [mmapRes, mmapPost]
  icases Hres with (⟨%he, Hm, Hc⟩ | ⟨%he, Hm⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ %(⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩ : CSt)
      %(And.intro (hok base) (hcut)) [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe Hm2
      iapply (show invBytes (L := L) d.ino ⟨m, bs, 0, 0, .idle⟩ ⊢ invBytes (L := L) d.ino
        ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩ from .rfl)
      iexact Hb2
    imodintro
    ileft
    isplitr; · ipureintro; exact he
    iframe Hc
    unfold csOwnL
    iframe Hv Hm1
    ipureintro; exact Hl
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ %(⟨m, bs, 0, 0, .idle⟩ : CSt) %Hok' [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe
    imodintro
    iright
    isplitr; · ipureintro; exact he
    unfold csOwnL
    iframe
    ipureintro; exact Hl

/-- `munmap` of a mapping of a file in a crash invariant, from the local caller's part: the mapping
is gone, or (on failure) maybe not, each of which the caller shows `Ok`. -/
theorem wp_osMunmap_L (base : Loc) (len cap : w64) (p : Ino) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok p) (m : OsMeta) (bs : List ByteG) (n : Nat)
    (vf : Nat → val)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n)
    (hok : Ok ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗
      csOwnL (L := L) Tok p ⟨m, bs, 0, 0, .idle⟩ -∗ cellsR base 0 n vf -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwnL (L := L) Tok p ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩) ∨
         (⌜e ≠ 0 ∧ ¬ FsNoErr⌝ ∗
           (csOwnL (L := L) Tok p ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ ∨
            (csOwnL (L := L) Tok p ⟨m, bs, 0, 0, .idle⟩ ∗ cellsR base 0 n vf)))) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) {{ Φ }} := by
  iintro #Hos #Hinv ⟨Hv, Hm1, %Hl⟩ Hc HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply (wp_post_cond FsNoErr (· = #(0 : w64)) _ (fun hno => by
    obtain ⟨Sio, hi, -, h2, -⟩ := hno
    haveI := h2
    exact wp_ext_post "Munmap" _ (by simp [val.isPanic]) _ (munmap_noErr hi _) _))
  iapply wp_osMunmap base len cap p m n vf hN hb hlen hcap $$ Hos Hm Hc
  iintro %e Hres %hne
  have hfe : e ≠ 0 → ¬ FsNoErr := fun he hno => he (go.intoVal_inj (hne hno))
  have hD : ∀ (Q : IProp GF),
      (csOwnL (L := L) Tok p ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ -∗ Q) ⊢
      invBytes (L := L) p ⟨m, bs, 0, 0, .idle⟩ -∗
      osMeta (L := L) p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) -∗
      (∀ s' : CSt, ⌜Ok s' ∧ s'.m.cut = none⌝ -∗ invResS (L := L) (some (p, s')) ={(⊤ : CoPset) \ ↑N, ⊤}=∗
        Tok s') -∗
      |={(⊤ : CoPset) \ ↑N, ⊤}=> Q := by
    intro Q
    iintro HQ Hb2 Hm Hclose
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ %(⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ : CSt)
      %(And.intro (hok) (hcut)) [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe Hm2
      iapply (show invBytes (L := L) p ⟨m, bs, 0, 0, .idle⟩ ⊢ invBytes (L := L) p
        ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ from .rfl)
      iexact Hb2
    imodintro
    iapply HQ
    unfold csOwnL
    iframe Hv Hm1
    ipureintro; exact Hl
  icases Hres with (⟨%he, Hm⟩ | ⟨%he, (Hm | ⟨Hm, Hc⟩)⟩)
  · iapply (hD _) $$ [HΦ] Hb2 Hm Hclose
    iintro H; iapply HΦ; ileft; iframe; ipureintro; exact he
  · iapply (hD _) $$ [HΦ] Hb2 Hm Hclose
    iintro H; iapply HΦ; iright; isplitr; · ipureintro; exact ⟨he, hfe he⟩
    ileft; iexact H
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ %(⟨m, bs, 0, 0, .idle⟩ : CSt) %Hok' [Hm2 Hb2] with Hv
    · iapply (invResS_idle _ _ rfl).2; iframe
    imodintro
    iapply HΦ; iright; isplitr; · ipureintro; exact ⟨he, hfe he⟩
    iright; iframe Hc
    unfold csOwnL
    iframe
    ipureintro; exact Hl

/-- `fsync`/`fdatasync` of a file in a crash invariant, from the local caller's part: the caller
passes its half of the bytes of a mask `c` (`cBytes` of the state's bytes from 0) and shows every
byte not yet durable (`[dlo, dhi)`) outside the mask durable in the state; on success every byte is
durable (`csSynced`), which the caller shows `Ok`, and the caller's bytes come back so; on failure
nothing changes. -/
theorem wp_osFsync_L (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok d.ino) (m : OsMeta) (bs : List ByteG) (c : Nat → Bool)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hcov : ∀ b, b < m.size → m.dlo ≤ b → b < m.dhi →
      c b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1)
    (hok : Ok (csSynced m [] [] bs 0 0)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ osFd (L := L) fd dq d -∗
      csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩ -∗
      cBytes (L := L) d.ino (fun _ => DFrac.own (1 : Qp).half) c 0 bs -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwnL (L := L) Tok d.ino (csSynced m [] [] bs 0 0) ∗
            cBytes (L := L) d.ino (fun _ => DFrac.own (1 : Qp).half) c 0 (bs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR ∧ ¬ FsNoErr⌝ ∗ csOwnL (L := L) Tok d.ino ⟨m, bs, 0, 0, .idle⟩ ∗
            cBytes (L := L) d.ino (fun _ => DFrac.own (1 : Qp).half) c 0 bs)) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd ⟨Hv, Hm1, %Hl⟩ Hc HΦ
  have hl : bs.length = m.size := Hl.1.1
  have hsy : (csSynced m [] [] bs 0 0).bs = bs.map (fun x => durB x.1) := rfl
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  ihave Hb2 := (show invBytes (L := L) d.ino ⟨m, bs, 0, 0, .idle⟩ ⊢
      cBytes (L := L) d.ino (fun _ => DFrac.own (1 : Qp).half) (fun _ => true) 0 bs from
    (invBytes_whole d.ino _ (taken_idle _ rfl) (Nat.le_refl _)).1.trans
      (cBytes_full d.ino (fun _ => DFrac.own (1 : Qp).half) (fun _ => true) (DFrac.own (1 : Qp).half)
        0 bs fun _ _ => ⟨rfl, rfl⟩).2) $$ Hb2
  icases (cBytes_split2 d.ino _ c 0 bs).1 $$ Hb2 with ⟨Hi1, HD⟩
  ihave HF := (cBytes_halvesC d.ino c 0 bs).2 $$ [Hi1 Hc]
  · iframe
  imodintro
  iapply (wp_post_cond FsNoErr (· = #(0 : w64)) _ (fun hno => by
    obtain ⟨Sio, hi, h1, -, -⟩ := hno
    haveI := h1
    exact wp_ext_post "Fsync" (#fd) (by simp) _ (fsync_noErr hi fd) _))
  iapply wp_osFsyncC fd dq d m bs c (fun k => !c k) (DFrac.own (1 : Qp).half)
    (fun k hk hck h1 h2 => by
      rcases hcov k (by omega) h1 h2 with h | ⟨x, hx, hxd⟩
      · simp [h] at hck
      · rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hx; subst hx; exact hxd)
    (fun b hb h1 h2 => ⟨by omega, by cases hcb : c b <;> simp⟩) hN
    $$ Hos Hfd Hm HF HD
  iintro %e Hres Hfd HD %hne
  have hfe : e ≠ 0 → ¬ FsNoErr := fun he hno => he (go.intoVal_inj (hne hno))
  icases Hres with (⟨%he, Hm, HF⟩ | ⟨%he, Hm, HF⟩)
  · have hdd := he.2 hcut
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (cBytes_halvesC d.ino c 0 _).1 $$ HF with ⟨HF1, HF2⟩
    ihave HD := (cBytes_vals d.ino _ _ 0 bs (bs.map (fun x => durB x.1)) (by simp)
      (fun k h1 h2 hc => by
        rw [List.getElem_map]; exact hdd k h1 (by simpa using hc))).1 $$ HD
    ihave Hi := (cBytes_split2 d.ino _ c 0 _).2 $$ [HF1 HD]
    · iframe
    imod Hclose $$ %(csSynced m [] [] bs 0 0) %(And.intro hok (by simp [hcut, csSynced, OsMeta.synced]))
      [Hm2 Hi] with Hv
    · iapply (invResS_idle _ _ rfl).2
      rw [show (csSynced m [] [] bs 0 0).m = m.synced from rfl]
      isplitl [Hm2]
      · iexact Hm2
      iapply (invBytes_whole d.ino _ (taken_idle _ rfl) (Nat.le_refl _)).2
      rw [hsy]
      iapply (cBytes_full d.ino (fun _ => DFrac.own (1 : Qp).half) (fun _ => true)
        (DFrac.own (1 : Qp).half) 0 _ fun _ _ => ⟨rfl, rfl⟩).1
      iexact Hi
    imodintro
    have hLs : (csSynced m [] [] bs 0 0).LocOk :=
      ⟨⟨by show (bs.map _).length = m.synced.size; simp [OsMeta.synced, hl], Nat.le_refl _,
        Nat.zero_le _, trivial⟩, rfl, rfl, rfl⟩
    iapply HΦ $$ %e [Hv Hm1 HF2] Hfd
    ileft
    isplitr; · ipureintro; exact he.1
    isplitl [Hv Hm1]
    · iapply (csOwnL_intro Tok d.ino _ m.synced rfl hLs)
      iframe
    iexact HF2
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (cBytes_halvesC d.ino c 0 _).1 $$ HF with ⟨HF1, HF2⟩
    ihave Hi := (cBytes_split2 d.ino _ c 0 _).2 $$ [HF1 HD]
    · iframe
    imod Hclose $$ %(⟨m, bs, 0, 0, .idle⟩ : CSt) %Hok' [Hm2 Hi] with Hv
    · iapply (invResS_idle _ _ rfl).2
      isplitl [Hm2]
      · iexact Hm2
      iapply (invBytes_whole d.ino _ (taken_idle _ rfl) (Nat.le_refl _)).2
      iapply (cBytes_full d.ino (fun _ => DFrac.own (1 : Qp).half) (fun _ => true)
        (DFrac.own (1 : Qp).half) 0 _ fun _ _ => ⟨rfl, rfl⟩).1
      iexact Hi
    imodintro
    iapply HΦ $$ %e [Hv Hm1 HF2] Hfd
    iright
    isplitr; · ipureintro; exact ⟨he.1, he.2, hfe he.1⟩
    isplitl [Hv Hm1]
    · iapply (csOwnL_intro Tok d.ino _ m rfl Hl)
      iframe
    iexact HF2

end ops

end Perennial
