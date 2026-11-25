/-
A crash invariant of a file by its inode, with a client value beside the file's state (Lean-first,
no Rocq counterpart).

`csInv` (`CrashSt.lean`) is keyed by a path: it holds half of the claim on the name and the path's
`FileAt`. `csInvI N i γ γa γc Ok` is about the inode `i` only, so the file's name may change while
the invariant holds it (etcd renames a snapshot onto the database's path while the old database is
open and committing). It also carries a value `a : A` of the client's (bbolt's committed data,
previous data and commit phase), which the client changes with no file operation (`csInvI_setA`).
It holds one of:

* **open**: the state `s : CSt` (half of `ghostVar γ`), the value `a` (half of `ghostVar γa`), the
  invariant's part of `s` (`invResS`), `Ok a s`, and no cut in `s` (`OsMeta.cut`);
* **closed**: `csDone γc` and the whole of `ghostVar γ`, once `csInvI_close` gave the file back.

The caller's part is `csOwnI i γ γa s a`: `csOwnG` (`CrashSt.lean`) of the token `csTokI γ γa a s`
(the other halves of the two ghost variables), so the operations of `CrashStOps.lean` apply
(`CrashStIOps.lean`). The closed alternative holds all of `ghostVar γ`, so a caller with its half
of it knows the invariant is open.

`csDone γc` (`ghostVar γc 1 ()`, exclusive) is made by `csInvI_alloc` and handed to the caller;
`csInvI_close` takes it. A crash loses the caller's `csOwnI`, so `csInvI_crash_keep` asks for
`csDone γc` instead, to know the invariant is still open: the caller keeps it where a crash leaves
it (its own crash invariant), until it closes this one.

A state the invariant starts with is idle with nothing frozen, and closing needs nothing frozen
(the frozen bytes of `csInv` are discarded); `cs_freeze_g` still applies.

* `csInvI_alloc`/`csInvI_alloc_start`: from the file whole (or as a generation starts with it).
* `csInvI_setA`: a new value, of which the caller shows `Ok` of the state.
* `csInvI_close`: the file whole back, idle, for `csDone γc`.
* `csInvI_crash_keep`: what a crash left of the file, `G a` of it for a value `a` the invariant
  held (given `FileOkS Q (G a)` of each `Ok a` state), and the restart's resources with `i` taken.
* `thrBytes_whole`/`csOwnI_idle`: an idle caller's part with nothing frozen holds half of the
  `OsMeta` and of every byte, so the crash-free specs of `ReadAt` and `Stat` (any fractions) apply.
-/
module

public import Proof.os.CrashStOps

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

/-- The token of a closed `csInvI` (exclusive). -/
def csDone (γc : GName) : IProp GF := ghostVar γc (1 : Qp) ()

instance csDone_timeless (γc : GName) : Timeless (csDone (GF := GF) γc) := by
  unfold csDone; infer_instance

theorem csDone_excl (γc : GName) : ⊢ csDone (GF := GF) γc -∗ csDone γc -∗ False := by
  unfold csDone
  iintro H1 H2
  ihave %h := ghostVar_valid_2 γc () 1 () 1 $$ H1 H2
  exfalso
  have h1 := h.1
  rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
  grind

/-- The caller's token of the state `s` and value `a` of a `csInvI`: half of each ghost
variable. -/
def csTokI (γ γa : GName) (a : A) (s : CSt) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a)

/-- The caller's part of the file `i` in a `csInvI`, in the state `s` with the value `a`. -/
def csOwnI (i : Ino) (γ γa : GName) (s : CSt) (a : A) : IProp GF :=
  csOwnG (L := L) (csTokI γ γa a) i s

/-- What `csInvI` holds: open (the state, the value, the invariant's part of the state, `Ok`, no
cut) or closed (`csDone` and the whole state variable). -/
def csInvIBody (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) : IProp GF :=
  iprop((∃ (s : CSt) (a : A), ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a ∗
      invResS (L := L) (some (i, s)) ∗ ⌜Ok a s ∧ s.m.cut = none⌝) ∨
    (csDone γc ∗ ∃ s : CSt, ghostVar γ (1 : Qp) s))

instance csInvIBody_timeless (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) :
    Timeless (csInvIBody (L := L) i γ γa γc Ok) := by
  unfold csInvIBody csDone; infer_instance

/-- **The crash invariant of the file of inode `i`** (the file header): its state (`γ`) and the
client's value (`γa`), of which `Ok` holds, or closed (`γc`). -/
def csInvI (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) : IProp GF :=
  inv N (csInvIBody (L := L) i γ γa γc Ok)

instance csInvI_persistent (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) :
    Persistent (csInvI (L := L) N i γ γa γc Ok) := by unfold csInvI; infer_instance

/-- The caller's part after a truncate grew the file, in a `csInvI` (`csGrownOwnG`). -/
def csGrownOwnI (i : Ino) (γ γa : GName) (m : OsMeta) (bs : List ByteG) (fa fb sz n : Nat) (a : A) :
    IProp GF :=
  csGrownOwnG (L := L) (csTokI γ γa a) i m bs fa fb sz n

/-- Opening `csInvI` with the caller's token: it is open (the closed alternative holds all of
`ghostVar γ`), its state and value are the caller's; it closes with any of its alternatives. -/
theorem csInvI_open (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ ghostVar γ (1 : Qp).half s -∗ ghostVar γa (1 : Qp).half a
      ={E, E \ ↑N}=∗ ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a ∗
      ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a ∗ invResS (L := L) (some (i, s)) ∗
      ⌜Ok a s ∧ s.m.cut = none⌝ ∗
      (▷ csInvIBody (L := L) i γ γa γc Ok ={E \ ↑N, E}=∗ True) := by
  iintro #Hinv Hv Ha
  unfold csInvI
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  unfold csInvIBody
  icases Hi with (⟨%s', %a', Hv', Ha', Hr, %Hok⟩ | ⟨-, %s', Hv'⟩)
  · icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
    subst Heq
    icases ghostVar_agree _ _ _ _ _ $$ Ha Ha' with %Heq
    subst Heq
    imodintro
    iframe Hv Ha Hv' Ha' Hr Hclose
    ipureintro; exact Hok
  · ihave %h := ghostVar_valid_2 γ s (1 : Qp).half s' 1 $$ Hv Hv'
    exfalso
    have h1 := h.1
    rw [Qp.le_iff] at h1
    simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h1
    grind

/-- The state a generation starts the file `f` with (as `osFileStart` gives it), idle, nothing
frozen (`csStart`'s). -/
def csStartI (f : OsFile) : CSt := ⟨initMeta f, f.contents.map durB, 0, 0, .idle⟩

theorem csStart_eq (i : Ino) (f : OsFile) : csStart i f = some (i, csStartI f) := rfl

/-- **The file of inode `i`, whole and idle, in a `csInvI`**, with the value `a` (`Ok a s` of its
state, which has no cut and nothing frozen): the caller's part and the invariant's closing
token. -/
theorem csInvI_alloc (N : Namespace) (i : Ino) (Ok : A → CSt → Prop) (s : CSt) (a : A)
    (E : CoPset) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) (hwf : s.Wf) (hcut : s.m.cut = none)
    (hok : Ok a s) :
    ⊢ osMeta (L := L) i (DFrac.own 1) s.m -∗ osBytes (L := L) i 0 (DFrac.own 1) s.bs ={E}=∗
      ∃ γ γa γc, csInvI (L := L) N i γ γa γc Ok ∗ csOwnI (L := L) i γ γa s a ∗ csDone γc := by
  iintro Hm Hb
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  imod ghostVar_alloc (GF := GF) a with ⟨%γa, Ha⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γc, Hd⟩
  icases (ghostVar_split_half (A := CSt) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (ghostVar_split_half (A := A) γa 1 _).1 $$ Ha with ⟨Ha1, Ha2⟩
  icases csStartRes_split (L := L) (some (i, s)) (fun _ _ h => by cases h; exact ⟨hb, hf⟩)
    $$ [Hm Hb] with ⟨Hi, Hth⟩
  · dsimp only [csStartRes]; iframe
  imod inv_alloc N E (csInvIBody (L := L) i γ γa γc Ok) $$ [Hv1 Ha1 Hi] with #Hinv
  · inext; unfold csInvIBody; ileft; iexists s, a; iframe; ipureintro; exact ⟨hok, hcut⟩
  imodintro
  iexists γ, γa, γc
  unfold csInvI csOwnI csOwnG csTokI
  iframe Hinv Hv2 Ha2 Hth
  isplitr
  · ipureintro; exact hwf
  unfold csDone; iexact Hd

/-- `csInvI_alloc` for the file `f` as a generation starts with it (`osFileStart`). -/
theorem csInvI_alloc_start (N : Namespace) (i : Ino) (Ok : A → CSt → Prop) (f : OsFile) (a : A)
    (E : CoPset) (hok : Ok a (csStartI f)) :
    ⊢ osFileStart (L := L) i f ={E}=∗
      ∃ γ γa γc, csInvI (L := L) N i γ γa γc Ok ∗ csOwnI (L := L) i γ γa (csStartI f) a ∗
        csDone γc := by
  show ⊢ osMeta (L := L) i (DFrac.own 1) (csStartI f).m ∗
    osBytes (L := L) i 0 (DFrac.own 1) (csStartI f).bs ={E}=∗ _
  iintro ⟨Hm, Hb⟩
  iapply csInvI_alloc N i Ok (csStartI f) a E rfl (Nat.le_refl _) (csStart_wf i f)
    (csStart_cut i f) hok $$ Hm Hb

/-- **A new value** `a'` of a `csInvI`, of which the caller shows `Ok` of its state: no file
operation. -/
theorem csInvI_setA (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a a' : A) (E : CoPset) (hE : ↑N ⊆ E) (hok : Ok a' s) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ csOwnI (L := L) i γ γa s a ={E}=∗
      csOwnI (L := L) i γ γa s a' := by
  unfold csOwnI csOwnG csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Ht, %Hwf⟩
  imod csInvI_open N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, %Hok, Hclose⟩
  imod ghostVar_update_halves a' γa _ _ $$ Ha Ha' with ⟨Ha, Ha'⟩
  imod Hclose $$ [Hv' Ha' Hr] with -
  · inext; unfold csInvIBody; ileft; iexists s, a'; iframe; ipureintro; exact ⟨hok, Hok.2⟩
  imodintro
  iframe
  ipureintro; exact Hwf

/-- **Closing a `csInvI`**: the caller's part of an idle state with nothing frozen, and the closing
token, give the file whole back; the invariant is closed from then on. -/
theorem csInvI_close (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ csOwnI (L := L) i γ γa s a -∗ csDone γc ={E}=∗
      osMeta (L := L) i (DFrac.own 1) s.m ∗ osBytes (L := L) i 0 (DFrac.own 1) s.bs := by
  iintro #Hinv Hown Hd
  unfold csOwnI
  icases (csOwnG_idle (L := L) (csTokI γ γa a) i s hb).1 $$ Hown with ⟨Ht, ⟨Hm1, Hb1⟩, -⟩
  unfold csTokI
  icases Ht with ⟨Hv, Ha⟩
  imod csInvI_open N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, -, Hv', -, Hr, -, Hclose⟩
  icases (invResS_idle _ _ hb).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hv := (ghostVar_split_half (A := CSt) γ 1 s).2 $$ [Hv Hv']
  · iframe
  imod Hclose $$ [Hd Hv] with -
  · inext; unfold csInvIBody; iright; isplitl [Hd]
    · iexact Hd
    iexists s; iexact Hv
  imodintro
  isplitl [Hm1 Hm2]
  · iapply (osMeta_halves _ _).2; iframe
  iapply (idleBytes_whole i s hb hf).2; iframe

/-- An idle state's bytes the caller holds, nothing frozen: half of each. -/
theorem thrBytes_whole (p : Ino) (s : CSt) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) :
    thrBytes (L := L) p s ⊣⊢ osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) s.bs := by
  have hfr : ∀ k, s.frozen k = false := fun k => by simp only [CSt.frozen]; simp; omega
  have hta : ∀ k, s.taken k = false := fun k => by simp [CSt.taken, hb]
  unfold thrBytes
  exact cBytes_full p _ _ _ 0 s.bs fun k _ => ⟨by simp [hfr, hta], rfl⟩

/-- **The caller's part of an idle state with nothing frozen**: its token, half of the `OsMeta` and
half of every byte (which the crash-free specs of `ReadAt` and `Stat` take at any fraction). -/
theorem csOwnI_idle (i : Ino) (γ γa : GName) (s : CSt) (a : A) (hb : s.busy = .idle)
    (hf : s.fb ≤ s.fa) :
    csOwnI (L := L) i γ γa s a ⊣⊢ csTokI γ γa a s ∗
      (osMeta (L := L) i (DFrac.own (1 : Qp).half) s.m ∗
        osBytes (L := L) i 0 (DFrac.own (1 : Qp).half) s.bs) ∗ ⌜s.Wf⌝ := by
  unfold csOwnI
  refine (csOwnG_idle _ _ _ hb).trans (sep_congr .rfl (sep_congr (sep_congr .rfl ?_) .rfl))
  exact thrBytes_whole i s hb hf

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]
variable {A : Type} [Pos.Countable A]

/-- **The file after a crash under the premise `Q`**, from the old generation's `csInvI` (open: the
caller's `csDone γc` says so): what the crash left of the file of inode `i` (`metaRes_take`), for
a value `a` the invariant held with some state `s` (`Ok a s`; the file's size one `s` allows,
`CSt.CrashSize`: one of the crash sizes its `OsMeta` knows), which is `G a` if the file is there
(by `FileOkS Q (G a)` of each `Ok a` state), and there if the new tree names `i`; the restart's
resources with `i` taken. The invariant is closed again as it was. -/
theorem csInvI_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (Gd : A → Option OsFile → Prop) (E : CoPset) (hE : ↑N ⊆ E) (hi : i ∉ D)
    (hok : ∀ a s, Ok a s → FileOkS Q (Gd a) i s) :
    ⊢ csInvI (L := L) N i γ γa γc Ok -∗ csDone (GF := GF) γc -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ={E}=∗
      ∃ (a : A) (fo : Option OsFile),
        ⌜(∃ s, Ok a s ∧ ∀ f, fo = some f → s.CrashSize f.size) ∧ (Named V'.now i → fo.isSome) ∧
          ∀ f, fo = some f → Gd a (some f)⌝ ∗
        osFileStartO (L := L') i fo ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (i :: D) tt V' ∗ csDone γc := by
  iintro #Hinv Hd Hr
  unfold csInvI
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  unfold csInvIBody
  icases Hi with (⟨%s, %a, Hv, Ha, Hs, %Hok⟩ | ⟨Hd', -⟩)
  · dsimp only [invResS]
    icases Hs with ⟨Hm, Hb⟩
    icases (invBytes_runs (L := L) i s).1 $$ Hb with Hb
    icases metaRes_take Q L L' D tt V' i hi s $$ Hr Hm Hb with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
    ihave Hb := (invBytes_runs (L := L) i s).2 $$ Hb
    obtain ⟨hfc, hnm, hseen⟩ := hfo
    imod Hclose $$ [Hv Ha Hm Hb] with -
    · inext; ileft; iexists s, a; iframe; ipureintro; exact Hok
    imodintro
    iexists a, fo
    iframe Hf Hr Hd
    ipureintro
    exact ⟨⟨s, Hok.1, crashSeen_crashSize hseen⟩, hnm,
      fun f hf => by subst hf; exact hok a s Hok.1 Hok.2 f hfc hseen⟩
  · iexfalso
    iapply csDone_excl γc $$ Hd Hd'

end crash

end Perennial
