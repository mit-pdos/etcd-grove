/-
**The inode-keyed crash invariant with a client resource** (Lean-first, no Rocq counterpart):
`csInvIR N i γ γa γc Ok R` is `csInvI` (`CrashStI.lean`) whose open alternative also holds `R a`,
a resource of the client's at the invariant's value `a`. `Ok` is pure, so `csInvI` cannot tie its
value to the client's ghost state; `R` can (bbolt: the half of a version variable whose other half
is in the committed data, `Proof/go_etcd_io/bbolt/Inv/BFileR.lean`). `csInvI` is the case
`R := fun _ => emp` (`csInvI_R`).

* `csInvIR_open`: the invariant open with the caller's token, `R a` included.
* `csInvIR_alloc_c`: `csInvI_alloc_c` with `R a`.
* `csOwnILR_ok`, `csOwnILR_agree`: `csOwnIL_ok`/`_agree` (the value unchanged, `R a` put back).
* `csOwnILR_upd`: a new value `a'`, the caller turning `R a` into `R a'` (any update inside the
  invariant's mask: bbolt's commit point fires its client's update there).
* `csI_accR`, `csI_accAR`: the accessors (`CsAcc`) of `csI_acc`/`csI_accA`; the latter for an `R` that
  survives the value's move (`R (av s) ⊢ R (av s')`).
* `csInvIR_close`: the file whole back and `R a`.
* `csInvIR_crash_keep`: `csInvI_crash_keep` from any fraction of the closing name (not all of it:
  the client keeps it where it wants), with what the caller reads off `R a` (`Y a`).
-/
module

public import Proof.os.CrashStILA

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

/-- What `csInvIR` holds: `csInvIBody`'s alternatives, the open one with `R a`. -/
def csInvIBodyR (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) : IProp GF :=
  iprop((∃ (s : CSt) (a : A), ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a ∗
      invResS (L := L) (some (i, s)) ∗ R a ∗ ⌜Ok a s ∧ s.m.cut = none⌝) ∨
    (csDone γc ∗ ∃ s : CSt, ghostVar γ (1 : Qp) s))

instance csInvIBodyR_timeless (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (R : A → IProp GF) [∀ a, Timeless (R a)] :
    Timeless (csInvIBodyR (L := L) i γ γa γc Ok R) := by
  unfold csInvIBodyR csDone; infer_instance

/-- **The crash invariant of the file of inode `i`, with the client resource `R`** (see the file
header). -/
def csInvIR (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) :
    IProp GF :=
  inv N (csInvIBodyR (L := L) i γ γa γc Ok R)

instance csInvIR_persistent (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (R : A → IProp GF) : Persistent (csInvIR (L := L) N i γ γa γc Ok R) := by
  unfold csInvIR; infer_instance

/-- **`csInvI` is `csInvIR` with no client resource.** -/
theorem csInvI_R (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) :
    csInvI (L := L) N i γ γa γc Ok ⊢ csInvIR (L := L) N i γ γa γc Ok (fun _ => iprop(emp)) := by
  unfold csInvI csInvIR
  iintro #Hinv
  iapply inv_iff $$ Hinv
  inext; imodintro
  unfold csInvIBody csInvIBodyR
  isplit
  · iintro (⟨%s, %a, Hv, Ha, Hr, %Hok⟩ | ⟨Hd, %s, Hv⟩)
    · ileft; iexists s, a; iframe; ipureintro; exact ⟨trivial, Hok⟩
    · iright; iframe
  · iintro (⟨%s, %a, Hv, Ha, Hr, -, %Hok⟩ | ⟨Hd, %s, Hv⟩)
    · ileft; iexists s, a; iframe; ipureintro; exact Hok
    · iright; iframe

variable (R : A → IProp GF) [hRt : ∀ a, Timeless (R a)]

/-- Opening `csInvIR` with the caller's token (`csInvI_open`, with `R a`). -/
theorem csInvIR_open (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ csInvIR (L := L) N i γ γa γc Ok R -∗ ghostVar γ (1 : Qp).half s -∗ ghostVar γa (1 : Qp).half a
      ={E, E \ ↑N}=∗ ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a ∗
      ghostVar γ (1 : Qp).half s ∗ ghostVar γa (1 : Qp).half a ∗ invResS (L := L) (some (i, s)) ∗
      R a ∗ ⌜Ok a s ∧ s.m.cut = none⌝ ∗
      (▷ csInvIBodyR (L := L) i γ γa γc Ok R ={E \ ↑N, E}=∗ True) := by
  iintro #Hinv Hv Ha
  unfold csInvIR
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  unfold csInvIBodyR
  icases Hi with (⟨%s', %a', Hv', Ha', Hr, HR, %Hok⟩ | ⟨-, %s', Hv'⟩)
  · icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
    subst Heq
    icases ghostVar_agree _ _ _ _ _ $$ Ha Ha' with %Heq
    subst Heq
    imodintro
    iframe Hv Ha Hv' Ha' Hr HR Hclose
    ipureintro; exact Hok
  · ihave %h := ghostVar_valid_2 γ s (1 : Qp).half s' 1 $$ Hv Hv'
    exfalso
    have h1 := h.1
    rw [Qp.le_iff] at h1
    simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h1
    grind

/-- **A file whole and idle in a `csInvIR` whose closing name `γc` the caller has**, with `R a`
(`csInvI_alloc_c`). -/
theorem csInvIR_alloc_c (N : Namespace) (i : Ino) (γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) (hwf : s.Wf)
    (hcut : s.m.cut = none) (hok : Ok a s) :
    ⊢ osMeta (L := L) i (DFrac.own 1) s.m -∗ osBytes (L := L) i 0 (DFrac.own 1) s.bs -∗ R a ={E}=∗
      ∃ γ γa, csInvIR (L := L) N i γ γa γc Ok R ∗ csOwnI (L := L) i γ γa s a := by
  iintro Hm Hb HR
  imod ghostVar_alloc (GF := GF) s with ⟨%γ, Hv⟩
  imod ghostVar_alloc (GF := GF) a with ⟨%γa, Ha⟩
  icases (ghostVar_split_half (A := CSt) γ 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (ghostVar_split_half (A := A) γa 1 _).1 $$ Ha with ⟨Ha1, Ha2⟩
  icases csStartRes_split (L := L) (some (i, s)) (fun _ _ h => by cases h; exact ⟨hb, hf⟩)
    $$ [Hm Hb] with ⟨Hi, Hth⟩
  · dsimp only [csStartRes]; iframe
  imod inv_alloc N E (csInvIBodyR (L := L) i γ γa γc Ok R) $$ [Hv1 Ha1 Hi HR] with #Hinv
  · inext; unfold csInvIBodyR; ileft; iexists s, a; iframe; ipureintro; exact ⟨hok, hcut⟩
  imodintro
  iexists γ, γa
  unfold csInvIR csOwnI csOwnG csTokI
  iframe Hinv Hv2 Ha2 Hth
  ipureintro; exact hwf

/-- **`Ok` of the caller's state** (`csOwnIL_ok`). -/
theorem csOwnILR_ok (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ csInvIR (L := L) N i γ γa γc Ok R -∗ csOwnIL (L := L) i γ γa s a ={E}=∗
      csOwnIL (L := L) i γ γa s a ∗ ⌜Ok a s ∧ s.m.cut = none⌝ := by
  unfold csOwnIL csOwnL csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Hm, %Hl⟩
  imod csInvIR_open R N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, HR, %Hok, Hclose⟩
  imod Hclose $$ [Hv' Ha' Hr HR] with -
  · inext; unfold csInvIBodyR; ileft; iexists s, a; iframe; ipureintro; exact Hok
  imodintro
  iframe
  ipureintro; exact ⟨Hl, Hok⟩

/-- **The caller's bytes are the state's** (`csOwnIL_agree`). -/
theorem csOwnILR_agree (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) (off : Nat) (dq : DFrac) (xs : List ByteG)
    (hl : off + xs.length ≤ s.bs.length) :
    ⊢ csInvIR (L := L) N i γ γa γc Ok R -∗ csOwnIL (L := L) i γ γa s a -∗
      osBytes (L := L) i off dq xs ={E}=∗
      csOwnIL (L := L) i γ γa s a ∗ osBytes (L := L) i off dq xs ∗
        ⌜xs = (s.bs.drop off).take xs.length⌝ := by
  unfold csOwnIL csOwnL csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Hm, %Hl⟩ Hx
  obtain ⟨hwf0, hb, hfa, hfb⟩ := Hl
  imod csInvIR_open R N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, HR, %Hok, Hclose⟩
  icases (invResS_idle _ _ hb).1 $$ Hr with ⟨Hm2, Hb2⟩
  icases (invBytes_whole i s (taken_idle s hb) (by omega)).1 $$ Hb2 with Hb2
  icases (osBytes_around i _ s.bs off xs.length hl).1 $$ Hb2 with ⟨H1, H2, H3⟩
  icases osBytes_agreeL i xs ((s.bs.drop off).take xs.length) off dq _
    (by simp only [List.length_take, List.length_drop]; omega) $$ [Hx H2] with ⟨Hx, H2, %he⟩
  · iframe
  ihave Hb2 := (osBytes_around i _ s.bs off xs.length hl).2 $$ [H1 H2 H3]
  · iframe
  ihave Hb2 := (invBytes_whole i s (taken_idle s hb) (by omega)).2 $$ Hb2
  imod Hclose $$ [Hv' Ha' Hm2 Hb2 HR] with -
  · inext; unfold csInvIBodyR; ileft; iexists s, a; iframe
    isplitl
    · iapply (invResS_idle _ _ hb).2; iframe
    ipureintro; exact Hok
  imodintro
  iframe
  ipureintro; exact ⟨⟨hwf0, hb, hfa, hfb⟩, he⟩

/-- **A new value `a'`**, the caller turning `R a` into `R a'` and `Q` inside the invariant's mask
(with `Ok a s` in hand), and showing `Ok a' s`. -/
theorem csOwnILR_upd (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a a' : A) (E : CoPset) (hE : ↑N ⊆ E) (hok : Ok a s → Ok a' s) (Q : IProp GF) :
    ⊢ csInvIR (L := L) N i γ γa γc Ok R -∗ csOwnIL (L := L) i γ γa s a -∗
      (R a ={E \ ↑N}=∗ R a' ∗ Q) ={E}=∗
      csOwnIL (L := L) i γ γa s a' ∗ Q := by
  unfold csOwnIL csOwnL csTokI
  iintro #Hinv ⟨⟨Hv, Ha⟩, Hm, %Hl⟩ Hu
  imod csInvIR_open R N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, HR, %Hok, Hclose⟩
  imod Hu $$ HR with ⟨HR, HQ⟩
  imod ghostVar_update_halves a' γa _ _ $$ Ha Ha' with ⟨Ha, Ha'⟩
  imod Hclose $$ [Hv' Ha' Hr HR] with -
  · inext; unfold csInvIBodyR; ileft; iexists s, a'; iframe; ipureintro
    exact ⟨hok Hok.1, Hok.2⟩
  imodintro
  iframe
  ipureintro; exact Hl

/-- **`csInvIR`'s accessor**, the caller's value being `a` (`csI_acc`). -/
theorem csI_accR (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (a : A) :
    CsAcc (L := L) N (csInvIR (L := L) N i γ γa γc Ok R) (csTokI γ γa a) (Ok a) i := by
  unfold CsAcc csTokI
  intro E s hE
  iintro #Hinv ⟨Hv, Ha⟩
  imod csInvIR_open R N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, HR, %Hok, Hclose⟩
  imodintro
  iframe Hr
  isplitr
  · ipureintro; exact Hok
  iintro %s' %hs' Hr'
  imod ghostVar_update_halves s' γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ha' Hr' HR] with -
  · inext; unfold csInvIBodyR; ileft; iexists s', a; iframe; ipureintro; exact hs'
  imodintro; iframe

/-- **`csInvIR`'s accessor, the value following the state** (`csI_accA`), for an `R` that survives
the move. -/
theorem csI_accAR (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (av : CSt → A) (hR : ∀ s s', R (av s) ⊢ R (av s')) :
    CsAcc (L := L) N (csInvIR (L := L) N i γ γa γc Ok R) (fun s => csTokI γ γa (av s) s)
      (fun s => Ok (av s) s) i := by
  unfold CsAcc
  intro E s hE
  unfold csTokI
  iintro #Hinv ⟨Hv, Ha⟩
  imod csInvIR_open R N i γ γa γc Ok s (av s) E hE $$ Hinv Hv Ha
    with ⟨Hv, Ha, Hv', Ha', Hr, HR, %Hok, Hclose⟩
  imodintro
  iframe Hr
  isplitr
  · ipureintro; exact Hok
  iintro %s' %hs' Hr'
  imod ghostVar_update_halves s' γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod ghostVar_update_halves (av s') γa _ _ $$ Ha Ha' with ⟨Ha, Ha'⟩
  ihave HR := hR s s' $$ HR
  imod Hclose $$ [Hv' Ha' Hr' HR] with -
  · inext; unfold csInvIBodyR; ileft; iexists s', av s'; iframe; ipureintro; exact hs'
  imodintro
  dsimp only
  iframe

/-- **Closing a `csInvIR`** (`csInvI_close`): the file whole back, and `R a`. -/
theorem csInvIR_close (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (s : CSt)
    (a : A) (E : CoPset) (hE : ↑N ⊆ E) (hb : s.busy = .idle) (hf : s.fb ≤ s.fa) :
    ⊢ csInvIR (L := L) N i γ γa γc Ok R -∗ csOwnI (L := L) i γ γa s a -∗ csDone γc ={E}=∗
      osMeta (L := L) i (DFrac.own 1) s.m ∗ osBytes (L := L) i 0 (DFrac.own 1) s.bs ∗ R a := by
  iintro #Hinv Hown Hd
  unfold csOwnI
  icases (csOwnG_idle (L := L) (csTokI γ γa a) i s hb).1 $$ Hown with ⟨Ht, ⟨Hm1, Hb1⟩, -⟩
  unfold csTokI
  icases Ht with ⟨Hv, Ha⟩
  imod csInvIR_open R N i γ γa γc Ok s a E hE $$ Hinv Hv Ha
    with ⟨Hv, -, Hv', -, Hr, HR, -, Hclose⟩
  icases (invResS_idle _ _ hb).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hv := (ghostVar_split_half (A := CSt) γ 1 s).2 $$ [Hv Hv']
  · iframe
  imod Hclose $$ [Hd Hv] with -
  · inext; unfold csInvIBodyR; iright; isplitl [Hd]
    · iexact Hd
    iexists s; iexact Hv
  imodintro
  iframe HR
  isplitl [Hm1 Hm2]
  · iapply (osMeta_halves _ _).2; iframe
  iapply (idleBytes_whole i s hb hf).2; iframe

end res

/-! ## After a crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]
variable {A : Type} [Pos.Countable A]

/-- `csDone` excludes any fraction of the closing name. -/
theorem csDone_frac (γc : GName) (q : Qp) : ⊢ csDone (GF := GF) γc -∗ ghostVar γc q () -∗ False := by
  unfold csDone
  iintro H1 H2
  ihave %h := ghostVar_valid_2 γc () 1 () q $$ H1 H2
  exfalso
  have h1 := h.1
  rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
  have := q.2
  grind

/-- **The file after a crash, from a `csInvIR`** (`csInvI_crash_keep`): the invariant known open
from a fraction `q` of its closing name (the closed alternative holds all of it), and what the
caller reads off the client resource of the value it reports (`Y a`, with the caller's `X`). -/
theorem csInvIR_crash_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop)
    (R : A → IProp GF) [∀ a, Timeless (R a)]
    (Gd : A → Option OsFile → Prop) (E : CoPset) (hE : ↑N ⊆ E) (hi : i ∉ D)
    (hok : ∀ a s, Ok a s → FileOkS Q (Gd a) i s) (q : Qp) (X : IProp GF) (Y : A → IProp GF) :
    ⊢ csInvIR (L := L) N i γ γa γc Ok R -∗ ghostVar (GF := GF) γc q () -∗ X -∗
      (∀ a, R a -∗ X -∗ R a ∗ Y a) -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ={E}=∗
      ∃ (a : A) (fo : Option OsFile),
        ⌜(∃ s, Ok a s ∧ ∀ f, fo = some f → s.CrashSize f.size) ∧ (Named V'.now i → fo.isSome) ∧
          ∀ f, fo = some f → Gd a (some f)⌝ ∗ Y a ∗
        osFileStartO (L := L') i fo ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (i :: D) tt V' := by
  iintro #Hinv Hq HX HY Hr
  unfold csInvIR
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  unfold csInvIBodyR
  icases Hi with (⟨%s, %a, Hv, Ha, Hs, HR, %Hok⟩ | ⟨Hd', -⟩)
  · ihave ⟨HR, HYa⟩ := HY $$ %a HR HX
    dsimp only [invResS]
    icases Hs with ⟨Hm, Hb⟩
    icases (invBytes_runs (L := L) i s).1 $$ Hb with Hb
    icases metaRes_take Q L L' D tt V' i hi s $$ Hr Hm Hb with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
    ihave Hb := (invBytes_runs (L := L) i s).2 $$ Hb
    obtain ⟨hfc, hnm, hseen⟩ := hfo
    imod Hclose $$ [Hv Ha Hm Hb HR] with -
    · inext; ileft; iexists s, a; iframe; ipureintro; exact Hok
    imodintro
    iexists a, fo
    iframe Hf Hr HYa
    ipureintro
    exact ⟨⟨s, Hok.1, crashSeen_crashSize hseen⟩, hnm,
      fun f hf => by subst hf; exact hok a s Hok.1 Hok.2 f hfc hseen⟩
  · iexfalso
    iapply csDone_frac γc q $$ Hd' Hq

end crash

end Perennial
