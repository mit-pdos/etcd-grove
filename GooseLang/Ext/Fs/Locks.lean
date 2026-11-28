/-
WP specs of the Linux file extension's lock calls (`OfdLock`, `Flock`: the lock rule `LockStep`,
`Impl.lean`) and of `close` (which releases the description's locks), over the locks' ghost state
(`lockCtx`, `Ghost.lean`). Untrusted. Design: `notes/wal-units/locks.md`.

**Resources**: `osLock k i fd`, an exclusive lock of kind `k` (OFD or `flock`) on the file `i`, held
through the fd `fd`; whole, and exclusive (`osLock_excl`: two for one file and kind are a
contradiction), so a successful exclusive lock proves that no other description holds one.
`lockTok k fd d`: the token of the description `d`'s exclusive lock of kind `k`, if it has one (`emp`
otherwise); `lockToks fd d`: both kinds' (`emp` for an unlocked description: every `open` gives one,
`lockToks_unlocked`).
-/
module

public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-! ## Pure facts -/

theorem setFd_fds (st : OsState) (fd : w64) (d : OsFd) (fd' : w64) :
    (st.setFd fd d).proc.fds !! fd' = if fd = fd' then some d else st.proc.fds !! fd' := by
  show (<[fd := d]> st.proc.fds) !! fd' = _
  split
  · subst_vars; exact GMap.lookup_insert _ _ _
  · exact GMap.lookup_insert_ne _ _ ‹_›

theorem setLk_lk (d : OsFd) (k k' : LockKind) (x : Option Bool) :
    (d.setLk k x).lk k' = if k' = k then x else d.lk k' := by
  cases k <;> cases k' <;> rfl

theorem setLk_setLk_ne (d : OsFd) {k k' : LockKind} (x : Option Bool) (h : k' ≠ k) :
    (d.setLk k x).lk k' = d.lk k' := by
  rw [setLk_lk, if_neg h]

/-- A lock through `fd` (to `x`) keeps `LockWf`, when a lock (`x = some ex`) has no conflict. -/
theorem lockWf_setLk {st : OsState} {fd : w64} {d : OsFd} {k : LockKind} {x : Option Bool}
    (hwf : LockWf st) (hd : st.proc.fds !! fd = some d)
    (hok : ∀ ex, x = some ex → ¬ LockConflict st k fd d.ino ex) :
    LockWf (st.setFd fd (d.setLk k x)) := by
  intro k' fd1 d1 fd2 d2 h1 h2 hne hino hk
  rw [setFd_fds] at h1 h2
  by_cases e1 : fd = fd1
  · subst e1
    rw [if_pos rfl] at h1; cases h1
    rw [if_neg hne] at h2
    rw [setLk_ino] at hino
    rw [setLk_lk] at hk
    by_cases ek : k' = k
    · subst ek; rw [if_pos rfl] at hk; subst hk
      cases h : d2.lk k' with
      | none => rfl
      | some y => exact absurd (.inl ⟨fd2, d2, h2, Ne.symm hne, hino.symm, y, h, .inl rfl⟩) (hok true rfl)
    · rw [if_neg ek] at hk
      exact hwf k' fd d fd2 d2 hd h2 hne hino hk
  · rw [if_neg e1] at h1
    by_cases e2 : fd = fd2
    · subst e2
      rw [if_pos rfl] at h2; cases h2
      rw [setLk_ino] at hino
      rw [setLk_lk]
      by_cases ek : k' = k
      · subst ek; rw [if_pos rfl]
        cases hx : x with
        | none => rfl
        | some ex =>
          exact absurd (.inl ⟨fd1, d1, h1, fun h => e1 h.symm, hino, true, hk, .inr rfl⟩) (hok ex hx)
      · rw [if_neg ek]; exact hwf k' fd1 d1 fd d h1 hd (fun h => e1 h.symm) hino hk
    · rw [if_neg e2] at h2; exact hwf k' fd1 d1 fd2 d2 h1 h2 hne hino hk

/-- The exclusive locks' map after a lock call through `fd` (description `d`) sets its lock of kind
`k` to `x`: the entry of `(k, d.ino)` is `fd` if the lock is now exclusive, gone if it was. -/
def lockMapSet (Λ : GMap (LockKind × Ino) w64) (k : LockKind) (fd : w64) (d : OsFd)
    (x : Option Bool) : GMap (LockKind × Ino) w64 :=
  if x = some true then <[(k, d.ino) := fd]> Λ
  else if d.lk k = some true then GMap.delete (k, d.ino) Λ else Λ

theorem lockCoh_setLk {st : OsState} {Λ : GMap (LockKind × Ino) w64} {fd : w64} {d : OsFd}
    {k : LockKind} {x : Option Bool} (hwf : LockWf st) (hcoh : LockCoh st Λ)
    (hd : st.proc.fds !! fd = some d)
    (hok : ∀ ex, x = some ex → d.lk k = none ∧ ¬ LockConflict st k fd d.ino ex) :
    LockCoh (st.setFd fd (d.setLk k x)) (lockMapSet Λ k fd d x) := by
  intro k' i fd'
  -- the holders after the call
  have hR : (∃ d', (st.setFd fd (d.setLk k x)).proc.fds !! fd' = some d' ∧ d'.ino = i ∧
      d'.lk k' = some true) ↔
      (if fd = fd' then d.ino = i ∧ (if k' = k then x else d.lk k') = some true
       else ∃ d', st.proc.fds !! fd' = some d' ∧ d'.ino = i ∧ d'.lk k' = some true) := by
    rw [setFd_fds]
    split
    · constructor
      · rintro ⟨d', h, h1, h2⟩; cases h; rw [setLk_ino] at h1; rw [setLk_lk] at h2; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨_, rfl, by rw [setLk_ino]; exact h1, by rw [setLk_lk]; exact h2⟩
    · exact Iff.rfl
  rw [hR]
  have hc := hcoh k' i fd'
  by_cases hp : (k', i) = (k, d.ino)
  · simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    unfold lockMapSet
    by_cases hx : x = some true
    · rw [if_pos hx, GMap.lookup_insert]
      subst hx
      obtain ⟨-, hnc⟩ := hok true rfl
      split
      · subst_vars; simp
      · constructor
        · intro h; cases h; contradiction
        · rintro ⟨d', h1, h2, h3⟩
          exact absurd (.inl ⟨fd', d', h1, fun h => ‹¬ fd = fd'› h.symm, h2, true, h3, .inl rfl⟩) hnc
    · rw [if_neg hx]
      by_cases hl : d.lk k' = some true
      · rw [if_pos hl, GMap.lookup_delete_iff]
        simp only [if_true, ite_true]
        split
        · simp only [true_and, hx]; simp
        · constructor
          · intro h; simp at h
          · rintro ⟨d', h1, h2, h3⟩
            exact absurd (hwf k' fd d fd' d' hd h1 ‹¬ fd = fd'› h2.symm hl) (by rw [h3]; simp)
      · rw [if_neg hl, hc]
        split
        · subst_vars
          simp only [true_and, if_true, hx, iff_false]
          rintro ⟨d', h1, -, h3⟩; rw [hd] at h1; cases h1; exact hl h3
        · exact Iff.rfl
  · have hm : (lockMapSet Λ k fd d x) !! (k', i) = Λ !! (k', i) := by
      unfold lockMapSet
      split
      · exact GMap.lookup_insert_ne _ _ (Ne.symm hp)
      · split
        · rw [GMap.lookup_delete_iff, if_neg (Ne.symm hp)]
        · rfl
    rw [hm, hc]
    split
    · subst_vars
      constructor
      · rintro ⟨d', h1, h2, h3⟩
        rw [hd] at h1; cases h1
        refine ⟨h2, ?_⟩
        split
        · subst_vars; exact absurd rfl hp
        · exact h3
      · rintro ⟨h2, h3⟩
        refine ⟨d, hd, h2, ?_⟩
        split at h3
        · subst_vars; exact absurd rfl hp
        · exact h3
    · exact Iff.rfl

/-- `st` with the fd `fd` closed. -/
abbrev OsState.delFd (st : OsState) (fd : w64) : OsState :=
  st.setProc { st.proc with fds := GMap.delete fd st.proc.fds }

section ghost
variable {GF : BundledGFunctors}

/-- **The locks' interpretation across a lock call** through `fd` that sets the description's lock
of kind `k` to `x` (a lock, `x = some ex`, only with no lock of the kind before and no conflict): the
token of the old exclusive lock (if any) goes in, that of the new one (if any) comes out. -/
theorem lockCtx_setLk (hL : OsGS GF) {st : OsState} {fd : w64} {d : OsFd} {k : LockKind}
    {x : Option Bool} (hd : st.proc.fds !! fd = some d)
    (hok : ∀ ex, x = some ex → d.lk k = none ∧ ¬ LockConflict st k fd d.ino ex) :
    lockCtx hL st ∗ (if d.lk k = some true then gElem hL hL.γlk (k, d.ino) (DFrac.own 1) fd
      else emp) ⊢ |==> (lockCtx hL (st.setFd fd (d.setLk k x)) ∗
      (if x = some true then gElem hL hL.γlk (k, d.ino) (DFrac.own 1) fd else emp)) := by
  unfold lockCtx
  iintro ⟨⟨%Λ, %hw, Ha⟩, Ht⟩
  obtain ⟨hwf, hcoh⟩ := hw
  have hwf' := lockWf_setLk (x := x) hwf hd (fun ex hx => (hok ex hx).2)
  have hcoh' := lockCoh_setLk hwf hcoh hd hok
  by_cases hx : x = some true
  · obtain ⟨hnone, hnc⟩ := hok true hx
    rw [if_neg (by rw [hnone]; simp), if_pos hx]
    have hfree : Λ !! (k, d.ino) = none := by
      cases hq : Λ !! (k, d.ino) with
      | none => rfl
      | some fd' =>
        obtain ⟨d', h1, h2, h3⟩ := (hcoh k d.ino fd').1 hq
        have hne : fd' ≠ fd := fun h => by subst h; rw [hd] at h1; cases h1; rw [hnone] at h3; cases h3
        exact absurd (.inl ⟨fd', d', h1, hne, h2, true, h3, .inl rfl⟩) hnc
    imod gAuth_insert hL _ _ _ fd hfree $$ Ha with ⟨Ha, Hk⟩
    imodintro
    iframe Hk
    iexists (lockMapSet Λ k fd d x)
    unfold lockMapSet
    rw [if_pos hx]
    iframe Ha
    ipureintro; exact ⟨hwf', by have := hcoh'; unfold lockMapSet at this; rwa [if_pos hx] at this⟩
  · rw [if_neg hx]
    by_cases hl : d.lk k = some true
    · rw [if_pos hl]
      imod gAuth_delete hL _ _ _ _ $$ Ha Ht with Ha
      imodintro
      isplitl [Ha]
      · iexists (lockMapSet Λ k fd d x)
        unfold lockMapSet
        rw [if_neg hx, if_pos hl]
        iframe Ha
        ipureintro; exact ⟨hwf', by have := hcoh'; unfold lockMapSet at this; rwa [if_neg hx, if_pos hl] at this⟩
      · iempintro
    · rw [if_neg hl]
      imodintro
      isplitl [Ha]
      · iexists Λ
        iframe Ha
        ipureintro; exact ⟨hwf', by have := hcoh'; unfold lockMapSet at this; rwa [if_neg hx, if_neg hl] at this⟩
      · iempintro

/-- The locks' interpretation across `close(fd)`: the description's tokens go in. -/
theorem lockCtx_close (hL : OsGS GF) {st : OsState} {fd : w64} {d : OsFd}
    (hd : st.proc.fds !! fd = some d) :
    lockCtx hL st ∗ ((if d.lk LockKind.ofd = some true then
        gElem hL hL.γlk (LockKind.ofd, d.ino) (DFrac.own 1) fd else emp) ∗
      (if d.lk LockKind.flock = some true then
        gElem hL hL.γlk (LockKind.flock, d.ino) (DFrac.own 1) fd else emp))
    ⊢ |==> lockCtx hL (st.delFd fd) := by
  iintro ⟨Hlk, Ho, Hf⟩
  imod lockCtx_setLk (x := none) hL hd (fun _ h => by cases h) $$ [Hlk Ho] with ⟨Hlk, -⟩
  · iframe
  have hd1 : (st.setFd fd (d.setLk .ofd none)).proc.fds !! fd = some (d.setLk .ofd none) := by
    rw [setFd_fds, if_pos rfl]
  rw [show d.lk .flock = (d.setLk .ofd none).lk .flock from (setLk_setLk_ne d none (by decide)).symm,
    show d.ino = (d.setLk .ofd none).ino from (setLk_ino _ _ _).symm]
  imod lockCtx_setLk (x := none) hL hd1 (fun _ h => by cases h) $$ [Hlk Hf] with ⟨Hlk, -⟩
  · iframe
  have hfr : LockFrame ((st.setFd fd (d.setLk LockKind.ofd none)).setFd fd
      ((d.setLk LockKind.ofd none).setLk LockKind.flock none)) (st.delFd fd) := by
    intro fd'
    have e3 : (st.delFd fd).proc.fds !! fd' = if fd = fd' then none else st.proc.fds !! fd' :=
      GMap.lookup_delete_iff _ _ _
    rw [e3, setFd_fds, setFd_fds]
    by_cases hq : fd = fd'
    · rw [if_pos hq, if_pos hq]
      refine .inr ⟨fun d' h' => ?_, fun d' h' => (by cases h')⟩
      cases h'; exact ⟨by cases d; rfl, by cases d; rfl⟩
    · rw [if_neg hq, if_neg hq, if_neg hq]; exact .inl rfl
  imodintro
  iapply lockCtx_frame hL hfr $$ Hlk

end ghost

/-! ## Resources -/

section resources
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- An exclusive lock of kind `k` on the file `i`, held through the fd `fd`. -/
def osLock (k : LockKind) (i : Ino) (fd : w64) : IProp GF :=
  gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γlk (k, i) (DFrac.own 1) fd

instance osLock_timeless (k : LockKind) (i : Ino) (fd : w64) : Timeless (osLock (L := L) k i fd) := by
  unfold osLock; infer_instance

/-- **Exclusive locks exclude each other**: at most one fd holds an exclusive lock of a kind on a
file. -/
theorem osLock_excl (k : LockKind) (i : Ino) (fd1 fd2 : w64) :
    osLock (L := L) k i fd1 ∗ osLock (L := L) k i fd2 ⊢ False := by
  unfold osLock
  iintro ⟨H1, H2⟩
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %Hv
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- The token of the description `d`'s exclusive lock of kind `k` (through `fd`), if it has one. -/
def lockTok (k : LockKind) (fd : w64) (d : OsFd) : IProp GF :=
  if d.lk k = some true then osLock (L := L) k d.ino fd else emp

/-- The tokens of the description `d`'s exclusive locks (through `fd`): `emp` if it has none. -/
def lockToks (fd : w64) (d : OsFd) : IProp GF :=
  iprop(lockTok (L := L) .ofd fd d ∗ lockTok (L := L) .flock fd d)

instance lockTok_timeless (k : LockKind) (fd : w64) (d : OsFd) :
    Timeless (lockTok (L := L) k fd d) := by
  unfold lockTok; split <;> infer_instance

instance lockToks_timeless (fd : w64) (d : OsFd) : Timeless (lockToks (L := L) fd d) := by
  unfold lockToks; infer_instance

theorem lockTok_none (k : LockKind) (fd : w64) (d : OsFd) (h : d.lk k ≠ some true) :
    ⊢ lockTok (L := L) k fd d := by
  unfold lockTok; rw [if_neg h]; iempintro

/-- An unlocked description (every `open` gives one) has no tokens. -/
theorem lockToks_unlocked (fd : w64) (d : OsFd) (h1 : d.ofd = none) (h2 : d.flk = none) :
    ⊢ lockToks (L := L) fd d := by
  unfold lockToks
  isplitl []
  · iapply lockTok_none; simp [OsFd.lk, h1]
  · iapply lockTok_none; simp [OsFd.lk, h2]

theorem lockTok_some (k : LockKind) (fd : w64) (d : OsFd) (h : d.lk k = some true) :
    lockTok (L := L) k fd d ⊣⊢ osLock (L := L) k d.ino fd := by
  unfold lockTok; rw [if_pos h]; exact .rfl

theorem lockTok_setLk_ne {k k' : LockKind} (fd : w64) (d : OsFd) (x : Option Bool) (h : k' ≠ k) :
    lockTok (L := L) k' fd (d.setLk k x) ⊣⊢ lockTok (L := L) k' fd d := by
  unfold lockTok; rw [setLk_setLk_ne d x h, setLk_ino]; exact .rfl

/-- What a lock call of kind `k` through `fd` leaves (`LockStep`), for the request `req` (`some ex`: a
lock, exclusive iff `ex`; `none`: an unlock): the description `d'`, whole, and its token of the kind:
`d` with the request done on success (`e = 0`), `d` unchanged on a lock's failure, either on an
unlock's failure. -/
def lockOut (k : LockKind) (fd : w64) (d : OsFd) (req : Option Bool) (e : w64) : IProp GF :=
  iprop(∃ d' : OsFd, osFd (L := L) fd (DFrac.own 1) d' ∗ lockTok (L := L) k fd d' ∗
    ⌜(d' = d ∨ d' = d.setLk k req) ∧ (e = 0 → d' = d.setLk k req) ∧ (req ≠ none → e ≠ 0 → d' = d)⌝)

end resources

/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

/-- The world after a lock call through `fd` set the description's lock of kind `k` to `x`. -/
theorem lockStep_world {st : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)} {fd : w64}
    {d : OsFd} {k : LockKind} {x : Option Bool} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hd : st.proc.fds !! fd = some d)
    (hok : ∀ ex, x = some ex → d.lk k = none ∧ ¬ LockConflict st k fd d.ino ex)
    (hr : HeapRendered st (st.setFd fd (d.setLk k x)) h h')
    (hfr : MapsFresh st (st.setFd fd (d.setLk k x)) h) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗ tokRes (gooseOsGS (L := L)) Γt -∗
      cellsRes (cellView st) -∗ naHeapCtx tls h -∗ lockCtx (gooseOsGS (L := L)) st -∗
      osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) k fd d ==∗
      ∃ Γf', osWorld (L := L) (st.setFd fd (d.setLk k x)) Γb Γm Γf' Γt h' ∗
        lockCtx (gooseOsGS (L := L)) (st.setFd fd (d.setLk k x)) ∗
        osFd (L := L) fd (DFrac.own 1) (d.setLk k x) ∗ lockTok (L := L) k fd (d.setLk k x) := by
  iintro HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht
  have hX : ∀ fd' d', (<[fd := d.setLk k x]> st.proc.fds) !! fd' = some d' →
      ∃ f, st.file d'.ino = some f := by
    intro fd' d' h1
    by_cases hq : fd = fd'
    · subst hq; rw [GMap.lookup_insert] at h1; cases h1; rw [setLk_ino]; exact hwf.fds fd d hd
    · rw [GMap.lookup_insert_ne _ _ hq] at h1; exact hwf.fds fd' d' h1
  have hwf' : OsWf (st.setFd fd (d.setLk k x)) := osWf_fds hwf _ hX
  unfold osFd
  imod gFdElem_update _ _ _ _ _ (d.setLk k x) $$ HAf Hfd with ⟨HAf, Hfd⟩
  imod cells_same hwf hwf' hr hfr rfl (cellView_congr hwf hwf' rfl (fun _ => rfl) rfl)
    $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  unfold lockTok osLock
  rw [setLk_lk, if_pos rfl, setLk_ino]
  imod lockCtx_setLk _ hd hok $$ [Hlk Ht] with ⟨Hlk, Ht⟩
  · iframe
  imodintro
  iexists (<[fd := d.setLk k x]> Γf)
  iframe Hlk Hfd Ht
  unfold osWorld
  iframe
  ipureintro
  refine ⟨hwf', ?_⟩
  rw [hcoh.fds]; exact osCoh_fds hcoh _

/-- A failing lock step's witness: errno 1, no change. -/
theorem lockStep_fail_ex {st : OsState} {k : LockKind} {fd : w64}
    {d : OsFd} {req : Option Bool} {nb : Bool} {w : Expr} (hfree : req ≠ none → d.lk k = none) :
    LockStep st k fd d req nb w (Val (#(1 : w64))) st := by
  unfold LockStep
  cases req with
  | some ex => exact ⟨hfree (by simp), .inr (.inl ⟨1, by decide, rfl, rfl⟩)⟩
  | none => exact .inr ⟨1, by decide, rfl, .inl rfl⟩

/-- **The lock rule's spec**: the step of an operation `o` whose steps from `st` are, for the open
`fd` (description `d`), the lock rule's for kind `k` and request `req`, with a fact `Ψ` of every step of
the semantics the program runs (a premise's, `FsStepSat`); a wait (the call steps to
itself) leaves everything as it was, and the call is made again (Löb induction). -/
theorem wp_osLockStepP (o : String) (v : val) (k : LockKind) (fd : w64) (d : OsFd)
    (req : Option Bool) (nb : Bool) (hv : v.isPanic = false) (ho : DataOp o) (hE : ↑osN ⊆ E)
    (hfree : req ≠ none → d.lk k = none)
    (hex : ∀ st e' st', st.proc.fds !! fd = some d →
      LockStep st k fd d req nb (ExternalOp fsExt.name o (Val v)) e' st' → IsFsStep o v st e' st')
    (hst : ∀ st e' st', st.proc.fds !! fd = some d → IsFsStep o v st e' st' →
      LockStep st k fd d req nb (ExternalOp fsExt.name o (Val v)) e' st')
    (Ψ : Expr → Prop)
    (hΨ : ∀ h st e' h' st', ExtSemantics.step (E := fsExt) GoLocalContext.typeFns o v h st () e' h' st' () → Ψ e')
    (Φ : val → IProp GF) (hM : o ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) k fd d -∗
      (∀ e : w64, ⌜Ψ (Val (#e))⌝ -∗ lockOut (L := L) k fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  iloeb as IH generalizing Hfd Ht HΦ
  iapply wp_os_stepLX o v Φ hv hE ho hM $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Hlk
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  ihave %Hfdl := (show ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
      osFd (L := L) fd (DFrac.own 1) d -∗ ⌜Γf !! fd = some d⌝ from by
    unfold osFd; exact gFdElem_lookup _ _ _ _ _ _) $$ HAf Hfd
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, hex st _ st hfd (lockStep_fail_ex hfree), mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨⟨Hst, Hfr, Hr⟩, Hsem⟩ := Hst
  have hψ := hΨ _ _ _ _ _ Hsem
  have hl := hst st e' st' hfd Hst
  have hdone : ∀ (x : Option Bool) (e : w64), st' = st.setFd fd (d.setLk k x) →
      e' = Val (#e) → (∀ ex, x = some ex → d.lk k = none ∧ ¬ LockConflict st k fd d.ino ex) →
      ((d.setLk k x = d ∨ d.setLk k x = d.setLk k req) ∧ (e = 0 → d.setLk k x = d.setLk k req) ∧
        (req ≠ none → e ≠ 0 → d.setLk k x = d)) →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗ tokRes (gooseOsGS (L := L)) Γt -∗
        cellsRes (cellView st) -∗ naHeapCtx tls h -∗ lockCtx (gooseOsGS (L := L)) st -∗
        osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) k fd d -∗
        (∀ e : w64, ⌜Ψ (Val (#e))⌝ -∗ lockOut (L := L) k fd d req e -∗ Φ (#e)) ==∗
        ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗ lockCtx (gooseOsGS (L := L)) st' ∗
          WP e' @ s; E {{ Φ }} := by
    intro x e hst' he' hok hpost
    subst hst' he'
    iintro HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ
    ihave HΦ := HΦ $$ %e %hψ
    imod lockStep_world hwf hcoh hfd hok Hr Hfr $$ HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht
      with ⟨%Γf', Hw, Hlk, Hfd, Ht⟩
    imodintro
    iexists Γb, Γm, Γf', Γt
    iframe Hw Hlk
    iapply wp_value'
    iapply HΦ
    unfold lockOut
    iexists (d.setLk k x)
    iframe Hfd Ht
    ipureintro; exact hpost
  have hsame : ∀ (e : w64), st' = st → e' = Val (#e) → (e = 0 → d = d.setLk k req) →
      ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γf Γf -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γt Γt -∗ tokRes (gooseOsGS (L := L)) Γt -∗
        cellsRes (cellView st) -∗ naHeapCtx tls h -∗ lockCtx (gooseOsGS (L := L)) st -∗
        osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) k fd d -∗
        (∀ e : w64, ⌜Ψ (Val (#e))⌝ -∗ lockOut (L := L) k fd d req e -∗ Φ (#e)) ==∗
        ∃ Γb' Γm' Γf' Γt', osWorld st' Γb' Γm' Γf' Γt' h' ∗ lockCtx (gooseOsGS (L := L)) st' ∗
          WP e' @ s; E {{ Φ }} := by
    intro e hst' he' h0
    subst hst' he'
    iintro HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ
    ihave HΦ := HΦ $$ %e %hψ
    imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, Γm, Γf, Γt
    iframe Hlk
    isplitl [HAb HAm HAf HAt Htok Hcells Hσ]
    · unfold osWorld; iframe; ipureintro; exact ⟨hwf, hcoh⟩
    iapply wp_value'
    iapply HΦ
    unfold lockOut
    iexists d
    iframe Hfd Ht
    ipureintro; exact ⟨.inl rfl, h0, fun _ _ => rfl⟩
  unfold osWorld at hdone hsame
  unfold LockStep at hl
  split at hl
  · rename_i ex
    obtain ⟨hnone, ⟨hnc, hst', he'⟩ | ⟨e, he, hst', he'⟩ | ⟨-, -, hst', he'⟩⟩ := hl
    · iapply hdone (some ex) 0 hst' he' (fun ex' h => by cases h; exact ⟨hnone, hnc⟩)
        ⟨.inr rfl, fun _ => rfl, fun _ h => absurd rfl h⟩ $$ HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ
    · iapply hsame e hst' he' (fun h => absurd h he) $$ HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ
    · -- the wait: nothing changes, the call again
      subst hst' he'
      imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
      · iframe
      imodintro
      iexists Γb, Γm, Γf, Γt
      iframe Hlk
      isplitl [HAb HAm HAf HAt Htok Hcells Hσ]
      · iframe; ipureintro; exact ⟨hwf, hcoh⟩
      iapply IH $$ Hfd Ht HΦ
  · obtain ⟨hst', he'⟩ | ⟨e, he, he', hst' | hst'⟩ := hl
    · iapply hdone none 0 hst' he' (fun ex h => by cases h)
        ⟨.inr rfl, fun _ => rfl, fun h => absurd rfl h⟩ $$ HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ
    · iapply hsame e hst' he' (fun h => absurd h he) $$ HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ
    · iapply hdone none e hst' he' (fun ex h => by cases h)
        ⟨.inr rfl, fun _ => rfl, fun h => absurd rfl h⟩ $$ HAb HAm HAf HAt Htok Hcells Hσ Hlk Hfd Ht HΦ

/-- **The lock rule's spec** (`wp_osLockStepP` with no fact of the steps). -/
theorem wp_osLockStep (o : String) (v : val) (k : LockKind) (fd : w64) (d : OsFd)
    (req : Option Bool) (nb : Bool) (hv : v.isPanic = false) (ho : DataOp o) (hE : ↑osN ⊆ E)
    (hfree : req ≠ none → d.lk k = none)
    (hex : ∀ st e' st', st.proc.fds !! fd = some d →
      LockStep st k fd d req nb (ExternalOp fsExt.name o (Val v)) e' st' → IsFsStep o v st e' st')
    (hst : ∀ st e' st', st.proc.fds !! fd = some d → IsFsStep o v st e' st' →
      LockStep st k fd d req nb (ExternalOp fsExt.name o (Val v)) e' st') (Φ : val → IProp GF)
    (hM : o ≠ "Mmap" := by decide) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) k fd d -∗
      (∀ e : w64, lockOut (L := L) k fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  iapply wp_osLockStepP o v k fd d req nb hv ho hE hfree hex hst (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) Φ hM $$ Hinv Hfd Ht
  iintro %e - Ho
  iapply HΦ $$ Ho

/-- `fcntl(fd, cmd, {typ, whole file})`, `cmd` `F_OFD_SETLK` or `F_OFD_SETLKW`, `typ` `F_RDLCK`,
`F_WRLCK` or `F_UNLCK` (`ofdReq`: the request `req`), with the whole fd and the token of its OFD lock
(if exclusive): a lock only on a description with no OFD lock. On success the description holds the
requested lock (an exclusive one with its token, `osLock .ofd d.ino fd`); a lock's failure changes
nothing; an unlock's failure may have released it. -/
theorem wp_osOfdLockP (fd cmd typ : w64) (d : OsFd) (req : Option Bool) (hE : ↑osN ⊆ E)
    (hcmd : cmd.toNat = F_OFD_SETLK ∨ cmd.toNat = F_OFD_SETLKW) (hreq : ofdReq typ.toNat = some req)
    (hw : req = some true → d.writable = true) (hr : req = some false → d.readable = true)
    (hfree : req ≠ none → d.ofd = none) (Ψ : Expr → Prop)
    (hΨ : ∀ h st e' h' st', ExtSemantics.step (E := fsExt) GoLocalContext.typeFns "OfdLock"
      (PairV (#fd) (PairV (#cmd) (#typ))) h st () e' h' st' () → Ψ e') (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .ofd fd d -∗
      (∀ e : w64, ⌜Ψ (Val (#e))⌝ -∗ lockOut (L := L) .ofd fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OfdLock" (Val (PairV (#fd) (PairV (#cmd) (#typ))))) @ s; E {{ Φ }} := by
  iapply wp_osLockStepP "OfdLock" _ .ofd fd d req (decide (cmd.toNat = F_OFD_SETLK))
    (by simp [val.isPanic]) (by simp [DataOp]) hE hfree (Ψ := Ψ) (hΨ := hΨ)
  · intro st e' st' hfd hl
    exact ⟨fd, cmd, typ, d, req, rfl, hfd, hcmd, hreq, hw, hr, hl⟩
  · intro st e' st' hfd hs
    simp only [IsFsStep] at hs
    obtain ⟨fd', cmd', typ', d', req', hv, hfd', -, hreq', -, -, hl⟩ := hs
    injection hv with h1 h2; injection h2 with h3 h4
    cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
    simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
    rw [hreq, Option.some.injEq] at hreq'; subst hreq'
    exact hl

/-- `wp_osOfdLockP` with no fact of the steps. -/
theorem wp_osOfdLock (fd cmd typ : w64) (d : OsFd) (req : Option Bool) (hE : ↑osN ⊆ E)
    (hcmd : cmd.toNat = F_OFD_SETLK ∨ cmd.toNat = F_OFD_SETLKW) (hreq : ofdReq typ.toNat = some req)
    (hw : req = some true → d.writable = true) (hr : req = some false → d.readable = true)
    (hfree : req ≠ none → d.ofd = none) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .ofd fd d -∗
      (∀ e : w64, lockOut (L := L) .ofd fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OfdLock" (Val (PairV (#fd) (PairV (#cmd) (#typ))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  iapply wp_osOfdLockP fd cmd typ d req hE hcmd hreq hw hr hfree (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) Φ $$ Hinv Hfd Ht
  iintro %e - Ho
  iapply HΦ $$ Ho

/-- `flock(fd, how)`, `how` `LOCK_SH`, `LOCK_EX` or `LOCK_UN`, with or without `LOCK_NB` (`flockReq`:
the request `req`), with the whole fd and the token of its `flock` lock (if exclusive): as
`wp_osOfdLock`, for the description's `flock` lock (no access mode needed). -/
theorem wp_osFlockP (fd how : w64) (d : OsFd) (req : Option Bool) (nb : Bool) (hE : ↑osN ⊆ E)
    (hhow : flockReq how.toNat = some (req, nb)) (hfree : req ≠ none → d.flk = none)
    (Ψ : Expr → Prop)
    (hΨ : ∀ h st e' h' st', ExtSemantics.step (E := fsExt) GoLocalContext.typeFns "Flock" (PairV (#fd) (#how)) h st () e' h'
      st' () → Ψ e') (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .flock fd d -∗
      (∀ e : w64, ⌜Ψ (Val (#e))⌝ -∗ lockOut (L := L) .flock fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how)))) @ s; E {{ Φ }} := by
  iapply wp_osLockStepP "Flock" _ .flock fd d req nb (by simp [val.isPanic]) (by simp [DataOp]) hE
    hfree (Ψ := Ψ) (hΨ := hΨ)
  · intro st e' st' hfd hl
    exact ⟨fd, how, d, req, nb, rfl, hfd, hhow, hl⟩
  · intro st e' st' hfd hs
    simp only [IsFsStep] at hs
    obtain ⟨fd', how', d', req', nb', hv, hfd', hhow', hl⟩ := hs
    injection hv with h1 h2
    cases go.intoVal_inj h1; cases go.intoVal_inj h2
    simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
    rw [hhow, Option.some.injEq, Prod.mk.injEq] at hhow'; obtain ⟨rfl, rfl⟩ := hhow'
    exact hl

/-- `wp_osFlockP` with no fact of the steps. -/
theorem wp_osFlock (fd how : w64) (d : OsFd) (req : Option Bool) (nb : Bool) (hE : ↑osN ⊆ E)
    (hhow : flockReq how.toNat = some (req, nb)) (hfree : req ≠ none → d.flk = none)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .flock fd d -∗
      (∀ e : w64, lockOut (L := L) .flock fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  iapply wp_osFlockP fd how d req nb hE hhow hfree (fun _ => True) (fun _ _ _ _ _ _ => trivial) Φ
    $$ Hinv Hfd Ht
  iintro %e - Ho
  iapply HΦ $$ Ho

/-- `close(fd)`, with the whole fd and its locks' tokens: whatever the errno, the fd is gone and its
locks' tokens are spent (the locks are released, or, with a live mapping made through `fd`, kept by
the description the mapping holds, `MapDesc`, until it is unmapped: no token for them remains). -/
theorem wp_osClose (fd : w64) (d : OsFd) (hE : ↑osN ⊆ E) :
    {{ osInv (L := L) ∗ osFd (L := L) fd (DFrac.own 1) d ∗ lockToks (L := L) fd d }}
      (ExternalOp fsExt.name "Close" (Val (#fd))) @ s; E
    {{ (e : w64), RET #e; True }} := by
  iintro %Φ ⟨#Hinv, Hfd, Ht⟩ HΦ
  iapply wp_os_stepL "Close" (#fd) Φ (by simp) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw Hlk
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gFdElem_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  have hwfC := osWf_closeFd hwf fd d
  have hcv : cellView (st.closeFd fd d) = cellView st :=
    cellView_congr hwf hwfC rfl (fun _ => rfl) rfl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st.closeFd fd d, ⟨fd, 0, d, rfl, hfd, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwfC rfl hcv Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', e, d', hv, hfd', rfl, rfl⟩ := Hst
  cases go.intoVal_inj hv
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  imod gFdElem_delete _ _ _ _ _ $$ HAf Hfd with HAf
  imod cells_same hwf hwfC Hr Hfr rfl hcv $$ [Hσ Hcells]
    with ⟨Hσ, Hcells⟩
  · iframe
  unfold lockToks lockTok osLock
  imod lockCtx_close _ hfd $$ [Hlk Ht] with Hlk
  · iframe
  ihave Hlk := lockCtx_frame _ (lockFrame_of_fds (st := st.delFd fd) (st' := st.closeFd fd d) rfl) $$ Hlk
  imodintro
  iexists Γb, Γm, (GMap.delete fd Γf), Γt
  iframe
  isplitr
  · ipureintro; refine ⟨hwfC, ?_⟩; rw [hcoh.fds]; exact osCoh_closeFd hcoh fd d
  iapply wp_value'
  iapply HΦ
  itrivial

end specs

end Fs
end Perennial

end
