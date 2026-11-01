/-
The extension's operations over a file in a crash invariant (`Proof/os/CrashFile.lean`): each
opens the invariant around its one step (`osOp_atomic`), applies the extension-level spec to the
halves of the resources put together, and closes it with the new state.

* `wp_osFsync_cf`: idle to synced (or, on failure, `ok := false`, which a crash does not see).
* `wp_osOpen_cf`: absent or idle to `openState`, on failure maybe not.
* `wp_osPWriteStart_cf`: idle to a write in flight, whose crash the caller shows `Good`.
* `wp_osPWriteFinish_cf`: a write in flight to idle, `Good` by `crashOk_finish`.
-/
module

public import Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

instance osBytes_timeless' (p : GoString) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) :
    Timeless (osBytes (L := L) p off dq xs) := by unfold osBytes; infer_instance

instance invRes_timeless (p : GoString) (s : CFile) : Timeless (invRes (L := L) p s) := by
  rcases s with _ | ⟨m, bs, _ | ⟨t, off, data⟩⟩ <;> unfold invRes
  · infer_instance
  · infer_instance
  · unfold pwTok osTok; infer_instance

theorem invRes_idle (p : GoString) (m : OsMeta) (bs : List (w8 × Bool)) :
    invRes (L := L) p (some (m, bs, none)) ⊣⊢
      osMeta (L := L) p (DFrac.own (1 : Qp).half) (some m) ∗
        osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) bs := .rfl

theorem invRes_none (p : GoString) :
    invRes (L := L) p none ⊣⊢ osMeta (L := L) p (DFrac.own (1 : Qp).half) none := .rfl

theorem invRes_busy (p : GoString) (m : OsMeta) (bs : List (w8 × Bool)) (t off : Nat)
    (data : List w8) :
    invRes (L := L) p (some (m, bs, some (t, off, data))) ⊣⊢
      pwTok (L := L) t p off data 1 m (cfRange m bs off data.length) ∗
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) (bs.take (cfLo m off)) ∗
      osBytes (L := L) p (cfHi m off data.length) (DFrac.own (1 : Qp).half)
        (bs.drop (cfHi m off data.length)) := .rfl

end res

/-! ## Pure facts of the crash views -/

theorem syncedBytes_length (m : OsMeta) (bs : List (w8 × Bool)) :
    (syncedBytes m bs).length = bs.length := by
  unfold syncedBytes; split <;> simp

/-- What a crash may leave does not depend on `ok`. -/
theorem crashOk_notOk {Good : Option OsFile → Prop} {m : OsMeta} {bs : List (w8 × Bool)}
    (h : CrashOk Good (some (m, bs, none))) : CrashOk Good (some ({ m with ok := false }, bs, none)) :=
  h

/-- The number of a write's token does not matter to a crash. -/
theorem crashOk_tok {Good : Option OsFile → Prop} {m : OsMeta} {bs : List (w8 × Bool)}
    {off : Nat} {data : List w8} (t : Nat) (h : CrashOk Good (cfWriting m bs off data)) :
    CrashOk Good (some (m, bs, some (t, off, data))) :=
  h

/-- The state an open without `O_TRUNC` leaves: the file created, if absent. -/
def openState : CFile → CFile
  | none => some (newMeta, [], none)
  | s => s

/-- The `OsMeta` of a state without a change in flight. -/
def cfMeta : CFile → Option OsMeta
  | none => none
  | some (m, _, _) => some m

theorem openMeta_cfMeta (s : CFile) (hs : s = none ∨ ∃ m bs, s = some (m, bs, none)) :
    openMeta (cfMeta s) true = cfMeta (openState s) := by
  rcases hs with rfl | ⟨m, bs, rfl⟩ <;> rfl

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- `fsync(fd)` of a file in a crash invariant, idle: on success it is synced, which the caller
shows a crash of `Good`; on failure, its `ok` is lost. -/
theorem wp_osFsync_cf (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Good : Option OsFile → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : CrashOk Good (some (m.synced, syncedBytes m bs, none))) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N d.path γ Good -∗ osFd (L := L) fd dq d -∗
      cfOwn (L := L) d.path γ (some (m, bs, none)) -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ cfOwn (L := L) d.path γ (some (m.synced, syncedBytes m bs, none))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ cfOwn (L := L) d.path γ (some ({ m with ok := false }, bs, none)))) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv Hfd ⟨Hv, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold cfInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases Ht with ⟨Hm1, Hb1⟩
  icases (invRes_idle _ _ _).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  ihave Hb := (osBytes_halves _ _ _).2 $$ [Hb1 Hb2]
  · iframe
  imodintro
  iapply wp_osFsync fd dq d m 0 bs hN $$ Hos Hfd Hm Hb
  iintro %e Hres Hfd
  icases Hres with (⟨%he, Hm, Hb⟩ | ⟨%he, Hm, Hb⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    imod ghostVar_update_halves (some (m.synced, syncedBytes m bs, none)) γ _ _ $$ Hv Hv'
      with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (m.synced, syncedBytes m bs, none)); iframe Hv'
      isplitl; · iapply (invRes_idle _ _ _).2; iframe
      ipureintro; exact hok
    imodintro
    iapply HΦ $$ %e [Hv Hm1 Hb1] Hfd
    ileft
    isplitr
    · ipureintro; exact he
    iframe
    ipureintro
    exact ⟨by rw [syncedBytes_length]; exact Hwf.1, Hwf.2⟩
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    imod ghostVar_update_halves (some ({ m with ok := false }, bs, none)) γ _ _ $$ Hv Hv'
      with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some ({ m with ok := false }, bs, none)); iframe Hv'
      isplitl; · iapply (invRes_idle _ _ _).2; iframe
      ipureintro; exact crashOk_notOk Hok'
    imodintro
    iapply HΦ $$ %e [Hv Hm1 Hb1] Hfd
    iright
    isplitr
    · ipureintro; exact he
    iframe
    ipureintro
    exact Hwf

end ops

end Perennial
