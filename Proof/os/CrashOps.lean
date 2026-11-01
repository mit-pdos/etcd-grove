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

public import Proof.os.CrashNarrow

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

theorem osBytes_nil' (p : GoString) (off : Nat) (dq : DFrac) :
    osBytes (L := L) p off dq [] ⊣⊢ emp := .rfl

/-- The bytes of a file, around a write of `n` bytes at `off`: before, taken, after. -/
theorem osBytes_split3 (p : GoString) (m : OsMeta) (bs : List (w8 × Bool)) (off n : Nat)
    (dq : DFrac) (hlen : bs.length = m.size) :
    osBytes (L := L) p 0 dq bs ⊣⊢ osBytes (L := L) p 0 dq (bs.take (cfLo m off)) ∗
      osBytes (L := L) p (cfLo m off) dq (cfRange m bs off n) ∗
      osBytes (L := L) p (cfHi m off n) dq (bs.drop (cfHi m off n)) := by
  have hlh : cfLo m off ≤ cfHi m off n := by unfold cfLo cfHi; omega
  have hhs : cfHi m off n ≤ bs.length := by unfold cfHi; omega
  have e : bs = bs.take (cfLo m off) ++ (cfRange m bs off n ++ bs.drop (cfHi m off n)) := by
    have : bs.drop (cfHi m off n) = (bs.drop (cfLo m off)).drop (cfHi m off n - cfLo m off) := by
      rw [List.drop_drop]; congr 1; omega
    unfold cfRange
    rw [this, List.take_append_drop, List.take_append_drop]
  have hl1 : 0 + (bs.take (cfLo m off)).length = cfLo m off := by
    simp only [List.length_take]; omega
  have hl2 : cfLo m off + (cfRange m bs off n).length = cfHi m off n := by
    unfold cfRange; simp only [List.length_take, List.length_drop]; omega
  have A1 := bytesG_append (gooseOsGS (L := L)) p dq 0 (bs.take (cfLo m off))
    (cfRange m bs off n ++ bs.drop (cfHi m off n))
  rw [hl1] at A1
  have A2 := bytesG_append (gooseOsGS (L := L)) p dq (cfLo m off) (cfRange m bs off n)
    (bs.drop (cfHi m off n))
  rw [hl2] at A2
  unfold osBytes
  conv => lhs; rw [e]
  exact A1.trans (sep_congr_right A2)

/-- Three runs of bytes, end to end (the last one may be empty, wherever it starts). -/
theorem osBytes_join3 (p : GoString) (o1 o2 o3 : Nat) (dq : DFrac) (xs ys zs : List (w8 × Bool))
    (h1 : o1 + xs.length = o2) (h2 : o2 + ys.length = o3 ∨ zs = []) :
    osBytes (L := L) p o1 dq xs ∗ osBytes (L := L) p o2 dq ys ∗ osBytes (L := L) p o3 dq zs ⊢
      osBytes (L := L) p o1 dq (xs ++ ys ++ zs) := by
  subst h1
  unfold osBytes
  rcases h2 with h2 | rfl
  · subst h2
    rw [List.append_assoc]
    refine BIBase.Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
    refine sep_mono .rfl ?_
    exact (bytesG_append _ _ _ _ _ _).2
  · rw [List.append_nil]
    iintro ⟨H1, H2, -⟩
    iapply (bytesG_append _ _ _ _ _ _).2
    iframe

theorem cfOwn_none (p : GoString) (γ : GName) :
    cfOwn (L := L) p γ none ⊣⊢ ghostVar γ (1 : Qp).half (none : CFile) ∗
      osMeta (L := L) p (DFrac.own (1 : Qp).half) none ∗ ⌜True⌝ := .rfl

theorem cfOwn_idle (p : GoString) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool)) :
    cfOwn (L := L) p γ (some (m, bs, none)) ⊣⊢ ghostVar γ (1 : Qp).half (some (m, bs, none) : CFile) ∗
      (osMeta (L := L) p (DFrac.own (1 : Qp).half) (some m) ∗
        osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) bs) ∗
      ⌜bs.length = m.size ∧ m.maps = ∅⌝ := .rfl

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

/-- `open(p, fl)` (with `O_CREAT`, without `O_TRUNC`) of a file in a crash invariant, absent or
idle: on success it is `openState s` (created if absent, which the caller shows a crash of
`Good`); on failure it may have been created. -/
theorem wp_osOpen_cf (p : GoString) (fl : w64) (N : Namespace) (γ : GName)
    (Good : Option OsFile → Prop) (s : CFile) (hs : s = none ∨ ∃ m bs, s = some (m, bs, none))
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 0)
    (hcr : fl.toNat / O_CREAT % 2 = 1) (hok : CrashOk Good (openState s)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p γ Good -∗ cfOwn (L := L) p γ s -∗
      (∀ fd : w64, ∀ e : w64, ∀ s' : CFile,
        ⌜(e = 0 ∧ 0 ≤ fd.toInt ∧ s' = openState s) ∨
          (e ≠ 0 ∧ fd = -1 ∧ (s' = s ∨ s' = openState s))⌝ -∗
        cfOwn (L := L) p γ s' -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd p fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "Open" (Val (PairV (#p) (#fl)))) {{ Φ }} := by
  have hcr' : decide (fl.toNat / O_CREAT % 2 = 1) = true := decide_eq_true hcr
  rcases hs with rfl | ⟨m, bs, rfl⟩
  · -- absent: the open may create it, with the whole `OsMeta`
    iintro #Hos #Hinv Hown HΦ
    icases (cfOwn_none _ _).1 $$ Hown with ⟨Hv, Hm1, -⟩
    iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
    unfold cfInv
    imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
      with ⟨Hi, Hclose⟩
    icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
    icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
    subst Heq
    icases (invRes_none _).1 $$ Hr with Hm2
    ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
    · iframe
    imodintro
    iapply wp_osOpen p fl (DFrac.own 1) none hN hfl htr (fun _ => rfl) $$ Hos Hm
    iintro %fd %e %mo' %hres Hm Hfd
    rw [hcr'] at hres
    have hmo : mo' = none ∨ mo' = some newMeta := by
      rcases hres with ⟨-, -, h, -⟩ | ⟨-, -, h | h⟩
      · exact .inr h
      · exact .inl h
      · exact .inr h
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    rcases hmo with rfl | rfl
    · imod Hclose $$ [Hv' Hm2] with -
      · inext; iexists none; iframe Hv'; isplitl
        · iapply (invRes_none _).2; iexact Hm2
        ipureintro; exact Hok'
      imodintro
      iapply HΦ $$ %fd %e %none [] [Hv Hm1] Hfd
      · ipureintro
        rcases hres with ⟨-, -, h, -⟩ | ⟨he, hfd, -⟩
        · cases h
        · exact .inr ⟨he, hfd, .inl rfl⟩
      iapply (cfOwn_none _ _).2
      iframe
    · imod ghostVar_update_halves (some (newMeta, [], none)) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
      imod Hclose $$ [Hv' Hm2] with -
      · inext; iexists (some (newMeta, [], none)); iframe Hv'; isplitl
        · iapply (invRes_idle _ _ _).2; iframe Hm2; iapply (osBytes_nil' _ _ _).2; iempintro
        ipureintro; exact hok
      imodintro
      iapply HΦ $$ %fd %e %(some (newMeta, [], none)) [] [Hv Hm1] Hfd
      · ipureintro
        rcases hres with ⟨he, hfd, -, -⟩ | ⟨he, hfd, -⟩
        · exact .inl ⟨he, hfd, rfl⟩
        · exact .inr ⟨he, hfd, .inr rfl⟩
      iapply (cfOwn_idle _ _ _ _).2
      iframe Hv Hm1
      isplitl
      · iapply (osBytes_nil' _ _ _).2; iempintro
      ipureintro; exact ⟨rfl, rfl⟩
  · -- idle: the thread's half of the `OsMeta` is enough, and the open changes nothing
    iintro #Hos #Hinv Hown HΦ
    icases (cfOwn_idle _ _ _ _).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
    iapply wp_osOpen p fl _ (some m) CoPset.subseteq_top hfl htr (fun h => by cases h) $$ Hos Hm1
    iintro %fd %e %mo' %hres Hm Hfd
    have hmo : mo' = some m := by
      rcases hres with ⟨-, -, h, -⟩ | ⟨-, -, h | h⟩ <;> rw [h] <;> rfl
    subst hmo
    iapply HΦ $$ %fd %e %(some (m, bs, none)) [] [Hv Hm Hb1] Hfd
    · ipureintro
      rcases hres with ⟨he, hfd, -⟩ | ⟨he, hfd, -⟩
      · exact .inl ⟨he, hfd, rfl⟩
      · exact .inr ⟨he, hfd, .inl rfl⟩
    iapply (cfOwn_idle _ _ _ _).2
    iframe; ipureintro; exact Hwf

/-- The first step of `pwrite(fd, data, off)` on a file in a crash invariant, idle: the write is
in flight, which the caller shows a crash of `Good`. -/
theorem wp_osPWriteStart_cf (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (γ : GName) (Good : Option OsFile → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hok : CrashOk Good (cfWriting m bs off.toNat data)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N d.path γ Good -∗ osFd (L := L) fd dq d -∗
      cfOwn (L := L) d.path γ (some (m, bs, none)) -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗
        cfOwn (L := L) d.path γ (some (m, bs, some (t, off.toNat, data))) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv Hfd ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold cfInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invRes_idle _ _ _).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (osBytes_split3 d.path m bs off.toNat data.length _ Hwf.1).1 $$ Hb1 with ⟨Hp1, Hr1, Hs1⟩
  icases (osBytes_split3 d.path m bs off.toNat data.length _ Hwf.1).1 $$ Hb2 with ⟨Hp2, Hr2, Hs2⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  ihave Hrg := (show osBytes (L := L) d.path (cfLo m off.toNat) (DFrac.own 1)
      (cfRange m bs off.toNat data.length) ⊢ osBytes (L := L) d.path (min off.toNat m.size)
      (DFrac.own 1) (cfRange m bs off.toNat data.length) from .rfl) $$ Hrg
  imodintro
  iapply wp_osPWriteStart fd off data dq d 1 m (cfRange m bs off.toNat data.length) hN hwr hoff
    (by have := Hwf.1; unfold cfRange cfLo cfHi; simp only [List.length_take, List.length_drop]; omega)
    (fun _ => rfl) $$ Hos Hfd Hm Hrg []
  · rw [Hwf.2]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
  iintro %t Hfd Ht
  imod ghostVar_update_halves (some (m, bs, some (t, off.toNat, data))) γ _ _ $$ Hv Hv'
    with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ht Hp2 Hs2] with -
  · inext; iexists (some (m, bs, some (t, off.toNat, data))); iframe Hv'; isplitl
    · iapply (invRes_busy _ _ _ _ _ _).2; iframe
    ipureintro; exact crashOk_tok t hok
  imodintro
  iapply HΦ $$ %t Hfd
  iframe; ipureintro; exact Hwf

/-- The second step of `pwrite(fd, data, off)` on a file in a crash invariant: idle again, as the
write of the first `k` bytes left it, which the caller shows a crash of `Good`. -/
theorem wp_osPWriteFinish_cf (t : Nat) (p : GoString) (off : Nat) (data : List w8)
    (N : Namespace) (γ : GName) (Good : Option OsFile → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : ∀ k ≤ data.length, CrashOk Good (some (finMeta m off data k, finBytes m bs off data k, none)))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p γ Good -∗
      cfOwn (L := L) p γ (some (m, bs, some (t, off, data))) -∗
      (∀ k : Nat, ∀ e : w64, ⌜k ≤ data.length ∧ (k = data.length ∧ e = 0 ∨ e ≠ 0)⌝ -∗
        cfOwn (L := L) p γ (some (finMeta m off data k, finBytes m bs off data k, none)) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp osFsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv ⟨Hv, ⟨Hp1, Hs1⟩, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold cfInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invRes_busy _ _ _ _ _ _).1 $$ Hr with ⟨Ht, Hp2, Hs2⟩
  imodintro
  iapply wp_osPWriteFinish t p off data 1 m (cfRange m bs off data.length) hN $$ Hos Ht
  iintro %k %e %hke Hm Hrg -
  have hk := hke.1
  have hlen : (finBytes m bs off data k).length = (finMeta m off data k).size :=
    finBytes_length Hwf.1 hk
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  have hwl := Hwf.1
  have hlo : 0 + (bs.take (cfLo m off)).length = min off m.size := by
    simp only [List.length_take]; unfold cfLo; omega
  have hhi : min off m.size + (pwBytes m.size off data k (cfRange m bs off data.length)).length =
      cfHi m off data.length ∨ bs.drop (cfHi m off data.length) = [] := by
    rw [pwBytes_length]
    have := pwSize_ge m.size off k
    by_cases hs : off + data.length ≤ m.size
    · left; unfold cfHi pwSize; split <;> omega
    · right; apply List.drop_eq_nil_of_le; unfold cfHi; omega
  ihave Hb1 := osBytes_join3 p 0 (min off m.size) (cfHi m off data.length) _ _ _ _ hlo hhi
    $$ [Hp1 Hr1 Hs1]
  · iframe
  ihave Hb2 := osBytes_join3 p 0 (min off m.size) (cfHi m off data.length) _ _ _ _ hlo hhi
    $$ [Hp2 Hr2 Hs2]
  · iframe
  imod ghostVar_update_halves (some (finMeta m off data k, finBytes m bs off data k, none)) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hm2 Hb2] with -
  · inext; iexists (some (finMeta m off data k, finBytes m bs off data k, none)); iframe Hv'
    isplitl
    · iapply (invRes_idle _ _ _).2; iframe
    ipureintro; exact hok k hk
  imodintro
  iapply HΦ $$ %k %e %hke
  iframe
  ipureintro; exact ⟨hlen, Hwf.2⟩

end ops

end Perennial
