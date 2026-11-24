/-
The extension's operations over a file in a crash invariant (`Proof/os/CrashFile.lean`): each
opens the invariant around its one step (`fsOp_atomic`), applies the extension-level spec to the
halves of the resources put together, and closes it with the new state.

* `wp_osFsync_cf`: idle to synced (on failure, unchanged).
* `wp_osOpenCreate_cf`: no file at `p`, the create (the invariant's half of the claim on the
  file's name and the caller's make it whole), to the new file and the claim with its `create`
  logged; on failure maybe.
* `wp_osPWriteStart_cf`: idle to a write in flight, whose crash the caller shows `Good`.
* `wp_osPWriteFinish_cf`: a write in flight to idle (`finBytes`), `Good` by the caller's `FileOk`.

The specs' loops (`Proof/os/Crash.lean`) use `openSt`/`OpenInv` (what an `open(O_CREAT)` loop may
have made of the state: a failed attempt may have created the file) and `Proof/os/CrashWrite.lean`
(a write's attempts keep `WIn` and the bytes written so far).
-/
module

public import Proof.os.CrashWrite

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

instance osBytes_timeless' (i : Ino) (off : Nat) (dq : DFrac) (xs : List ByteG) :
    Timeless (osBytes (L := L) i off dq xs) := by unfold osBytes; infer_instance

instance invRes_timeless (s : CFile) : Timeless (invRes (L := L) s) := by
  rcases s with _ | ⟨i, m, bs, _ | ⟨t, off, data, n⟩⟩ <;> unfold invRes
  · infer_instance
  · infer_instance
  · unfold pwTok osTok; infer_instance

theorem osBytes_nil' (i : Ino) (off : Nat) (dq : DFrac) :
    osBytes (L := L) i off dq [] ⊣⊢ emp := by
  unfold osBytes bytesG; simp

/-- The bytes of a file, around a write of `n` bytes at `off`: before, taken, after. -/
theorem osBytes_split3 (i : Ino) (m : OsMeta) (bs : List ByteG) (off n : Nat)
    (dq : DFrac) (hlen : bs.length = m.size) :
    osBytes (L := L) i 0 dq bs ⊣⊢ osBytes (L := L) i 0 dq (bs.take (cfLo m off)) ∗
      osBytes (L := L) i (cfLo m off) dq (cfRange m bs off n) ∗
      osBytes (L := L) i (cfHi m off n) dq (bs.drop (cfHi m off n)) := by
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
  have A1 := bytesG_append (gooseOsGS (L := L)) i dq 0 (bs.take (cfLo m off))
    (cfRange m bs off n ++ bs.drop (cfHi m off n))
  rw [hl1] at A1
  have A2 := bytesG_append (gooseOsGS (L := L)) i dq (cfLo m off) (cfRange m bs off n)
    (bs.drop (cfHi m off n))
  rw [hl2] at A2
  unfold osBytes
  conv => lhs; rw [e]
  exact A1.trans (sep_congr_right A2)

/-- Three runs of bytes, end to end (the last one may be empty, wherever it starts). -/
theorem osBytes_join3 (i : Ino) (o1 o2 o3 : Nat) (dq : DFrac) (xs ys zs : List ByteG)
    (h1 : o1 + xs.length = o2) (h2 : o2 + ys.length = o3 ∨ zs = []) :
    osBytes (L := L) i o1 dq xs ∗ osBytes (L := L) i o2 dq ys ∗ osBytes (L := L) i o3 dq zs ⊢
      osBytes (L := L) i o1 dq (xs ++ ys ++ zs) := by
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

end res


/-! ## Pure facts of the crash views -/

/-- `TreeOk` depends on the state's inode only. -/
theorem treeOk_ino {Good : Option OsFile → Prop} {j : Ino} {b : GoString} {s s' : CFile}
    {h : NamesH} (he : cIno s' = cIno s) (ht : TreeOk Good j b s h) : TreeOk Good j b s' h := by
  intro K
  rcases ht K with h1 | ⟨i, hi, hl⟩
  · exact .inl h1
  · exact .inr ⟨i, he.trans hi, hl⟩

/-- `PathOk` depends on the state's inode only. -/
theorem pathOk_ino {b : GoString} {i : Ino} {x x' : CX} {h : NamesH}
    (hp : PathOk b (some (i, x)) h) : PathOk b (some (i, x')) h := hp

/-- The state of the file at `p` after an `open(O_CREAT)` of it succeeds, from the state `s`, the
file being `i`: created if `s` has none, unchanged otherwise. -/
def openSt (i : Ino) : CFile → CFile
  | none => some (i, newMeta, [], none)
  | some x => some x

/-- What an `open(O_CREAT)` loop of the file at `p` may have made of the state `s` so far:
nothing, or `openSt` of it (a failed attempt may have created the file). -/
def OpenInv (s s' : CFile) : Prop :=
  s' = s ∨ ∃ i, s' = openSt i s

/-- With a file at the path, it is idle, and it is what `openSt` makes of `s`. -/
theorem openInv_some {s : CFile} {i : Ino} {y : CX}
    (hs : s = none ∨ ∃ i m bs, s = some (i, m, bs, none)) (h : OpenInv s (some (i, y))) :
    (s = none ∨ cIno s = some i) ∧ some (i, y) = openSt i s ∧ ∃ m bs, y = (m, bs, none) := by
  rcases h with h1 | ⟨i1, h⟩
  · subst h1
    rcases hs with h | ⟨i0, m, bs, h⟩
    · cases h
    · cases h; exact ⟨.inr rfl, rfl, m, bs, rfl⟩
  · cases s with
    | none =>
      simp only [openSt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.inl rfl, rfl, _, _, rfl⟩
    | some x =>
      simp only [openSt, Option.some.injEq] at h
      subst h
      rcases hs with h | ⟨i0, m, bs, h⟩
      · cases h
      · cases h; exact ⟨.inr rfl, rfl, m, bs, rfl⟩

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant's state, from the caller's: they agree; and the invariant's half of the claim
on the file's name. -/
theorem cf_open (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (s : CFile) :
    ⊢ cfInv (L := L) N p R γ Good -∗ ghostVar γ (1 : Qp).half s ={⊤, ⊤ \ ↑N}=∗
      ghostVar γ (1 : Qp).half s ∗ invRes (L := L) s ∗ ghostVar γ (1 : Qp).half s ∗
      ∃ (j : Ino) (b : GoString) (h : NamesH), ⌜FileAt R p j b⌝ ∗ ⌜CrashOk Good j b s h⌝ ∗
        osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ∗
        (∀ (s' : CFile) (h' : NamesH), ghostVar γ (1 : Qp).half s' -∗ invRes (L := L) s' -∗
          osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h' -∗
          ⌜CrashOk Good j b s' h'⌝ ={⊤ \ ↑N, ⊤}=∗ True) := by
  iintro #Hinv Hv
  unfold cfInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%s', %j, %b, %h, %hfa, Hv', Hr, Hn, %Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  imodintro
  iframe Hv Hr Hv'
  iexists j, b, h
  iframe Hn
  isplitr
  · ipureintro; exact hfa
  isplitr
  · ipureintro; exact Hok'
  iintro %s2 %h2 Hv2 Hr2 Hn2 %Hok2
  iapply Hclose
  inext; iexists s2, j, b, h2; iframe; isplitr
  · ipureintro; exact hfa
  ipureintro; exact Hok2

/-- The caller's claim and the invariant's are on one name: they agree, and make it whole. -/
theorem cf_claims (R : Roots) (p : GoString) (j j' : Ino) (b b' : GoString) (h h' : NamesH)
    (hfa : FileAt R p j b) (hfa' : FileAt R p j' b') :
    ⊢ osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h -∗
      osNames (L := L) j' (.only [b']) (DFrac.own (1 : Qp).half) h' -∗
      ⌜j' = j ∧ b' = b ∧ h' = h⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h := by
  obtain ⟨rfl, rfl⟩ := fileAt_unique hfa hfa'
  iintro H1 H2
  icases osNames_agree _ _ _ _ _ _ $$ H1 H2 with %he
  subst he
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iapply (osNames_halves' j _ h).2
  iframe

/-- `fsync(fd)` of a file in a crash invariant, idle: on success it is synced (every byte durable),
which the caller shows a crash of `Good`; on failure it is unchanged. -/
theorem wp_osFsync_cf (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (p : GoString) (R : Roots)
    (γ : GName) (Good : Option OsFile → Prop) (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : FileOk Good (m.synced, bs.map (fun x => durB x.1), none))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p R γ Good -∗ osFd (L := L) fd dq d -∗
      cfOwn (L := L) p R γ (some (d.ino, m, bs, none)) -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ cfOwn (L := L) p R γ (some (d.ino, m.synced, bs.map (fun x => durB x.1), none))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ cfOwn (L := L) p R γ (some (d.ino, m, bs, none)))) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv Hfd ⟨%j0, %b0, %h0, Hv, ⟨Hm1, Hb1⟩, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N p R γ Good _ $$ Hinv Hv with ⟨Hv, Hr, Hv', %j, %b, %h, %hfa, %Hok', Hti, Hclose⟩
  dsimp only [invRes]
  icases Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  ihave Hb := (osBytes_halves _ _ _).2 $$ [Hb1 Hb2]
  · iframe
  imodintro
  iapply wp_osFsync fd dq d m 0 bs (m.covers_whole Hwf.1.1) hN $$ Hos Hfd Hm Hb
  iintro %e Hres Hfd
  icases Hres with (⟨%he, Hm, Hb⟩ | ⟨%he, Hm, Hb⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    imod ghostVar_update_halves (some (d.ino, m.synced, bs.map (fun x => durB x.1), none)) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    have hok2 : CrashOk Good j b (some (d.ino, m.synced, bs.map (fun x => durB x.1), none)) h :=
      ⟨treeOk_ino rfl Hok'.1, by rintro i x hx; cases hx; exact hok⟩
    imod Hclose $$ %_ %h Hv' [Hm2 Hb2] Hti %hok2 with -
    · dsimp only [invRes]; iframe
    imodintro
    iapply HΦ $$ %e [Hv Hm1 Hb1 Ht] Hfd
    ileft
    isplitr
    · ipureintro; exact he
    iexists j0, b0, h0
    iframe
    ipureintro
    exact ⟨⟨by rw [List.length_map]; exact Hwf.1.1, Hwf.1.2⟩, Hwf.2⟩
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    imod Hclose $$ %_ %h Hv' [Hm2 Hb2] Hti %Hok' with -
    · dsimp only [invRes]; iframe
    imodintro
    iapply HΦ $$ %e [Hv Hm1 Hb1 Ht] Hfd
    iright
    isplitr
    · ipureintro; exact he
    iexists j0, b0, h0
    iframe
    ipureintro
    exact Hwf


/-- The first step of `pwrite(fd, data, off)` on a file in a crash invariant, idle, the write
starting inside the file and not empty: the write in flight, whose crash the caller shows `Good`
(for any token and change number). -/
theorem wp_osPWriteStart_cf (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hgap : off.toNat ≤ m.size) (hd : data ≠ [])
    (hok : ∀ t n, FileOk Good (m, bs, some (t, off.toNat, data, n))) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p R γ Good -∗ osFd (L := L) fd dq d -∗
      cfOwn (L := L) p R γ (some (d.ino, m, bs, none)) -∗
      (∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗
        cfOwn (L := L) p R γ (some (d.ino, m, bs, some (t, off.toNat, data, n))) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv Hfd ⟨%j0, %b0, %h0, Hv, ⟨Hm1, Hb1⟩, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N p R γ Good _ $$ Hinv Hv with ⟨Hv, Hr, Hv', %j, %b, %h, %hfa, %Hok', Hti, Hclose⟩
  dsimp only [invRes]
  icases Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (osBytes_split3 d.ino m bs off.toNat data.length _ Hwf.1.1).1 $$ Hb1 with ⟨Hp1, Hr1, Hs1⟩
  icases (osBytes_split3 d.ino m bs off.toNat data.length _ Hwf.1.1).1 $$ Hb2 with ⟨Hp2, Hr2, Hs2⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  have hlo : cfLo m off.toNat = off.toNat := Nat.min_eq_left hgap
  ihave Hrg := (show osBytes (L := L) d.ino (cfLo m off.toNat) (DFrac.own 1)
      (cfRange m bs off.toNat data.length) ⊢ osBytes (L := L) d.ino off.toNat
      (DFrac.own 1) (cfRange m bs off.toNat data.length) by rw [hlo]) $$ Hrg
  imodintro
  iapply wp_osPWriteStart fd off data dq d m (cfRange m bs off.toNat data.length) hN hwr hoff
    hgap hd (by have := Hwf.1.1; unfold cfRange cfLo cfHi; simp only [List.length_take, List.length_drop]; omega)
    $$ Hos Hfd Hm Hrg []
  · rw [Hwf.1.2]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
  iintro %t %n %- Hfd Htok
  imod ghostVar_update_halves (some (d.ino, m, bs, some (t, off.toNat, data, n))) γ _ _ $$ Hv Hv'
    with ⟨Hv, Hv'⟩
  have hok2 : CrashOk Good j b (some (d.ino, m, bs, some (t, off.toNat, data, n))) h :=
    ⟨treeOk_ino rfl Hok'.1, by rintro i x hx; cases hx; exact hok t n⟩
  imod Hclose $$ %_ %h Hv' [Htok Hp2 Hs2] Hti %hok2 with -
  · dsimp only [invRes]; iframe
  imodintro
  iapply HΦ $$ %t %n Hfd
  iexists j0, b0, h0
  iframe; ipureintro; exact Hwf

/-- The second step of `pwrite(fd, data, off)` on a file in a crash invariant: idle again, as the
write of the first `k` bytes left it (`finBytes`, the bytes past the old size it reached with the
candidates `zs`), which the caller shows a crash of `Good`. The write started inside the file. -/
theorem wp_osPWriteFinish_cf (t : Nat) (i : Ino) (off : Nat) (data : List w8) (n : Nat)
    (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : ∀ k (zs : List Cands), k ≤ data.length → off ≤ m.size →
      FileOk Good (pwPost m off data.length k, finBytes m bs off data k n zs, none))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p R γ Good -∗
      cfOwn (L := L) p R γ (some (i, m, bs, some (t, off, data, n))) -∗
      (∀ (k : Nat) (e : w64) (zs : List Cands),
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧ off ≤ m.size ∧
          data ≠ []⌝ -∗
        cfOwn (L := L) p R γ (some (i, pwPost m off data.length k, finBytes m bs off data k n zs, none)) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv ⟨%j0, %b0, %h0, Hv, ⟨Hp1, Hs1⟩, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N p R γ Good _ $$ Hinv Hv with ⟨Hv, Hr, Hv', %j, %b, %h, %hfa, %Hok', Hti, Hclose⟩
  dsimp only [invRes]
  icases Hr with ⟨Htok, Hp2, Hs2⟩
  unfold pwTok
  icases Htok with ⟨Htok, %hgap⟩
  obtain ⟨hgap, hd, -⟩ := hgap
  imodintro
  iapply wp_osPWriteFinish t i off data m (cfRange m bs off data.length) n hN $$ Hos [Htok]
  · unfold pwTok; iframe; ipureintro
    refine ⟨hgap, hd, ?_⟩
    have := Hwf.1.1; unfold cfRange cfLo cfHi; simp only [List.length_take, List.length_drop]; omega
  iintro %k %e %zs %hke %- Hm Hrg -
  have hk := hke.1
  have hwl := Hwf.1.1
  have hlen : (finBytes m bs off data k n zs).length = (pwPost m off data.length k).size :=
    finBytes_length hwl hgap hk
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  have hlo : 0 + (bs.take (cfLo m off)).length = off := by
    simp only [List.length_take]; unfold cfLo; omega
  have hhi : off + (pwBytes m.size off data k n (cfRange m bs off data.length) zs).length =
      cfHi m off data.length ∨ bs.drop (cfHi m off data.length) = [] := by
    rw [pwBytes_length]
    have := pwSize_ge3 m.size off k
    by_cases hs : off + data.length ≤ m.size
    · left; unfold cfHi pwSize; split <;> omega
    · right; apply List.drop_eq_nil_of_le; unfold cfHi; omega
  ihave Hb1 := osBytes_join3 i 0 off (cfHi m off data.length) _ _ _ _ hlo hhi
    $$ [Hp1 Hr1 Hs1]
  · iframe
  ihave Hb2 := osBytes_join3 i 0 off (cfHi m off data.length) _ _ _ _ hlo hhi
    $$ [Hp2 Hr2 Hs2]
  · iframe
  have hlo' : cfLo m off = off := Nat.min_eq_left hgap
  have hfb : ∀ dq, osBytes (L := L) i 0 dq (bs.take (cfLo m off) ++
      pwBytes m.size off data k n (cfRange m bs off data.length) zs ++ bs.drop (cfHi m off data.length)) ⊢
      osBytes (L := L) i 0 dq (finBytes m bs off data k n zs) := fun _ => by unfold finBytes; rw [hlo']
  ihave Hb1 := hfb _ $$ Hb1
  ihave Hb2 := hfb _ $$ Hb2
  imod ghostVar_update_halves (some (i, pwPost m off data.length k, finBytes m bs off data k n zs, none))
    γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  have hok2 : CrashOk Good j b (some (i, pwPost m off data.length k, finBytes m bs off data k n zs, none)) h :=
    ⟨treeOk_ino rfl Hok'.1, by rintro i' x hx; cases hx; exact hok k zs hk hgap⟩
  have hke' : k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧ off ≤ m.size ∧
      data ≠ [] := ⟨hke.1, hke.2.1, hgap, hd⟩
  imod Hclose $$ %_ %h Hv' [Hm2 Hb2] Hti %hok2 with -
  · dsimp only [invRes]; iframe Hm2; iexact Hb2
  imodintro
  iapply HΦ $$ %k %e %zs %hke'
  iexists j0, b0, h0
  iframe Hv Hm1 Ht
  isplitl [Hb1]
  · iexact Hb1
  ipureintro; exact ⟨⟨hlen, by simp [pwPost, Hwf.1.2]⟩, Hwf.2⟩

/-- `open(2)` with `O_RDWR | O_CREAT` of `p = d/b` (`d` the root directory `j`), no file there, in
a crash invariant: the invariant's half of the claim on `b` and the caller's make it whole, so the
create can happen; on success the new file, idle, which the caller shows a crash of `Good`
(`FileOk Good (newMeta, [], none)`); on failure it may have been created. -/
theorem wp_osOpenCreate_cf (d b : GoString) (N : Namespace) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (j : Ino) (dq : DFrac) (h : NamesH) (k s0 : Nat) (q : Qp)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hN' : ↑osShN ⊆ (⊤ : CoPset) \ ↑N) (hb : NameOk b)
    (hfa : FileAt R (child d b) j b) (hn : h.cur !! b = none) (hs : h.next ≤ s0)
    (hok : FileOk Good (newMeta, [], none)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ cfInv (L := L) N (child d b) R γ Good -∗
      osPathS (L := L) R d dq j -∗ ghostVar γ (1 : Qp).half (none : CFile) -∗
      osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h -∗
      osCallS (L := L) k s0 (child d b) q -∗
      (∀ fd : w64, ∀ e : w64, osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        ((∃ i, ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗
            cfOwn (L := L) (child d b) R γ (some (i, newMeta, [], none)) ∗
            osFd (L := L) fd (DFrac.own 1) ⟨i, true, true, none, none⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (cfOwn (L := L) (child d b) R γ none ∨ ∃ i,
            cfOwn (L := L) (child d b) R γ (some (i, newMeta, [], none))))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#flCreat)))))
        {{ Φ }} := by
  iintro #Hos #Hsi #Hinv Hp Hv Hn Hk HΦ
  have hnm : ([] : List ByteG).length = newMeta.size ∧ newMeta.maps = ∅ := by
    simp [newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N (child d b) R γ Good _ $$ Hinv Hv
    with ⟨Hv, -, Hv', %j', %b', %h', %hfa', %Hok', Hti, Hclose⟩
  icases cf_claims R (child d b) j j' b b' h h' hfa hfa' $$ Hn Hti with ⟨%he, Hw⟩
  obtain ⟨hj, hb', hh⟩ := he
  subst j' b' h'
  imodintro
  iapply wp_osOpenCreateS R d b j dq h k s0 q flCreat
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) (by decide) hb
    (fun J hJ => by rw [hn] at hJ; cases hJ) hs hN hN' $$ Hos Hsi Hp Hw Hk
  iintro %fd %e Hperm Hp Hres
  have hpush : ∀ x i, CrashOk Good j b (some (i, newMeta, [], none))
      (h.log x ⟨.create j b i, s0⟩ (<[b := .file i]> h.cur)) :=
    fun x i => ⟨treeOk_create x s0 _ Hok'.1, by rintro i' y hy; cases hy; exact hok⟩
  have hpath : ∀ x i, PathOk b (some (i, newMeta, [], none))
      (h.log x ⟨.create j b i, s0⟩ (<[b := .file i]> h.cur)) :=
    fun x i => GMap.lookup_insert _ _ _
  icases Hres with (⟨%i, %hi, -, -⟩ | ⟨-, %x, %i, -, Hw, Hm, Hfd⟩ | ⟨%he, Hw⟩)
  · rw [hn] at hi; cases hi
  · icases (osNames_halves' j _ _).1 $$ Hw with ⟨Hw1, Hw2⟩
    icases (osMeta_halves i newMeta).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves (some (i, newMeta, [], none)) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ %_ %_ Hv' [Hm2] Hw1 %(hpush x i) with -
    · dsimp only [invRes]; iframe; iapply (osBytes_nil' _ _ _).2; iempintro
    imodintro
    iapply HΦ $$ %fd %e Hperm Hp
    ihave Hown := (show ghostVar γ (1 : Qp).half (some (i, newMeta, [], none) : CFile) ∗
        osMeta (L := L) i (DFrac.own (1 : Qp).half) newMeta ∗
        osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half)
          (h.log x ⟨.create j b i, s0⟩ (<[b := .file i]> h.cur)) ⊢
        cfOwn (L := L) (child d b) R γ (some (i, newMeta, [], none)) by
      iintro ⟨Hv, Hm1, Hw2⟩
      unfold cfOwn
      iexists j, b, _
      dsimp only [thrRes]
      iframe Hv Hm1 Hw2
      isplitl []
      · iapply (osBytes_nil' _ _ _).2; iempintro
      ipureintro; exact ⟨hnm, hpath x i, hfa⟩) $$ [Hv Hm1 Hw2]
    · iframe
    icases Hfd with (%he | ⟨%he, Hfd⟩)
    · iright
      isplitr
      · ipureintro; exact he
      iright; iexists i; iexact Hown
    · ileft
      iexists i
      isplitr
      · ipureintro; exact he
      iframe Hown
      rw [openFd_rw]; iexact Hfd
  · icases (osNames_halves' j _ _).1 $$ Hw with ⟨Hw1, Hw2⟩
    imod Hclose $$ %none %h Hv' [] Hw1 %Hok' with -
    · dsimp only [invRes]; iempintro
    imodintro
    iapply HΦ $$ %fd %e Hperm Hp
    iright
    isplitr
    · ipureintro; exact he
    ileft
    unfold cfOwn
    iexists j, b, h
    dsimp only [thrRes]
    iframe Hv Hw2
    isplitr
    · iempintro
    ipureintro; first | exact ⟨trivial, hn, hfa⟩ | exact ⟨hn, hfa⟩


theorem cfOwn_wf (p : GoString) (R : Roots) (γ : GName) (s : CFile) :
    cfOwn (L := L) p R γ s ⊢ ⌜CfWf s⌝ := by
  unfold cfOwn; iintro ⟨%j, %b, %h, -, -, -, %hw⟩; ipureintro; exact hw.1

/-- The caller's part of no file at `p`: the claim's half, on a name holding nothing. -/
theorem cfOwn_none (p : GoString) (R : Roots) (γ : GName) :
    cfOwn (L := L) p R γ none ⊢ ghostVar γ (1 : Qp).half (none : CFile) ∗
      ∃ (j : Ino) (b : GoString) (h : NamesH),
        osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ∗
        ⌜h.cur !! b = none ∧ FileAt R p j b⌝ := by
  unfold cfOwn; dsimp only [thrRes]
  iintro ⟨%j, %b, %h, Hv, -, Ht, %hw⟩; iframe Hv; iexists j, b, h; iframe; ipureintro
  exact hw.2

/-- The caller's part of the file `i` at `p`: its half of the claim, lent out. -/
theorem cfOwn_tree (p : GoString) (R : Roots) (γ : GName) (i : Ino) (x : CX) :
    cfOwn (L := L) p R γ (some (i, x)) ⊢ ∃ (j : Ino) (b : GoString) (h : NamesH),
      osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h ∗
      ⌜h.cur !! b = some (.file i) ∧ FileAt R p j b⌝ ∗
      (osNames (L := L) j (.only [b]) (DFrac.own (1 : Qp).half) h -∗
        cfOwn (L := L) p R γ (some (i, x))) := by
  unfold cfOwn
  iintro ⟨%j, %b, %h, Hv, Hr, Ht, %hw⟩
  iexists j, b, h
  iframe Ht
  isplitr
  · ipureintro; exact hw.2
  iintro Ht
  iexists j, b, h
  iframe
  ipureintro; exact hw

end ops

end Perennial
