/-
The extension's operations over a file in a crash invariant (`Proof/os/CrashFile.lean`): each
opens the invariant around its one step (`fsOp_atomic`), applies the extension-level spec to the
halves of the resources put together, and closes it with the new state.

* `wp_osFsync_cf`: idle to synced (or, on failure, `ok := false`, which a crash does not see).
* `wp_osOpenCreate_cf`: no file at `p`, the create (the invariant's half of the history and the
  caller's make it whole), to the new file and the history with its `create`; on failure maybe.
* `wp_osPWriteStart_cf`: idle to a write in flight, whose crash the caller shows `Good`.
* `wp_osPWriteFinish_cf`: a write in flight to idle, `Good` by the caller's `FileOk`.

The specs' loops (`Proof/os/Crash.lean`) use `openSt`/`OpenInv` (what an `open(O_CREAT)` loop may
have made of the state: a failed attempt may have created the file) and `wa_step` (a write's
attempt from `nn` keeps the narrowing and the bytes written so far).
-/
module

public import Proof.os.CrashNarrow
public import Proof.os.OpenFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

instance osBytes_timeless' (i : Ino) (off : Nat) (dq : DFrac) (xs : List (w8 × Bool)) :
    Timeless (osBytes (L := L) i off dq xs) := by unfold osBytes; infer_instance

instance invRes_timeless (s : CFile) : Timeless (invRes (L := L) s) := by
  rcases s with _ | ⟨i, m, bs, _ | ⟨t, off, data⟩⟩ <;> unfold invRes
  · infer_instance
  · infer_instance
  · unfold pwTok osTok; infer_instance

instance osTree_timeless (dq : DFrac) (R : Roots) (V : Hist) : Timeless (osTree (L := L) dq R V) := by
  unfold osTree; infer_instance

theorem osBytes_nil' (i : Ino) (off : Nat) (dq : DFrac) :
    osBytes (L := L) i off dq [] ⊣⊢ emp := by
  unfold osBytes bytesG; simp

/-- The bytes of a file, around a write of `n` bytes at `off`: before, taken, after. -/
theorem osBytes_split3 (i : Ino) (m : OsMeta) (bs : List (w8 × Bool)) (off n : Nat)
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
theorem osBytes_join3 (i : Ino) (o1 o2 o3 : Nat) (dq : DFrac) (xs ys zs : List (w8 × Bool))
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

theorem syncedBytes_length (m : OsMeta) (bs : List (w8 × Bool)) :
    (syncedBytes m bs).length = bs.length := by
  unfold syncedBytes; split <;> simp

/-- `TreeOk` depends on the state's inode only. -/
theorem treeOk_ino {Good : Option OsFile → Prop} {p : GoString} {R : Roots} {s s' : CFile}
    {V : Hist} (he : cIno s' = cIno s) (h : TreeOk Good p R s V) : TreeOk Good p R s' V := by
  intro V' hc
  rcases h V' hc with h | ⟨i, hi, hl⟩
  · exact .inl h
  · exact .inr ⟨i, he.trans hi, hl⟩

/-- `PathOk` depends on the state's inode only. -/
theorem pathOk_ino {p : GoString} {R : Roots} {i : Ino} {x x' : OsMeta × List (w8 × Bool) ×
    Option (Nat × Nat × List w8)} {V : Hist} (h : PathOk p R (some (i, x)) V) :
    PathOk p R (some (i, x')) V := h

/-- What a crash may leave does not depend on `ok`. -/
theorem fileOk_notOk {Good : Option OsFile → Prop} {m : OsMeta} {bs : List (w8 × Bool)}
    (h : FileOk Good (m, bs, none)) : FileOk Good ({ m with ok := false }, bs, none) :=
  h

/-- The number of a write's token does not matter to a crash. -/
theorem fileOk_tok {Good : Option OsFile → Prop} {m : OsMeta} {bs : List (w8 × Bool)}
    {off : Nat} {data : List w8} (t : Nat) (h : FileOk Good (cfWriting m bs off data)) :
    FileOk Good (m, bs, some (t, off, data)) :=
  h

/-- **The tree after the create** of the file `i` at `p`, from no file at `p`: every crash leaves
`p` naming nothing, as before the create, or the file. -/
theorem treeOk_create {Good : Option OsFile → Prop} {d b : GoString} {R : Roots} {V : Hist}
    {j i : Ino} (hr : RootsOk R) (hd : lookupH R V d = some (.dir j)) (hb : NameOk b)
    (hn : lookupH R V (child d b) = none) (h : TreeOk Good (child d b) R none V)
    (x : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8)) :
    TreeOk Good (child d b) R (some (i, x)) (V.push ⟨.create j b i, V.2.length⟩) := by
  intro V' hc
  rcases treeCrashed_push hc with hc | hnow
  · rcases h V' hc with h | ⟨i', hi, -⟩
    · exact .inl h
    · cases hi
  · right
    refine ⟨i, rfl, ?_⟩
    rw [lookupH_congr _ hnow]
    exact EtcdGrove.lookupH_create V.2.length hr hd hb hn

/-- The state of the file at `d/b` and the history after an `open(O_CREAT)` of it succeeds, from
the state `s` and the history `V`, the file being `i`: created (`d` being the directory `j`) if `s`
has none, unchanged otherwise. -/
def openSt (j : Ino) (b : GoString) (V : Hist) (i : Ino) : CFile → CFile × Hist
  | none => (some (i, newMeta, [], none), V.push ⟨.create j b i, V.2.length⟩)
  | some x => (some x, V)

/-- What an `open(O_CREAT)` loop of the file at `d/b` may have made of the state `s` and the
history `V` so far: nothing, or `openSt` of them (a failed attempt may have created the file). -/
def OpenInv (j : Ino) (b : GoString) (V : Hist) (s s' : CFile) (V' : Hist) : Prop :=
  (s' = s ∧ V' = V) ∨ ∃ i, (s', V') = openSt j b V i s

/-- With a file at the path, it is idle, and it is what `openSt` makes of `s`. -/
theorem openInv_some {j : Ino} {b : GoString} {V V' : Hist} {s : CFile} {i : Ino}
    {y : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8)}
    (hs : s = none ∨ ∃ i m bs, s = some (i, m, bs, none)) (h : OpenInv j b V s (some (i, y)) V') :
    (s = none ∨ cIno s = some i) ∧ (some (i, y), V') = openSt j b V i s ∧
      ∃ m bs, y = (m, bs, none) := by
  rcases h with ⟨h1, h2⟩ | ⟨i1, h⟩
  · subst h1 h2
    rcases hs with h | ⟨i0, m, bs, h⟩
    · cases h
    · cases h; exact ⟨.inr rfl, rfl, m, bs, rfl⟩
  · cases s with
    | none =>
      simp only [openSt, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨.inl rfl, rfl, _, _, rfl⟩
    | some x =>
      simp only [openSt, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hs with h | ⟨i0, m, bs, h⟩
      · cases h
      · cases h; exact ⟨.inr rfl, rfl, m, bs, rfl⟩

/-- An attempt of a write's loop, `w` of its bytes written so far, the attempt from `nn ≤ w` (the
next from `o = off + nn`), the first `k` of the rest written by it: the narrowing, the size, the
bytes written so far (`max w (nn + k)` of them) and the bytes past them unchanged. -/
theorem wa_step {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {off nn w o k : Nat} {data : List w8}
    (hgap : off ≤ m.size) (hNar : Narrow m bs off data m' bs') (hS : off + w ≤ m'.size)
    (hnw : nn ≤ w) (hw : w ≤ data.length)
    (hpre : ∀ i < w, (bs'[off + i]?).map Prod.fst = data[i]?)
    (hmid : ∀ i, off + w ≤ i → bs'[i]? = bs[i]?) (ho : o = off + nn)
    (hk : k ≤ (data.drop nn).length) (hU : m'.size ≤ max m.size (off + w)) :
    Narrow m bs off data (finMeta m' o (data.drop nn) k) (finBytes m' bs' o (data.drop nn) k) ∧
      off + max w (nn + k) ≤ (finMeta m' o (data.drop nn) k).size ∧
      (finMeta m' o (data.drop nn) k).size ≤ max m.size (off + max w (nn + k)) ∧
      (∀ i < max w (nn + k), ((finBytes m' bs' o (data.drop nn) k)[off + i]?).map Prod.fst = data[i]?) ∧
      ∀ i, off + max w (nn + k) ≤ i → (finBytes m' bs' o (data.drop nn) k)[i]? = bs[i]? := by
  subst ho
  have hdl : (data.drop nn).length = data.length - nn := List.length_drop
  refine ⟨narrow_fin hNar hgap nn (by omega) hk, ?_, ?_, ?_, ?_⟩
  · show off + max w (nn + k) ≤ pwSize m'.size (off + nn) k
    unfold pwSize; split <;> omega
  · show pwSize m'.size (off + nn) k ≤ _
    unfold pwSize; split <;> omega
  · intro i hi
    by_cases hin : i < nn
    · rw [finBytes_pre hNar.len (off + i) (by unfold cfLo; omega)]
      exact hpre i (by omega)
    by_cases hik : i < nn + k
    · have := finBytes_written (m := m') (bs := bs') (off := off + nn) (data := data.drop nn)
        (k := k) hNar.len (by omega) hk (i - nn) (by omega)
      rw [show off + nn + (i - nn) = off + i by omega, List.getElem?_drop,
        show nn + (i - nn) = i by omega] at this
      exact this
    · rw [finBytes_keep hNar.len (by omega) hk (off + i) (by omega)]
      exact hpre i (by omega)
  · intro i hi
    rw [finBytes_keep hNar.len (by omega) hk i (by omega)]
    exact hmid i (by omega)

/-- An attempt of a write's loop, `nn` of its bytes written (the next from `o = off + nn`), the
first `k` of the rest written by it: the narrowing, the size and the bytes written so far (the
loop of `Proof/os/CrashStSpec.lean`, which needs neither the size bound nor the bytes past them). -/
theorem wa_stepS {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {off nn o k : Nat} {data : List w8}
    (hgap : off ≤ m.size) (hNar : Narrow m bs off data m' bs') (hS : off + nn ≤ m'.size)
    (hpre : ∀ i < nn, (bs'[off + i]?).map Prod.fst = data[i]?) (ho : o = off + nn)
    (hnn : nn ≤ data.length) (hk : k ≤ (data.drop nn).length) :
    Narrow m bs off data (finMeta m' o (data.drop nn) k) (finBytes m' bs' o (data.drop nn) k) ∧
      off + nn + k ≤ (finMeta m' o (data.drop nn) k).size ∧
      ∀ i < nn + k, ((finBytes m' bs' o (data.drop nn) k)[off + i]?).map Prod.fst = data[i]? := by
  subst ho
  have hdl : (data.drop nn).length = data.length - nn := List.length_drop
  refine ⟨narrow_fin hNar hgap nn hnn hk, ?_, ?_⟩
  · show off + nn + k ≤ pwSize m'.size (off + nn) k
    unfold pwSize; split <;> omega
  · intro i hi
    by_cases hin : i < nn
    · rw [finBytes_pre hNar.len (off + i) (by unfold cfLo; omega)]
      exact hpre i hin
    · have := finBytes_written (m := m') (bs := bs') (off := off + nn) (data := data.drop nn)
        (k := k) hNar.len hS hk (i - nn) (by omega)
      rw [show off + nn + (i - nn) = off + i by omega, List.getElem?_drop,
        show nn + (i - nn) = i by omega] at this
      exact this


section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant's state, from the caller's: they agree, and so do the histories. -/
theorem cf_open (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (s : CFile) (V : Hist) (dq : DFrac) :
    ⊢ cfInv (L := L) N p R γ Good -∗ ghostVar γ (1 : Qp).half s -∗
      osTree (L := L) dq R V ={⊤, ⊤ \ ↑N}=∗
      ghostVar γ (1 : Qp).half s ∗ osTree (L := L) dq R V ∗ invRes (L := L) s ∗
        osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ghostVar γ (1 : Qp).half s ∗
        ⌜CrashOk Good p R s V⌝ ∗
        (∀ (s' : CFile) (V' : Hist), ghostVar γ (1 : Qp).half s' -∗ invRes (L := L) s' -∗
          osTree (L := L) (DFrac.own (1 : Qp).half) R V' -∗ ⌜CrashOk Good p R s' V'⌝ ={⊤ \ ↑N, ⊤}=∗
          True) := by
  iintro #Hinv Hv Ht
  unfold cfInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', %V', >Hv', >Hr, >Ht', >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases osTree_agree _ _ _ _ _ _ $$ Ht Ht' with %Heq
  obtain ⟨-, rfl⟩ := Heq
  imodintro
  iframe Hv Ht Hr Ht' Hv'
  isplitr
  · ipureintro; exact Hok'
  iintro %s2 %V2 Hv2 Hr2 Ht2 %Hok2
  iapply Hclose
  inext; iexists s2, V2; iframe; ipureintro; exact Hok2

/-- `fsync(fd)` of a file in a crash invariant, idle: on success it is synced, which the caller
shows a crash of `Good`; on failure, its `ok` is lost. -/
theorem wp_osFsync_cf (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (p : GoString) (R : Roots)
    (γ : GName) (Good : Option OsFile → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (V : Hist)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hok : FileOk Good (m.synced 0 bs, syncedBytes m bs, none))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p R γ Good -∗ osFd (L := L) fd dq d -∗
      cfOwn (L := L) p R γ (some (d.ino, m, bs, none)) V -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ cfOwn (L := L) p R γ (some (d.ino, m.synced 0 bs, syncedBytes m bs, none)) V) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗
            cfOwn (L := L) p R γ (some (d.ino, { m with ok := false }, bs, none)) V)) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv Hfd ⟨Hv, ⟨Hm1, Hb1⟩, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N p R γ Good _ V _ $$ Hinv Hv Ht with ⟨Hv, Ht, Hr, Hti, Hv', %Hok', Hclose⟩
  dsimp only [invRes]
  icases Hr with ⟨Hm2, Hb2⟩
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
    imod ghostVar_update_halves (some (d.ino, m.synced 0 bs, syncedBytes m bs, none)) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    have hok2 : CrashOk Good p R (some (d.ino, m.synced 0 bs, syncedBytes m bs, none)) V :=
      ⟨treeOk_ino rfl Hok'.1, by rintro i x hx; cases hx; exact hok⟩
    imod Hclose $$ %_ %V Hv' [Hm2 Hb2] Hti %hok2 with -
    · dsimp only [invRes]; iframe
    imodintro
    iapply HΦ $$ %e [Hv Hm1 Hb1 Ht] Hfd
    ileft
    isplitr
    · ipureintro; exact he
    iframe
    ipureintro
    exact ⟨⟨by rw [syncedBytes_length]; exact Hwf.1.1, Hwf.1.2⟩, Hwf.2⟩
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    imod ghostVar_update_halves (some (d.ino, { m with ok := false }, bs, none)) γ _ _ $$ Hv Hv'
      with ⟨Hv, Hv'⟩
    have hok2 : CrashOk Good p R (some (d.ino, { m with ok := false }, bs, none)) V :=
      ⟨treeOk_ino rfl Hok'.1, by rintro i x hx; cases hx; exact fileOk_notOk (Hok'.2 _ _ rfl)⟩
    imod Hclose $$ %_ %V Hv' [Hm2 Hb2] Hti %hok2 with -
    · dsimp only [invRes]; iframe
    imodintro
    iapply HΦ $$ %e [Hv Hm1 Hb1 Ht] Hfd
    iright
    isplitr
    · ipureintro; exact he
    iframe
    ipureintro
    exact Hwf

theorem qp_three : ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half = 1 :=
  Subtype.ext (by grind)

/-- `open(2)` with `O_RDWR | O_CREAT` of `p = d/b`, no file there, in a crash invariant: the
invariant's half of the history and the caller's (with the call's) make it whole, so the create
can happen; on success the new file, idle, which the caller shows a crash of `Good`
(`FileOk Good (newMeta, [], none)`); on failure it may have been created. -/
theorem wp_osOpenCreate_cf (d b : GoString) (N : Namespace) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (V : Hist) (j : Ino) (k s0 : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hb : NameOk b) (hd : lookupH R V d = some (.dir j))
    (hn : lookupH R V (child d b) = none)
    (hok : FileOk Good (newMeta, [], none)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N (child d b) R γ Good -∗
      ghostVar γ (1 : Qp).half (none : CFile) -∗ osTree (L := L) (DFrac.own (1 : Qp).half.half) R V -∗
      osCall (L := L) k s0 (1 : Qp).half.half -∗
      (∀ fd : w64, ∀ e : w64,
        ((∃ i, ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗
            cfOwn (L := L) (child d b) R γ (some (i, newMeta, [], none))
              (V.push ⟨.create j b i, V.2.length⟩) ∗
            osFd (L := L) fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (cfOwn (L := L) (child d b) R γ none V ∨ ∃ i,
            cfOwn (L := L) (child d b) R γ (some (i, newMeta, [], none))
              (V.push ⟨.create j b i, V.2.length⟩)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#flCreat)))))
        {{ Φ }} := by
  iintro #Hos #Hinv Hv Ht Hk HΦ
  have Hwf : CfWf none ∧ PathOk (child d b) R none V := ⟨trivial, hn⟩
  have hnm : ([] : List (w8 × Bool)).length = newMeta.size ∧ newMeta.maps = ∅ := by
    simp [initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N (child d b) R γ Good _ V _ $$ Hinv Hv Ht with ⟨Hv, Ht, -, Hti, Hv', %Hok', Hclose⟩
  ihave Hh := (osTree_split (1 : Qp).half (1 : Qp).half.half R V).2 $$ [Hti Ht]
  · iframe
  imodintro
  iapply wp_osOpenCreate d b R V _ _ k s0 j hb hd hn qp_three hN $$ Hos Hh Hk
  iintro %fd %e %hr Hres
  have hpush : ∀ i, CrashOk Good (child d b) R (some (i, newMeta, [], none))
      (V.push ⟨.create j b i, V.2.length⟩) :=
    fun i => ⟨treeOk_create hr hd hb hn Hok'.1 _, by rintro i' x hx; cases hx; exact hok⟩
  have hpath : ∀ i, PathOk (child d b) R (some (i, newMeta, [], none))
      (V.push ⟨.create j b i, V.2.length⟩) :=
    fun i => EtcdGrove.lookupH_create V.2.length hr hd hb hn
  icases Hres with (⟨%he, %i, Ht, Hm, Hfd⟩ | ⟨%he, (Ht | ⟨%i, Ht, Hm⟩)⟩)
  · icases (osTree_halves R _).1 $$ Ht with ⟨Ht1, Ht2⟩
    icases (osMeta_halves i newMeta).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves (some (i, newMeta, [], none)) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ %_ %_ Hv' [Hm2] Ht1 %(hpush i) with -
    · dsimp only [invRes]; iframe; iapply (osBytes_nil' _ _ _).2; iempintro
    imodintro
    iapply HΦ
    ileft
    iexists i
    iframe Hfd
    isplitr
    · ipureintro; exact he
    try unfold cfOwn
    try dsimp only [thrRes]
    iframe Hv Ht2
    isplitl [Hm1]
    · iframe Hm1; iapply (osBytes_nil' _ _ _).2; iempintro
    ipureintro; exact ⟨hnm, hpath i⟩
  · icases (osTree_halves R _).1 $$ Ht with ⟨Ht1, Ht2⟩
    imod Hclose $$ %none %V Hv' [] Ht1 %Hok' with -
    · dsimp only [invRes]; iempintro
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    ileft
    try unfold cfOwn
    try dsimp only [thrRes]
    iframe Hv Ht2
    isplitr
    · iempintro
    ipureintro; exact Hwf.2
  · icases (osTree_halves R _).1 $$ Ht with ⟨Ht1, Ht2⟩
    icases (osMeta_halves i newMeta).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves (some (i, newMeta, [], none)) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ %_ %_ Hv' [Hm2] Ht1 %(hpush i) with -
    · dsimp only [invRes]; iframe; iapply (osBytes_nil' _ _ _).2; iempintro
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    iright
    iexists i
    try unfold cfOwn
    try dsimp only [thrRes]
    iframe Hv Ht2
    isplitl [Hm1]
    · iframe Hm1; iapply (osBytes_nil' _ _ _).2; iempintro
    ipureintro; exact ⟨hnm, hpath i⟩


/-- The first step of `pwrite(fd, data, off)` on a file in a crash invariant, idle, the write
starting inside the file: the write in flight, whose crash the caller shows `Good`. -/
theorem wp_osPWriteStart_cf (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (m : OsMeta) (bs : List (w8 × Bool)) (V : Hist)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hgap : off.toNat ≤ m.size)
    (hok : FileOk Good (cfWriting m bs off.toNat data)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p R γ Good -∗ osFd (L := L) fd dq d -∗
      cfOwn (L := L) p R γ (some (d.ino, m, bs, none)) V -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗
        cfOwn (L := L) p R γ (some (d.ino, m, bs, some (t, off.toNat, data))) V -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv Hfd ⟨Hv, ⟨Hm1, Hb1⟩, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N p R γ Good _ V _ $$ Hinv Hv Ht with ⟨Hv, Ht, Hr, Hti, Hv', %Hok', Hclose⟩
  dsimp only [invRes]
  icases Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (osBytes_split3 d.ino m bs off.toNat data.length _ Hwf.1.1).1 $$ Hb1 with ⟨Hp1, Hr1, Hs1⟩
  icases (osBytes_split3 d.ino m bs off.toNat data.length _ Hwf.1.1).1 $$ Hb2 with ⟨Hp2, Hr2, Hs2⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  ihave Hrg := (show osBytes (L := L) d.ino (cfLo m off.toNat) (DFrac.own 1)
      (cfRange m bs off.toNat data.length) ⊢ osBytes (L := L) d.ino (min off.toNat m.size)
      (DFrac.own 1) (cfRange m bs off.toNat data.length) from .rfl) $$ Hrg
  imodintro
  iapply wp_osPWriteStart fd off data dq d 1 m (cfRange m bs off.toNat data.length) hN hwr hoff
    hgap (by have := Hwf.1.1; unfold cfRange cfLo cfHi; simp only [List.length_take, List.length_drop]; omega)
    (fun _ => rfl) $$ Hos Hfd Hm Hrg []
  · rw [Hwf.1.2]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
  iintro %t Hfd Htok
  imod ghostVar_update_halves (some (d.ino, m, bs, some (t, off.toNat, data))) γ _ _ $$ Hv Hv'
    with ⟨Hv, Hv'⟩
  have hok2 : CrashOk Good p R (some (d.ino, m, bs, some (t, off.toNat, data))) V :=
    ⟨treeOk_ino rfl Hok'.1, by rintro i x hx; cases hx; exact fileOk_tok t hok⟩
  imod Hclose $$ %_ %V Hv' [Htok Hp2 Hs2] Hti %hok2 with -
  · dsimp only [invRes]; iframe
  imodintro
  iapply HΦ $$ %t Hfd
  iframe; ipureintro; exact Hwf

/-- The second step of `pwrite(fd, data, off)` on a file in a crash invariant: idle again, as the
write of the first `k` bytes left it, which the caller shows a crash of `Good`. The write started
inside the file. -/
theorem wp_osPWriteFinish_cf (t : Nat) (i : Ino) (off : Nat) (data : List w8)
    (N : Namespace) (p : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (m : OsMeta) (bs : List (w8 × Bool)) (V : Hist)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : ∀ k ≤ data.length, FileOk Good (finMeta m off data k, finBytes m bs off data k, none))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ cfInv (L := L) N p R γ Good -∗
      cfOwn (L := L) p R γ (some (i, m, bs, some (t, off, data))) V -∗
      (∀ k : Nat, ∀ e : w64,
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧ off ≤ m.size⌝ -∗
        cfOwn (L := L) p R γ (some (i, finMeta m off data k, finBytes m bs off data k, none)) V -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
  unfold cfOwn
  dsimp only [thrRes]
  iintro #Hos #Hinv ⟨Hv, ⟨Hp1, Hs1⟩, Ht, %Hwf⟩ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cf_open N p R γ Good _ V _ $$ Hinv Hv Ht with ⟨Hv, Ht, Hr, Hti, Hv', %Hok', Hclose⟩
  dsimp only [invRes]
  icases Hr with ⟨Htok, Hp2, Hs2⟩
  unfold pwTok
  icases Htok with ⟨Htok, %hgap⟩
  imodintro
  iapply wp_osPWriteFinish t i off data 1 m (cfRange m bs off data.length) hN $$ Hos [Htok]
  · unfold pwTok; iframe; ipureintro; exact hgap
  iintro %k %e %hke Hm Hrg -
  have hk := hke.1
  have hlen : (finBytes m bs off data k).length = (finMeta m off data k).size :=
    finBytes_length Hwf.1.1 hk
  ihave Hm := (show osMeta (L := L) i (DFrac.own 1)
      ({ pwMeta m off data.length with size := pwSize m.size off k }) ⊢
      osMeta (L := L) i (DFrac.own 1) (finMeta m off data k) from .rfl) $$ Hm
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  have hwl := Hwf.1.1
  have hlo : 0 + (bs.take (cfLo m off)).length = min off m.size := by
    simp only [List.length_take]; unfold cfLo; omega
  have hhi : min off m.size + (pwBytes m.size off data k (cfRange m bs off data.length)).length =
      cfHi m off data.length ∨ bs.drop (cfHi m off data.length) = [] := by
    rw [pwBytes_length]
    have := pwSize_ge' m.size off k
    by_cases hs : off + data.length ≤ m.size
    · left; unfold cfHi pwSize; split <;> omega
    · right; apply List.drop_eq_nil_of_le; unfold cfHi; omega
  ihave Hb1 := osBytes_join3 i 0 (min off m.size) (cfHi m off data.length) _ _ _ _ hlo hhi
    $$ [Hp1 Hr1 Hs1]
  · iframe
  ihave Hb2 := osBytes_join3 i 0 (min off m.size) (cfHi m off data.length) _ _ _ _ hlo hhi
    $$ [Hp2 Hr2 Hs2]
  · iframe
  have hfb : ∀ dq, osBytes (L := L) i 0 dq (bs.take (cfLo m off) ++
      pwBytes m.size off data k (cfRange m bs off data.length) ++ bs.drop (cfHi m off data.length)) ⊢
      osBytes (L := L) i 0 dq (finBytes m bs off data k) := fun _ => .rfl
  ihave Hb1 := hfb _ $$ Hb1
  ihave Hb2 := hfb _ $$ Hb2
  imod ghostVar_update_halves (some (i, finMeta m off data k, finBytes m bs off data k, none)) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  have hok2 : CrashOk Good p R (some (i, finMeta m off data k, finBytes m bs off data k, none)) V :=
    ⟨treeOk_ino rfl Hok'.1, by rintro i' x hx; cases hx; exact hok k hk⟩
  have hke' : k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧ off ≤ m.size :=
    ⟨hke.1, hke.2, hgap⟩
  imod Hclose $$ %_ %V Hv' [Hm2 Hb2] Hti %hok2 with -
  · dsimp only [invRes]; iframe Hm2; iexact Hb2
  imodintro
  iapply HΦ $$ %k %e %hke'
  iframe Hv Hm1 Ht
  isplitl [Hb1]
  · iexact Hb1
  ipureintro; exact ⟨⟨hlen, Hwf.1.2⟩, Hwf.2⟩


theorem cfOwn_wf (p : GoString) (R : Roots) (γ : GName) (s : CFile) (V : Hist) :
    cfOwn (L := L) p R γ s V ⊢ ⌜CfWf s⌝ := by
  unfold cfOwn; iintro ⟨-, -, -, %h⟩; ipureintro; exact h.1

/-- The caller's part of no file at `p`. -/
theorem cfOwn_none (p : GoString) (R : Roots) (γ : GName) (V : Hist) :
    cfOwn (L := L) p R γ none V ⊢ ghostVar γ (1 : Qp).half (none : CFile) ∗
      osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜lookupH R V p = none⌝ := by
  unfold cfOwn; dsimp only [thrRes]
  iintro ⟨Hv, -, Ht, %h⟩; iframe; ipureintro; exact h.2

/-- The caller's part of the file `i` at `p`: its half of the history, lent out. -/
theorem cfOwn_tree (p : GoString) (R : Roots) (γ : GName) (i : Ino)
    (x : OsMeta × List (w8 × Bool) × Option (Nat × Nat × List w8)) (V : Hist) :
    cfOwn (L := L) p R γ (some (i, x)) V ⊢ osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗
      ⌜lookupH R V p = some (.file i)⌝ ∗
      (osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗ cfOwn (L := L) p R γ (some (i, x)) V) := by
  unfold cfOwn
  iintro ⟨Hv, Hr, Ht, %h⟩
  iframe Ht
  isplitr
  · ipureintro; exact h.2
  iintro Ht
  iframe
  ipureintro; exact h

end ops

end Perennial
