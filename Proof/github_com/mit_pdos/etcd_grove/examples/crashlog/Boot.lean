/-
The proofs of `examples/crashlog` (one generation): the crash invariant of the file `dir/log`
and the specs of `Boot` and its helpers.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.crashlog
public import Spec.os.Crash
public import Spec.os.File__ReadAt
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Spec.os.File__Fd
public import Spec.os.File__Close
public import Perennial.Std.Namespaces

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.crashlog

/-- The data the flag guards (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

/-- **The crash invariant**, of a file image: a nonzero flag byte (offset 8) means the data is at
offset 0. -/
def GoodImg (img : List w8) : Prop := ∀ b, img[8]? = some b → b ≠ 0 → img.take 8 = dataC

/-- The crash invariant of what a crash leaves at the path: no file, or a `GoodImg` one. -/
def Good : Option OsFile → Prop
  | none => True
  | some f => GoodImg f.cur

/-- The namespace of the file's invariant. -/
def logN : Namespace := nroot .@ "crashlog"

theorem take8_of {img : List w8} (h : ∀ i < 8, img[i]? = dataC[i]?) : img.take 8 = dataC := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_take]
  split
  · exact h i ‹_›
  · rw [List.getElem?_eq_none (by simp [dataC]; omega)]

/-- The first write, of the data at 0: a crash leaves no flag, or the flag as it was (clean). -/
theorem crash_W1 (m : OsMeta) (bs : List (w8 × Bool)) (hhi : m.hi = m.size)
    (hlen : bs.length = m.size) (hflag : m.size ≤ 8 ∨ bs[8]? = some (0, true)) :
    CrashOk Good (cfWriting m bs 0 dataC) := by
  intro fo h
  rcases h with ⟨rfl, -⟩ | ⟨img, rfl, -, hhi', hb⟩
  · trivial
  change GoodImg img
  intro b hb8 hb0
  exfalso
  have hl8 : 8 < img.length := (List.getElem?_eq_some_iff.1 hb8).1
  simp only [pwMeta, dataC, List.length] at hhi'
  rcases hflag with hs | hf
  · omega
  · have hs : 8 < m.size := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hf).1
    have hcf : cfHi m 0 dataC.length = 8 := by unfold cfHi; simp [dataC]; omega
    have := hb _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) 0 (0, true)
      (by simp only [List.getElem?_drop, hcf, Nat.add_zero]; exact hf) rfl
    simp only [hcf, Nat.add_zero] at this
    rw [this] at hb8
    cases hb8
    exact hb0 rfl

/-- A sync after the data is written: a crash leaves the data. -/
theorem crash_synced (m : OsMeta) (bs : List (w8 × Bool)) (hok : m.ok = true)
    (hlen : bs.length = m.size) (hsz : 8 ≤ m.size) (hv : ∀ i < 8, (bs[i]?).map Prod.fst = dataC[i]?) :
    CrashOk Good (some (m.synced, syncedBytes m bs, none)) := by
  intro fo h
  rcases h with ⟨rfl, -⟩ | ⟨img, rfl, -, -, hb⟩
  · trivial
  change GoodImg img
  intro _ _ _
  apply take8_of
  intro i hi
  have hbi : i < bs.length := by omega
  have := hb _ (List.mem_singleton_self _) i (bs[i].1, true)
    (by simp [syncedBytes, hok, List.getElem?_eq_getElem hbi]) rfl
  simp only [Nat.zero_add] at this
  rw [this, ← hv i hi, List.getElem?_eq_getElem hbi]; rfl

/-- The second write, of the flag at 8: a crash leaves the data (clean). -/
theorem crash_W2 (m : OsMeta) (bs : List (w8 × Bool)) (hsz : 8 ≤ m.size)
    (hv : ∀ i < 8, ∃ b, bs[i]? = some (b, true) ∧ dataC[i]? = some b) :
    CrashOk Good (cfWriting m bs 8 [W8 1]) := by
  intro fo h
  rcases h with ⟨rfl, -⟩ | ⟨img, rfl, -, -, hb⟩
  · trivial
  change GoodImg img
  intro _ _ _
  apply take8_of
  intro i hi
  obtain ⟨b, hbi, hd⟩ := hv i hi
  have := hb _ List.mem_cons_self i (b, true)
    (by rw [List.getElem?_take_of_lt (by unfold cfLo; omega)]; exact hbi) rfl
  simp only [Nat.zero_add] at this
  rw [this, hd]

/-- A generation's file, opened: a crash leaves it as it was, or no file. -/
theorem crash_open (fo : Option OsFile) (hg : Good fo) : CrashOk Good (openState (startState fo)) := by
  intro fo' h
  cases fo with
  | none =>
    rcases h with ⟨rfl, -⟩ | ⟨img, rfl, -, hhi, -⟩
    · trivial
    have h0 : img.length ≤ 0 := hhi
    have : img = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    change GoodImg []
    intro b hb; simp at hb
  | some f =>
    rcases h with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hb⟩
    · trivial
    replace hlo : f.cur.length ≤ img.length := hlo
    replace hhi : img.length ≤ f.cur.length := hhi
    have : img = f.cur := by
      apply List.ext_getElem?; intro k
      by_cases hk : k < f.cur.length
      · have := hb _ (List.mem_singleton_self _) k (f.cur[k], true)
          (by simp [List.getElem?_eq_getElem hk]) rfl
        simp only [Nat.zero_add] at this
        rw [this, List.getElem?_eq_getElem hk]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    subst this
    exact hg

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.crashlog.Assumptions]

theorem wp_dataOk (sl : GoSlice) (dq : DFrac) (vs : List w8) (h : vs.take 8 = dataC) :
    {{ (sl ↦*{dq} vs : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.crashlog.dataOk)) (Val #sl))
    {{ RET #true; sl ↦*{dq} vs }} := by
  wp_start as Hs
  icases ownSlice_len sl dq vs $$ Hs with %Hlen
  have hl : 8 ≤ vs.length := by
    have := congrArg List.length h; simp [dataC] at this; omega
  have hv : ∀ i : Nat, i < 8 → vs[i]? = dataC[i]? := by
    intro i hi
    rw [← h, List.getElem?_take_of_lt hi]
  have hs8' : (8 : Int) ≤ sint.Z sl.len := by
    have h1 := Hlen.1; simp only [sint.nat, sint.Z] at h1 ⊢; omega
  have hs8 : sint.Z (W64 8) ≤ sint.Z sl.len := by
    rw [show sint.Z (W64 8) = 8 from rfl]; exact hs8'
  try wp_auto
  rw [decide_eq_true hs8]
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) vs dq (W8 0xde) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 0)).toNat = 0 from rfl]; exact hv 0 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 1)) vs dq (W8 0xad) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 1)).toNat = 1 from rfl]; exact hv 1 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z sl.len by
    rw [show sint.Z (W64 2) = 2 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 2)) vs dq (W8 0xbe) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 2)).toNat = 2 from rfl]; exact hv 2 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z sl.len by
    rw [show sint.Z (W64 3) = 3 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 3)) vs dq (W8 0xef) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 3)).toNat = 3 from rfl]; exact hv 3 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) < sint.Z sl.len by
    rw [show sint.Z (W64 4) = 4 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 4)) vs dq (W8 0x01) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 4)).toNat = 4 from rfl]; exact hv 4 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) < sint.Z sl.len by
    rw [show sint.Z (W64 5) = 5 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 5)) vs dq (W8 0x23) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 5)).toNat = 5 from rfl]; exact hv 5 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 6) ∧ sint.Z (W64 6) < sint.Z sl.len by
    rw [show sint.Z (W64 6) = 6 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 6)) vs dq (W8 0x45) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 6)).toNat = 6 from rfl]; exact hv 6 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) < sint.Z sl.len by
    rw [show sint.Z (W64 7) = 7 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 7)) vs dq (W8 0x67) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 7)).toNat = 7 from rfl]; exact hv 7 (by decide)
  try wp_auto
  iapply HΦ
  iframe

theorem wp_newData :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.crashlog.newData)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* dataC }} := by
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal (V := w8) (l := dataC)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hs, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd]
  (try wp_auto)
  iapply HΦ
  iexact Hs

theorem osBytes_take_drop (p : GoString) (off n : Nat) (dq : DFrac) (bs : List (w8 × Bool))
    (hn : n ≤ bs.length) :
    osBytes (GF := GF) p off dq bs ⊣⊢
      osBytes (GF := GF) p off dq (bs.take n) ∗ osBytes (GF := GF) p (off + n) dq (bs.drop n) := by
  have A := bytesG_append (gooseOsGS (L := hG.goose_localGS)) p dq off (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take, show min n bs.length = n by omega] at A
  exact A

variable [os.Assumptions]

theorem wp_check (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (p : GoString) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool))
    (hsz : 8 < m.size) (hv : ∀ i < 8, (bs[i]?).map Prod.fst = dataC[i]?) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd p (DFrac.own 1) ∗
        osFd (GF := GF) fd (DFrac.own 1) ⟨p, true, true⟩ ∗ cfOwn (GF := GF) p γ (some (m, bs, none)) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.crashlog.check)) (Val #f))
    {{ RET #(); os.ownFile f fd p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨p, true, true⟩ ∗
        cfOwn p γ (some (m, bs, none)) }} := by
  wp_start as ⟨#Hos, Hf, Hfd, Hown⟩
  icases (cfOwn_idle _ _ _ _).1 $$ Hown with ⟨Hv, ⟨Hm, Hb⟩, %Hwf⟩
  have hlen : bs.length = m.size := Hwf.1
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  icases (osBytes_take_drop p 0 8 _ bs (by omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  have h8 : sint.nat (W64 8) = 8 := rfl
  wp_apply wp_ReadAt f fd p (DFrac.own 1) buf (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0)
      (DFrac.own 1) (DFrac.own (1 : Qp).half)
      (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ m (bs.take 8) rfl (by decide)
      (by rw [List.length_replicate, h8]; decide) (by rw [List.length_replicate, h8]; simp; omega)
      (by rw [List.length_replicate, h8, List.length_take]; omega) $$ [Hos Hf Hbuf Hfd Hm Hb8]
    as %n %err ⟨Hf, Hfd, Hm, Hb8, %vs', Hbuf, %Hres⟩
  · iframe; iframe #
  ihave Hb := (osBytes_take_drop p 0 8 _ bs (by omega)).2 $$ [Hb8 Hbr]
  · iframe
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | ⟨rfl, hne⟩⟩ := Hres
  · (try wp_auto)
    have hd : vs'.take 8 = dataC := by
      apply take8_of; intro i hi
      rw [hvs', List.getElem?_map, List.getElem?_take_of_lt hi]
      exact hv i hi
    wp_apply wp_dataOk buf (DFrac.own 1) vs' hd $$ [Hbuf] as Hbuf
    · iframe
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iapply (cfOwn_idle _ _ _ _).2
    iframe; ipureintro; exact Hwf
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iapply (cfOwn_idle _ _ _ _).2
    iframe; ipureintro; exact Hwf

theorem cfOwn_wf (p : GoString) (γ : GName) (s : CFile) :
    cfOwn (GF := GF) p γ s ⊢ ⌜CfWf s⌝ := by
  unfold cfOwn; iintro ⟨-, -, %h⟩; ipureintro; exact h

theorem logN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑logN := mask_ndot_ne' nroot "osfs" "crashlog" (by decide)

theorem syncedBytes_fst (m : OsMeta) (bs : List (w8 × Bool)) (i : Nat) :
    ((syncedBytes m bs)[i]?).map Prod.fst = (bs[i]?).map Prod.fst := by
  unfold syncedBytes; split
  · rw [List.getElem?_map]; cases bs[i]? <;> rfl
  · rfl

theorem syncedBytes_clean (m : OsMeta) (bs : List (w8 × Bool)) (hok : m.ok = true) (i : Nat)
    (hi : i < bs.length) : (syncedBytes m bs)[i]? = some (bs[i].1, true) := by
  simp [syncedBytes, hok, List.getElem?_eq_getElem hi]

theorem wp_commit (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_WriteAtC : os.File.WriteAt.specCrash (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_FdatasyncC : syscall.Fdatasync.specCrash (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (p : GoString) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool))
    (hhi : m.hi = m.size) (hok : m.ok = true) (hflag : m.size ≤ 8 ∨ bs[8]? = some (0, true)) :
    {{ osInv (GF := GF) ∗ cfInv (GF := GF) logN p γ Good ∗ os.ownFile (GF := GF) f fd p (DFrac.own 1) ∗
        osFd (GF := GF) fd (DFrac.own 1) ⟨p, true, true⟩ ∗ cfOwn (GF := GF) p γ (some (m, bs, none)) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.crashlog.commit)) (Val #f))
    {{ RET #(); os.ownFile f fd p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨p, true, true⟩ ∗
        ∃ s', cfOwn p γ s' }} := by
  wp_start as ⟨#Hos, #Hinv, Hf, Hfd, Hown⟩
  icases cfOwn_wf _ _ _ $$ Hown with %Hwf
  have hlen : bs.length = m.size := Hwf.1
  wp_auto
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  wp_apply wp_WriteAtC f fd p (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0) (DFrac.own 1)
      ⟨p, true, true⟩ logN γ Good m bs rfl (by decide) (by decide) (by decide) logN_disj
      (crash_W1 m bs hhi hlen hflag) $$ [Hos Hinv Hf Hsl Hfd Hown]
    as %n %err ⟨Hf, Hsl, Hfd, %m1, %bs1, %Hres, Hown⟩
  · iframe; iframe #
  obtain ⟨hN1, ⟨rfl, rfl, hsz1, hv1⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iexists _; iexact Hown
  have hdl : dataC.length = 8 := rfl
  simp only [show (W64 0).toNat = 0 from rfl, Nat.zero_add, hdl] at hN1 hsz1 hv1
  (try wp_auto)
  wp_apply wp_Fd f fd p (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  -- the data made durable
  have hok1 : m1.ok = true := hN1.ok.trans hok
  have hlen1 : bs1.length = m1.size := hN1.len
  wp_apply wp_FdatasyncC fd (DFrac.own 1) ⟨p, true, true⟩ logN γ Good m1 bs1 logN_disj
      (crash_synced m1 bs1 hok1 hlen1 hsz1 hv1) $$ [Hos Hinv Hfd Hown]
    as %e ⟨Hfd, Hs⟩
  · iframe; iframe #
  icases Hs with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ; iframe Hf Hfd; iexists _; iexact Hown
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  -- the flag at 8
  wp_apply wp_slice_literal (V := w8) (l := [W8 1])
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd]
  (try wp_auto)
  have hsz2 : 8 ≤ m1.synced.size := hsz1
  have hv2 : ∀ i < 8, ∃ b, (syncedBytes m1 bs1)[i]? = some (b, true) ∧ dataC[i]? = some b := by
    intro i hi
    have hi' : i < bs1.length := by omega
    refine ⟨bs1[i].1, syncedBytes_clean m1 bs1 hok1 i hi', ?_⟩
    have := hv1 i hi; rw [List.getElem?_eq_getElem hi'] at this; exact this.symm
  wp_apply wp_WriteAtC f fd p (DFrac.own 1) _ [W8 1] (DFrac.own 1) (W64 8) (DFrac.own 1)
      ⟨p, true, true⟩ logN γ Good m1.synced (syncedBytes m1 bs1) rfl (by decide) (by decide)
      (by decide) logN_disj (crash_W2 _ _ hsz2 hv2) $$ [Hos Hinv Hf Hsl2 Hfd Hown]
    as %n2 %err2 ⟨Hf, Hsl2, Hfd, %m3, %bs3, %Hres, Hown⟩
  · iframe; iframe #
  obtain ⟨hN3, ⟨rfl, rfl, hsz3, hv3⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err2 with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iexists _; iexact Hown
  simp only [show (W64 8).toNat = 8 from rfl, List.length_singleton] at hN3 hsz3 hv3
  (try wp_auto)
  wp_apply wp_Fd f fd p (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  -- the flag made durable
  have hok3 : m3.ok = true := hN3.ok.trans hok1
  have hlen3 : bs3.length = m3.size := hN3.len
  have hv3' : ∀ i < 8, (bs3[i]?).map Prod.fst = dataC[i]? := by
    intro i hi
    rw [hN3.pre i (by unfold cfLo; show i < min 8 m1.size; omega), syncedBytes_fst]
    exact hv1 i hi
  wp_apply wp_FdatasyncC fd (DFrac.own 1) ⟨p, true, true⟩ logN γ Good m3 bs3 logN_disj
      (crash_synced m3 bs3 hok3 hlen3 (by omega) hv3') $$ [Hos Hinv Hfd Hown]
    as %e ⟨Hfd, Hs⟩
  · iframe; iframe #
  icases Hs with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ; iframe Hf Hfd; iexists _; iexact Hown
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  -- the read back
  wp_apply (wp_slice_make2 (V := w8) (W64 9)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  icases (cfOwn_idle _ _ _ _).1 $$ Hown with ⟨Hv, ⟨Hm, Hb⟩, %Hwf4⟩
  have hlen4 : (syncedBytes m3 bs3).length = m3.size := by rw [syncedBytes_length]; exact hlen3
  icases (osBytes_take_drop p 0 9 _ (syncedBytes m3 bs3) (by omega)).1 $$ Hb with ⟨Hb9, Hbr⟩
  have h9 : sint.nat (W64 9) = 9 := rfl
  wp_apply wp_ReadAt f fd p (DFrac.own 1) buf (List.replicate (sint.nat (W64 9)) (zero_val w8)) (W64 0)
      (DFrac.own 1) (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ m3.synced
      ((syncedBytes m3 bs3).take 9) rfl (by decide)
      (by rw [List.length_replicate, h9]; decide)
      (by rw [List.length_replicate, h9]; show 0 + 9 ≤ m3.size; omega)
      (by rw [List.length_replicate, h9, List.length_take]; omega) $$ [Hos Hf Hbuf Hfd Hm Hb9]
    as %n %err ⟨Hf, Hfd, Hm, Hb9, %vs', Hbuf, %Hres⟩
  · iframe; iframe #
  ihave Hb := (osBytes_take_drop p 0 9 _ (syncedBytes m3 bs3) (by omega)).2 $$ [Hb9 Hbr]
  · iframe
  ihave Hown := (cfOwn_idle _ _ _ _).2 $$ [Hv Hm Hb]
  · iframe; ipureintro; exact Hwf4
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iexists _; iexact Hown
  (try wp_auto)
  have hvs : ∀ i < 9, vs'[i]? = ((bs3[i]?).map Prod.fst) := by
    intro i hi
    rw [hvs', List.getElem?_map, List.getElem?_take_of_lt hi, syncedBytes_fst]
  have hd : vs'.take 8 = dataC := by
    apply take8_of; intro i hi
    rw [hvs i (by omega)]; exact hv3' i hi
  wp_apply wp_dataOk buf (DFrac.own 1) vs' hd $$ [Hbuf] as Hbuf
  · iframe
  (try wp_auto)
  ihave %Hbl := ownSlice_len $$ Hbuf
  have hl9 : vs'.length = 9 := by rw [hl', List.length_replicate, h9]
  rw [if_pos (show 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) < sint.Z buf.len by
    rw [show sint.Z (W64 8) = 8 from rfl]
    have h1 := Hbl.1; simp only [sint.nat, sint.Z] at h1 ⊢; omega)]
  wp_apply wp_load_slice_index buf (sint.Z (W64 8)) vs' (DFrac.own 1) (W8 1) (by decide) $$ [Hbuf] as Hbuf
  · iframe; ipureintro
    rw [show (sint.Z (W64 8)).toNat = 8 from rfl, hvs 8 (by decide)]
    have := hv3 0 (by decide); simpa using this
  (try wp_auto)
  iapply HΦ
  iframe Hf Hfd
  iexists _; iexact Hown

end proof

end crashlog
end EtcdGrove
end Perennial
