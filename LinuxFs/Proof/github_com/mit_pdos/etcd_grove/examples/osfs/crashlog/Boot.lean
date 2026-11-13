/-
The proofs of `examples/osfs/crashlog` (one generation): the crash invariant of the file `dir/log`
(`dir` a directory, in the roots `R`) and the specs of `Boot` and its helpers, over the file
extension v2 (`GooseLang/Ext/Fs`): the file by inode, in the directory tree.
-/
module

public import LinuxFs.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog
public import LinuxFs.Spec.os.Crash
public import LinuxFs.Proof.os.CrashWrite
public import LinuxFs.Spec.os.File__ReadAt
public import LinuxFs.Spec.os.File__Stat
public import LinuxFs.Spec.os.fileStat__Size
public import LinuxFs.Spec.os.File__Fd
public import LinuxFs.Spec.os.File__Close
public import Perennial.Std.Namespaces

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.crashlog
open Fs

/-- The data the flag guards (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

/-- The name of the file in `dir`. -/
def logB : GoString := go!"log"

theorem logB_ok : NameOk logB := by decide

/-- **The crash invariant**, of a file's contents: a nonzero flag byte (offset 8) means the data
is at offset 0. -/
def GoodImg (img : List w8) : Prop := ∀ b, img[8]? = some b → b ≠ 0 → img.take 8 = dataC

/-- The crash invariant of what a crash leaves at the path: no file, or a `GoodImg` one, of a size
an `int64` holds (as `Stat` gives it). -/
def Good : Option OsFile → Prop
  | none => True
  | some f => GoodImg f.contents ∧ f.size < 2 ^ 62

/-- The namespace of the file's invariant. -/
def logN : Namespace := nroot .@ "crashlog"

theorem take8_of {img : List w8} (h : ∀ i < 8, img[i]? = dataC[i]?) : img.take 8 = dataC := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_take]
  split
  · exact h i ‹_›
  · rw [List.getElem?_eq_none (by simp [dataC]; omega)]

theorem contents_length (f : OsFile) : f.contents.length = f.size := by simp [OsFile.contents]

/-- The first write, of the data at 0: a crash leaves no flag, or the flag as it was (durable). -/
theorem crash_W1 (m : OsMeta) (bs : List ByteG) (hhi : m.hi = m.size)
    (hlen : bs.length = m.size) (hbd : m.size < 2 ^ 62)
    (hflag : m.size ≤ 8 ∨ bs[8]? = some (durB 0)) :
    WriteOk Good m bs 0 dataC := by
  rintro f ⟨-, -, hhi', hr, -⟩
  have hhi2 : f.size ≤ max m.hi (max m.size 8) := by simpa [wT, dataC] using hhi'
  refine ⟨?_, by omega⟩
  intro b hb8 hb0
  exfalso
  have hl8 : 8 < f.size := by
    have := (List.getElem?_eq_some_iff.1 hb8).1; rw [contents_length] at this; exact this
  rcases hflag with hs | hf
  · omega
  · have hs : 8 < bs.length := (List.getElem?_eq_some_iff.1 hf).1
    rw [List.getElem?_eq_getElem hs, Option.some.injEq] at hf
    rcases hr 8 hs hl8 with ⟨s, hm⟩ | ⟨-, h2, -⟩ | ⟨-, h0⟩
    · rw [hf, List.mem_singleton] at hm
      rw [contents_getElem?_of_lt hl8, (Prod.mk.inj hm).1] at hb8
      cases hb8; exact hb0 rfl
    · simp [dataC] at h2
    · rw [contents_getElem?_of_lt hl8, h0] at hb8
      cases hb8; exact hb0 rfl

/-- A sync after the data is written: a crash leaves the data. -/
theorem crash_synced (m : OsMeta) (bs : List ByteG)
    (hlen : bs.length = m.size) (hsz : 8 ≤ m.size) (hbd : m.size < 2 ^ 62)
    (hv : ∀ i < 8, (bs[i]?).map Prod.fst = dataC[i]?) :
    FileOk Good (m.synced, bs.map (fun x => durB x.1), none) := by
  intro f hfc
  obtain ⟨-, hlo, hhi', -, -⟩ := hfc f rfl
  have h1 : f.size = m.size := by
    simp only [fMeta, OsMeta.synced] at hlo hhi'; omega
  refine ⟨?_, by omega⟩
  intro _ _ _
  apply take8_of
  intro i hi
  have hbi : i < bs.length := by omega
  have := crashed_dur hfc (r := (0, DFrac.own (1 : Qp).half, bs.map (fun x => durB x.1)))
    (by simp [fRuns]) (b := i) (x := bs[i].1) (Nat.zero_le _) (by simpa using hbi)
    (by simp) (by omega) (by simp only [fMeta, OsMeta.synced]; omega)
  rw [this, ← hv i hi, List.getElem?_eq_getElem hbi]; rfl

/-- The second write, of the flag at 8: a crash leaves the data (durable). -/
theorem crash_W2 (m : OsMeta) (bs : List ByteG) (hsz : 8 ≤ m.size) (hlo : 8 ≤ m.lo)
    (hlen : bs.length = m.size)
    (hbd : m.hi < 2 ^ 62) (hbd' : m.size < 2 ^ 62)
    (hv : ∀ i < 8, ∃ b, bs[i]? = some (durB b) ∧ dataC[i]? = some b) :
    WriteOk Good m bs 8 [W8 1] := by
  rintro f ⟨-, -, hhi', hr, -⟩
  have hhi2 : f.size ≤ max m.hi (max m.size 9) := by simpa [wT] using hhi'
  refine ⟨?_, by omega⟩
  intro b8 hb8 _
  have hl8 : 8 < f.size := by
    have := (List.getElem?_eq_some_iff.1 hb8).1; rw [contents_length] at this; exact this
  apply take8_of
  intro i hi
  obtain ⟨b, hbi, hd⟩ := hv i hi
  have hbl : i < bs.length := (List.getElem?_eq_some_iff.1 hbi).1
  rw [List.getElem?_eq_getElem hbl, Option.some.injEq] at hbi
  rcases hr i hbl (by omega) with ⟨s, hm⟩ | ⟨h1, -, -⟩ | ⟨h0, -⟩
  · rw [hbi, List.mem_singleton] at hm
    rw [contents_getElem?_of_lt (by omega), (Prod.mk.inj hm).1, hd]
  · omega
  · simp only [wT] at h0; omega

/-- A file the open creates: empty, so `Good`. -/
theorem crash_new : FileOk Good (newMeta, [], none) := by
  intro f hfc
  obtain ⟨-, -, hhi', -, -⟩ := hfc f rfl
  have h0 : f.size = 0 := by
    have : f.size ≤ 0 := by simpa [fMeta, newMeta, initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
      using hhi'
    omega
  refine ⟨?_, by omega⟩
  intro b hb
  rw [List.getElem?_eq_none (by rw [contents_length]; omega)] at hb
  cases hb

/-- A generation's file, as on disk: a crash leaves it as it was. -/
theorem crash_start (f : OsFile) (hg : Good (some f)) :
    FileOk Good (initMeta f, f.contents.map durB, none) := by
  intro f' hfc
  obtain ⟨-, hlo, hhi', -, -⟩ := hfc f' rfl
  have hs : f'.size = f.size := by simp only [fMeta, initMeta] at hlo hhi'; omega
  have hc : f'.contents = f.contents := by
    apply List.ext_getElem?; intro k
    by_cases hk : k < f.size
    · have hk' : k < f.contents.length := by rw [contents_length]; exact hk
      rw [crashed_dur hfc (r := (0, DFrac.own (1 : Qp).half, f.contents.map durB))
        (by simp [fRuns]) (b := k) (x := f.contents[k]) (Nat.zero_le _) (by simpa using hk')
        (by simp) (by omega) (by simp only [fMeta, initMeta]; omega), List.getElem?_eq_getElem hk']
    · rw [List.getElem?_eq_none (by rw [contents_length]; omega),
        List.getElem?_eq_none (by rw [contents_length]; omega)]
  exact ⟨by rw [hc]; exact hg.1, by rw [hs]; exact hg.2⟩

/-- What a generation starts with at the path: no file, or a `Good` one as on disk. -/
def StartOk (s : CFile) : Prop :=
  s = none ∨ ∃ i f, s = some (i, initMeta f, f.contents.map durB, none) ∧ Good (some f)

/-- What the boot program knows of the file once open: as on disk (or empty), `GoodImg`. -/
theorem open_facts (j : Ino) (V : Hist) (i : Ino) (s : CFile) (hs : StartOk s)
    (hi : s = none ∨ cIno s = some i) :
    ∃ m bs, (openSt j logB V i s).1 = some (i, m, bs, none) ∧ m.hi = m.size ∧
      m.size < 2 ^ 62 ∧ (∀ (k : Nat) (x : ByteG), bs[k]? = some x → x = durB x.1) ∧
      GoodImg (bs.map Prod.fst) := by
  rcases hs with rfl | ⟨i0, f, rfl, hg⟩
  · refine ⟨newMeta, [], rfl, rfl, by decide, fun k x h => by simp at h, ?_⟩
    intro b hb; simp at hb
  · have hi0 : i0 = i := by
      rcases hi with h | h
      · cases h
      · simpa [cIno] using h
    subst hi0
    refine ⟨initMeta f, f.contents.map durB, rfl, rfl, hg.2, fun k x h => ?_, ?_⟩
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at h
      obtain ⟨_, -, rfl⟩ := h; rfl
    · have e : (f.contents.map durB).map Prod.fst = f.contents := by
        rw [List.map_map]; exact List.map_id'' (fun _ => rfl) _
      rw [e]; exact hg.1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.Assumptions]

theorem wp_dataOk (sl : GoSlice) (dq : DFrac) (vs : List w8) (h : vs.take 8 = dataC) :
    {{ (sl ↦*{dq} vs : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.dataOk)) (Val #sl))
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
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.newData)) (Val #()))
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

theorem osBytes_take_drop (i : Ino) (off n : Nat) (dq : DFrac) (bs : List ByteG)
    (hn : n ≤ bs.length) :
    osBytes (GF := GF) i off dq bs ⊣⊢
      osBytes (GF := GF) i off dq (bs.take n) ∗ osBytes (GF := GF) i (off + n) dq (bs.drop n) := by
  have A := bytesG_append (gooseOsGS (L := hG.goose_localGS)) i dq off (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take, show min n bs.length = n by omega] at A
  exact A

/-- The caller's part of an idle file, unfolded. -/
theorem cfOwn_idle (p : GoString) (R : Roots) (γ : GName) (i : Ino) (m : OsMeta)
    (bs : List ByteG) (V : Hist) :
    cfOwn (GF := GF) p R γ (some (i, m, bs, none)) V ⊣⊢
      ghostVar γ (1 : Qp).half (some (i, m, bs, none) : CFile) ∗
      (osMeta (GF := GF) i (DFrac.own (1 : Qp).half) m ∗
        osBytes (GF := GF) i 0 (DFrac.own (1 : Qp).half) bs) ∗
      osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗
      ⌜CfWf (some (i, m, bs, none)) ∧ PathOk p R (some (i, m, bs, none)) V⌝ := by
  unfold cfOwn; exact .rfl

variable [os.Assumptions]

theorem wp_check (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (p : GoString) (R : Roots) (γ : GName) (i : Ino) (m : OsMeta)
    (bs : List ByteG) (V : Hist)
    (hsz : 8 < m.size) (hv : ∀ k < 8, (bs[k]?).map Prod.fst = dataC[k]?) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd p (DFrac.own 1) ∗
        osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗
        cfOwn (GF := GF) p R γ (some (i, m, bs, none)) V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.check)) (Val #f))
    {{ RET #(); os.ownFile f fd p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗
        cfOwn p R γ (some (i, m, bs, none)) V }} := by
  wp_start as ⟨#Hos, Hf, Hfd, Hown⟩
  icases (cfOwn_idle _ _ _ _ _ _ _).1 $$ Hown with ⟨Hv, ⟨Hm, Hb⟩, Ht, %Hwf⟩
  have hlen : bs.length = m.size := Hwf.1.1
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  icases (osBytes_take_drop i 0 8 _ bs (by omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  have h8 : sint.nat (W64 8) = 8 := rfl
  wp_apply wp_ReadAt f fd p (DFrac.own 1) buf (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0)
      (DFrac.own 1) (DFrac.own (1 : Qp).half)
      (DFrac.own (1 : Qp).half) ⟨i, true, true⟩ m (bs.take 8) rfl (by decide)
      (by rw [List.length_replicate, h8]; decide)
      (by rw [List.length_replicate, h8]; decide)
      (by rw [List.length_replicate, h8]; simp; omega)
      (by rw [List.length_replicate, h8, List.length_take]; omega) $$ [Hos Hf Hbuf Hfd Hm Hb8]
    as %n %err ⟨Hf, Hfd, Hm, Hb8, %vs', Hbuf, %Hres, -⟩
  · iframe; iframe #
  ihave Hb := (osBytes_take_drop i 0 8 _ bs (by omega)).2 $$ [Hb8 Hbr]
  · iframe
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | hne⟩ := Hres
  · (try wp_auto)
    have hd : vs'.take 8 = dataC := by
      apply take8_of; intro k hk
      rw [hvs', List.getElem?_map, List.getElem?_take_of_lt hk]
      exact hv k hk
    wp_apply wp_dataOk buf (DFrac.own 1) vs' hd $$ [Hbuf] as Hbuf
    · iframe
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iapply (cfOwn_idle _ _ _ _ _ _ _).2
    iframe; ipureintro; exact Hwf
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iapply (cfOwn_idle _ _ _ _ _ _ _).2
    iframe; ipureintro; exact Hwf

theorem logN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑logN := mask_ndot_ne' nroot "osfs" "crashlog" (by decide)

variable [syscall.Assumptions]

theorem wp_commit (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_WriteAtC : os.File.WriteAt.specCrash (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_FdatasyncC : syscall.Fdatasync.specCrash (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (p : GoString) (R : Roots) (γ : GName) (i : Ino) (m : OsMeta)
    (bs : List ByteG) (V : Hist)
    (hhi : m.hi = m.size) (hbd : m.size < 2 ^ 62)
    (hflag : m.size ≤ 8 ∨ bs[8]? = some (durB 0)) :
    {{ osInv (GF := GF) ∗ cfInv (GF := GF) logN p R γ Good ∗
        os.ownFile (GF := GF) f fd p (DFrac.own 1) ∗
        osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗
        cfOwn (GF := GF) p R γ (some (i, m, bs, none)) V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.commit)) (Val #f))
    {{ RET #(); os.ownFile f fd p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗
        ∃ s' V', cfOwn p R γ s' V' }} := by
  wp_start as ⟨#Hos, #Hinv, Hf, Hfd, Hown⟩
  icases (cfOwn_idle _ _ _ _ _ _ _).1 $$ Hown with ⟨Hv, Hr, Ht, %Hwf⟩
  ihave Hown := (cfOwn_idle _ _ _ _ _ _ _).2 $$ [Hv Hr Ht]
  · iframe; ipureintro; exact Hwf
  have hlen : bs.length = m.size := Hwf.1.1
  wp_auto
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  wp_apply wp_WriteAtC f fd p (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0) (DFrac.own 1)
      ⟨i, true, true⟩ logN p R γ Good m bs V rfl (by decide) (Nat.zero_le _) (by decide)
      (by decide) (by decide) logN_disj
      (crash_W1 m bs hhi hlen (by omega) hflag) $$ [Hos Hinv Hf Hsl Hfd Hown]
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
    iexists _, _; iexact Hown
  have hdl : dataC.length = 8 := rfl
  simp only [show (W64 0).toNat = 0 from rfl, Nat.zero_add, hdl] at hN1 hsz1 hv1
  (try wp_auto)
  wp_apply wp_Fd f fd p (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  -- the data made durable
  have hlen1 : bs1.length = m1.size := hN1.len
  have hbd1 : m1.size < 2 ^ 62 := by have := hN1.sz2; simp only [wT] at this; omega
  wp_apply wp_FdatasyncC fd (DFrac.own 1) ⟨i, true, true⟩ logN p R γ Good m1 bs1 V logN_disj
      (crash_synced m1 bs1 hlen1 hsz1 hbd1 hv1) $$ [Hos Hinv Hfd Hown]
    as %e ⟨Hfd, Hs⟩
  · iframe; iframe #
  icases Hs with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ; iframe Hf Hfd; iexists _, _; iexact Hown
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
  have hv2 : ∀ k < 8, ∃ b, (bs1.map (fun x => durB x.1))[k]? = some (durB b) ∧
      dataC[k]? = some b := by
    intro k hk
    have hk' : k < bs1.length := by omega
    refine ⟨bs1[k].1, by rw [List.getElem?_map, List.getElem?_eq_getElem hk']; rfl, ?_⟩
    have := hv1 k hk; rw [List.getElem?_eq_getElem hk'] at this; exact this.symm
  wp_apply wp_WriteAtC f fd p (DFrac.own 1) _ [W8 1] (DFrac.own 1) (W64 8) (DFrac.own 1)
      ⟨i, true, true⟩ logN p R γ Good m1.synced (bs1.map (fun x => durB x.1)) V rfl (by decide)
      (show 8 ≤ m1.synced.size from hsz2) (by decide) (by decide) (by decide) logN_disj
      (crash_W2 _ _ hsz2 (show 8 ≤ m1.synced.lo from hsz2) (by rw [List.length_map]; exact hlen1) (show m1.size < _ by omega)
        (show m1.size < _ by omega) hv2) $$ [Hos Hinv Hf Hsl2 Hfd Hown]
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
    iexists _, _; iexact Hown
  simp only [show (W64 8).toNat = 8 from rfl, List.length_singleton] at hN3 hsz3 hv3
  (try wp_auto)
  wp_apply wp_Fd f fd p (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  -- the flag made durable
  have hlen3 : bs3.length = m3.size := hN3.len
  have hbd3 : m3.size < 2 ^ 62 := by
    have h1 := hN3.sz2; have h2 : m1.synced.size = m1.size := rfl
    simp only [wT, List.length_singleton] at h1; omega
  have hv3' : ∀ k < 8, (bs3[k]?).map Prod.fst = dataC[k]? := by
    intro k hk
    rw [hN3.out k (.inl hk), List.getElem?_map]
    have := hv1 k hk
    cases h : bs1[k]? with
    | none => rw [h] at this; exact this
    | some x => rw [h] at this; exact this
  wp_apply wp_FdatasyncC fd (DFrac.own 1) ⟨i, true, true⟩ logN p R γ Good m3 bs3 V logN_disj
      (crash_synced m3 bs3 hlen3 (by omega) hbd3 hv3') $$ [Hos Hinv Hfd Hown]
    as %e ⟨Hfd, Hs⟩
  · iframe; iframe #
  icases Hs with (⟨%He, Hown⟩ | ⟨%He, Hown⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ; iframe Hf Hfd; iexists _, _; iexact Hown
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  -- the read back
  wp_apply (wp_slice_make2 (V := w8) (W64 9)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  icases (cfOwn_idle _ _ _ _ _ _ _).1 $$ Hown with ⟨Hv, ⟨Hm, Hb⟩, Ht, %Hwf4⟩
  have hlen4 : (bs3.map (fun x => durB x.1)).length = m3.size := by rw [List.length_map]; exact hlen3
  icases (osBytes_take_drop i 0 9 _ (bs3.map (fun x => durB x.1)) (by omega)).1 $$ Hb with ⟨Hb9, Hbr⟩
  have h9 : sint.nat (W64 9) = 9 := rfl
  wp_apply wp_ReadAt f fd p (DFrac.own 1) buf (List.replicate (sint.nat (W64 9)) (zero_val w8))
      (W64 0) (DFrac.own 1) (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨i, true, true⟩
      m3.synced ((bs3.map (fun x => durB x.1)).take 9) rfl (by decide)
      (by rw [List.length_replicate, h9]; decide)
      (by rw [List.length_replicate, h9]; decide)
      (by rw [List.length_replicate, h9]; show 0 + 9 ≤ m3.size; omega)
      (by rw [List.length_replicate, h9, List.length_take]; omega) $$ [Hos Hf Hbuf Hfd Hm Hb9]
    as %n %err ⟨Hf, Hfd, Hm, Hb9, %vs', Hbuf, %Hres, -⟩
  · iframe; iframe #
  ihave Hb := (osBytes_take_drop i 0 9 _ (bs3.map (fun x => durB x.1)) (by omega)).2 $$ [Hb9 Hbr]
  · iframe
  ihave Hown := (cfOwn_idle _ _ _ _ _ _ _).2 $$ [Hv Hm Hb Ht]
  · iframe; ipureintro; exact Hwf4
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | hne⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iexists _, _; iexact Hown
  (try wp_auto)
  have hvs : ∀ k < 9, vs'[k]? = ((bs3[k]?).map Prod.fst) := by
    intro k hk
    rw [hvs', List.getElem?_map, List.getElem?_take_of_lt hk, List.getElem?_map]
    cases bs3[k]? <;> rfl
  have hd : vs'.take 8 = dataC := by
    apply take8_of; intro k hk
    rw [hvs k (by omega)]; exact hv3' k hk
  wp_apply wp_dataOk buf (DFrac.own 1) vs' hd $$ [Hbuf] as Hbuf
  · iframe
  (try wp_auto)
  ihave %Hbl := ownSlice_len $$ Hbuf
  have hl9 : vs'.length = 9 := by rw [hl', List.length_replicate, h9]
  rw [if_pos (show 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) < sint.Z buf.len by
    rw [show sint.Z (W64 8) = 8 from rfl]
    have h1 := Hbl.1; simp only [sint.nat, sint.Z] at h1 ⊢; omega)]
  wp_apply wp_load_slice_index buf (sint.Z (W64 8)) vs' (DFrac.own 1) (W8 1) (by decide) $$ [Hbuf]
    as Hbuf
  · iframe; ipureintro
    rw [show (sint.Z (W64 8)).toNat = 8 from rfl, hvs 8 (by decide)]
    have := hv3 0 (by decide); simpa using this
  (try wp_auto)
  iapply HΦ
  iframe Hf Hfd
  iexists _, _; iexact Hown

theorem wp_run (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_WriteAtC : os.File.WriteAt.specCrash (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_FdatasyncC : syscall.Fdatasync.specCrash (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (p : GoString) (R : Roots) (γ : GName) (i : Ino) (m : OsMeta)
    (bs : List ByteG) (V : Hist)
    (hhi : m.hi = m.size) (hbd : m.size < 2 ^ 62)
    (hcl : ∀ (k : Nat) (x : ByteG), bs[k]? = some x → x = durB x.1)
    (hg : GoodImg (bs.map Prod.fst)) :
    {{ osInv (GF := GF) ∗ cfInv (GF := GF) logN p R γ Good ∗
        os.ownFile (GF := GF) f fd p (DFrac.own 1) ∗
        osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗
        cfOwn (GF := GF) p R γ (some (i, m, bs, none)) V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.run)) (Val #f))
    {{ RET #(); os.ownFile f fd p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗
        ∃ s' V', cfOwn p R γ s' V' }} := by
  wp_start as ⟨#Hos, #Hinv, Hf, Hfd, Hown⟩
  icases (cfOwn_idle _ _ _ _ _ _ _).1 $$ Hown with ⟨Hv, ⟨Hm, Hb⟩, Ht, %Hwf⟩
  have hlen : bs.length = m.size := Hwf.1.1
  wp_auto
  wp_apply wp_Stat f fd p (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half) ⟨i, true, true⟩ m
      $$ [Hos Hf Hfd Hm] as %fi %err ⟨Hf, Hfd, Hm, Hfi⟩
  · iframe; iframe #
  icases Hfi with ⟨(⟨%fs, %Hfi, Hfs⟩ | %Hfi), -, -⟩
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Hfi
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    iexists _, _; iapply (cfOwn_idle _ _ _ _ _ _ _).2; iframe; ipureintro; exact Hwf
  obtain ⟨rfl, rfl⟩ := Hfi
  (try wp_auto)
  wp_apply wp_Size fs (W64 m.size) $$ [Hfs] as -
  · iexact Hfs
  have hsZ : sint.Z (W64 (m.size : Int)) = m.size := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  (try wp_auto)
  rw [hsZ, show sint.Z (W64 8) = 8 from rfl]
  by_cases h8 : (8 : Int) < m.size
  · rw [decide_eq_true h8]
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    icases (osBytes_take_drop i 0 8 _ bs (by omega)).1 $$ Hb with ⟨Hb0, Hb8⟩
    icases (osBytes_take_drop i (0 + 8) 1 _ (bs.drop 8) (by simp; omega)).1 $$ Hb8 with ⟨Hb1, Hb9⟩
    have h1 : sint.nat (W64 1) = 1 := rfl
    wp_apply wp_ReadAt f fd p (DFrac.own 1) buf (List.replicate (sint.nat (W64 1)) (zero_val w8))
        (W64 8) (DFrac.own 1) (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨i, true, true⟩ m
        ((bs.drop 8).take 1) rfl (by decide)
        (by rw [List.length_replicate, h1]; decide)
        (by rw [List.length_replicate, h1]; decide)
        (by rw [List.length_replicate, h1]; show 8 + 1 ≤ m.size; omega)
        (by rw [List.length_replicate, h1, List.length_take, List.length_drop]; omega)
        $$ [Hos Hf Hbuf Hfd Hm Hb1]
      as %n %err ⟨Hf, Hfd, Hm, Hb1, %vs', Hbuf, %Hres, -⟩
    · iframe; iframe #
    ihave Hb8 := (osBytes_take_drop i (0 + 8) 1 _ (bs.drop 8) (by simp; omega)).2 $$ [Hb1 Hb9]
    · iframe
    ihave Hb := (osBytes_take_drop i 0 8 _ bs (by omega)).2 $$ [Hb0 Hb8]
    · iframe
    ihave Hown := (cfOwn_idle _ _ _ _ _ _ _).2 $$ [Hv Hm Hb Ht]
    · iframe; ipureintro; exact Hwf
    obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | hne⟩ := Hres
    rotate_left
    · cases err with
      | nil => exact absurd rfl hne
      | ok ie =>
      (try wp_auto)
      iapply HΦ
      iframe Hf Hfd
      iexists _, _; iexact Hown
    (try wp_auto)
    have hb8 : 8 < bs.length := by omega
    have hvs0 : vs'[0]? = some bs[8].1 := by
      rw [hvs']; simp [List.getElem?_eq_getElem hb8]
    ihave %Hbl := ownSlice_len $$ Hbuf
    have hl1 : vs'.length = 1 := by rw [hl', List.length_replicate, h1]
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z buf.len by
      rw [show sint.Z (W64 0) = 0 from rfl]
      have h1 := Hbl.1; simp only [sint.nat, sint.Z] at h1 ⊢; omega)]
    wp_apply wp_load_slice_index buf (sint.Z (W64 0)) vs' (DFrac.own 1) bs[8].1 (by decide) $$ [Hbuf]
      as Hbuf
    · iframe; ipureintro; exact hvs0
    by_cases hz : bs[8].1 = W8 0
    · -- the flag is not set: commit
      rw [hz]
      (try wp_auto)
      have hcl8 : bs[8]? = some (durB 0) := by
        rw [List.getElem?_eq_getElem hb8]
        have := hcl 8 bs[8] (List.getElem?_eq_getElem hb8)
        rw [this, hz]; rfl
      wp_apply wp_commit wp_ReadAt wp_WriteAtC wp_Fd wp_FdatasyncC f fd p R γ i m bs V hhi hbd
          (.inr hcl8) $$ [Hos Hinv Hf Hfd Hown] as ⟨Hf, Hfd, Hown⟩
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      iframe
    · -- the flag is set: the data is there
      have hv : ∀ k < 8, (bs[k]?).map Prod.fst = dataC[k]? := by
        intro k hk
        have ht := hg bs[8].1 (by simp [List.getElem?_eq_getElem hb8]) hz
        rw [← ht, List.getElem?_take_of_lt hk, List.getElem?_map]
      rw [decide_eq_false hz]
      (try wp_auto)
      wp_apply wp_check wp_ReadAt f fd p R γ i m bs V (by omega) hv $$ [Hos Hf Hfd Hown]
        as ⟨Hf, Hfd, Hown⟩
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      iframe Hf Hfd
      iexists _, _; iexact Hown
  · rw [decide_eq_false h8]
    (try wp_auto)
    ihave Hown := (cfOwn_idle _ _ _ _ _ _ _).2 $$ [Hv Hm Hb Ht]
    · iframe; ipureintro; exact Hwf
    wp_apply wp_commit wp_ReadAt wp_WriteAtC wp_Fd wp_FdatasyncC f fd p R γ i m bs V hhi hbd
        (.inl (by omega)) $$ [Hos Hinv Hf Hfd Hown] as ⟨Hf, Hfd, Hown⟩
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    iframe

/-- `Boot(dir)`, `dir` the directory `j` (in the roots `R`), the file at `dir/log` in its crash
invariant, from a start `StartOk`: it does not panic. -/
theorem wp_Boot (wp_OpenFileC : os.OpenFile.specCrash (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_WriteAtC : os.File.WriteAt.specCrash (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_FdatasyncC : syscall.Fdatasync.specCrash (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (dir : GoString) (R : Roots) (j : Ino) (γ : GName) (s : CFile) (V : Hist)
    (hdj : lookupH R V dir = some (.dir j)) (hs : StartOk s) :
    {{ osInv (GF := GF) ∗ cfInv (GF := GF) logN (child dir logB) R γ Good ∗
        cfOwn (GF := GF) (child dir logB) R γ s V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.Boot)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  wp_auto
  have hs' : s = none ∨ ∃ i m bs, s = some (i, m, bs, none) := by
    rcases hs with h | ⟨i, f, h, -⟩
    · exact .inl h
    · exact .inr ⟨_, _, _, h⟩
  rw [show (W64 2 ||| W64 64) = W64 0x42 from by decide]
  try rw [show dir ++ go!"/log" = child dir logB from rfl]
  wp_apply wp_OpenFileC dir logB _ logN R V j γ Good s logB_ok hdj hs' logN_disj
      (fun _ => crash_new) $$ [Hos Hinv Hown]
    as %f %err (⟨%fd, %i, %Herr, Hf, Hfd, Hown⟩ | ⟨%Herr, -⟩)
  · iframe; iframe #
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, hi⟩ := Herr
  (try wp_auto)
  obtain ⟨m, bs, hst, hhi, hbd, hcl, hgi⟩ := open_facts j V i s hs hi
  rw [hst]
  wp_apply wp_run wp_ReadAt wp_WriteAtC wp_Fd wp_FdatasyncC wp_Stat wp_Size f fd _ R γ i m bs _
      hhi hbd hcl hgi $$ [Hos Hinv Hf Hfd Hown] as ⟨Hf, Hfd, -⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply wp_Close f fd _ ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %_e -
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end osfs_crashlog
end EtcdGrove
end Perennial

end
