/-
What `examples/osfs/walfs`'s `dirswap.go` proof takes of the segment's data (over the file
extension v2): the name `seg`, what a crash must leave of the segment's file (`DataGood`), the
invariant's and the program's halves of it (`keyRes`, `segRes`), how a generation's start splits
into them, and the specs of `dataOk`, `check(w)` (`w` any directory) and `syncDir(d)` (`d` a root).
Copied from the segdir proof's `Boot.lean` (not imported: its names would clash), `check`
generalized from a root to any directory.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSBase
public import Spec.os.File__ReadAt
public import Spec.os.File__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

def segB : GoString := go!"seg"

theorem segB_ok : NameOk segB := by decide

/-! ## The data a crash must leave -/

/-- What a crash may leave of the segment's file: no file, or the data at 0. -/
def DataGood (fo : Option OsFile) : Prop :=
  ∀ f, fo = some f → 8 ≤ f.size ∧ ∀ b < 8, f.contents[b]? = dataC[b]?

/-- What the program knows of the segment's file, held at the fractions `m`, `bs`: its first 8
bytes in the page cache are the data. -/
def CheckOk (m : OsMeta) (bs : List ByteG) : Prop :=
  8 ≤ m.size ∧ bs.length = 8 ∧ bs.map Prod.fst = dataC

/-- The data written and synced: every crash leaves it. -/
theorem synced_good (m : OsMeta) (hsz : m.size = 8) (ys : List ByteG)
    (hys : ys.map Prod.fst = dataC) :
    ∀ fo, FileCrashedR m.synced [(0, DFrac.own (1 : Qp).half, ys.map (fun x => durB x.1))] fo →
      DataGood fo := by
  intro fo hfc f hf
  subst hf
  obtain ⟨-, hlo, -, -, -⟩ := hfc f rfl
  have hl : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  have h8 : 8 ≤ f.size := by simpa [OsMeta.synced, hsz] using hlo
  refine ⟨h8, fun b hb => ?_⟩
  have hyb : b < ys.length := by omega
  rw [crashed_dur hfc (List.mem_singleton_self _) (b := b) (x := (ys[b]'hyb).1) (Nat.zero_le _)
    (by simpa using hyb) (by simp) (by omega), ← hys, List.getElem?_map,
    List.getElem?_eq_getElem hyb]; rfl

theorem newMeta_size : newMeta.size = 0 := rfl

/-- The bytes a whole write of the data leaves in a new file: the data. -/
theorem pwOut_data {ys : List ByteG} (h : os.PwOut newMeta 0 dataC 8 [] ys) :
    ys.map Prod.fst = dataC := by
  obtain ⟨hl, hv⟩ := h
  have hl8 : ys.length = 8 := by rw [hl, newMeta_size]; rfl
  apply List.ext_getElem (by simp [hl8, dataC])
  intro i h1 h2
  simp only [List.getElem_map]
  rw [(hv i (by simpa using h1)).1]
  have hi : i < 8 := by simpa [hl8] using h1
  simp only [pwByte, Nat.zero_add, if_pos hi, Nat.sub_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < dataC.length from hi), Option.getD_some]

/-- A file a crash left `DataGood`, as a new generation starts with it (`osFileStart`): its bytes'
first 8 the data, and every crash of it `DataGood` again. -/
theorem dataGood_start {f : OsFile} (h : DataGood (some f)) :
    CheckOk (initMeta f) ((f.contents.map durB).take 8) ∧
      ∀ fo, FileCrashedR (initMeta f) [(0, DFrac.own (1 : Qp).half, f.contents.map durB)] fo →
        DataGood fo := by
  obtain ⟨h8, hb⟩ := h f rfl
  refine ⟨⟨h8, by simp [contents_length]; omega, ?_⟩, ?_⟩
  · apply List.ext_getElem?
    intro b
    by_cases hb8 : b < 8
    · rw [List.getElem?_map, List.getElem?_take, if_pos hb8, List.getElem?_map, hb b hb8]
      cases dataC[b]? <;> rfl
    · rw [List.getElem?_map, List.getElem?_take, if_neg hb8]
      simp [dataC]; omega
  · intro fo hfc f' hf'
    subst hf'
    obtain ⟨-, hlo, -, -, -⟩ := hfc f' rfl
    have h8' : 8 ≤ f'.size := by have : (initMeta f).lo = f.size := rfl; omega
    refine ⟨h8', fun b hb8 => ?_⟩
    have hbl : b < (f.contents.map durB).length := by simp [contents_length]; omega
    rw [crashed_dur hfc (List.mem_singleton_self _) (b := b) (x := f.cache b) (Nat.zero_le _)
      (by simpa using hbl) (by
        have e := contents_getElem?_of_lt (f := f) (show b < f.size by omega)
        rw [List.getElem?_eq_getElem (by rw [contents_length]; omega), Option.some.injEq] at e
        simp [e])
      (by omega), ← hb b hb8, contents_getElem?_of_lt (by omega)]

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant's half of the segment's file of the key `ko`: of its `OsMeta` and bytes, every
crash of which is `DataGood`. -/
def keyRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List ByteG),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗
      ⌜∀ fo, FileCrashedR m [(0, DFrac.own (1 : Qp).half, bs)] fo → DataGood fo⌝)

instance keyRes_timeless (ko : Option Ino) : Timeless (keyRes (L := L) ko) := by
  cases ko <;> unfold keyRes <;> unfold osMeta osBytes bytesG <;> infer_instance

/-- The program's half of the segment's file of the key `ko`, as `check` needs it. -/
def segRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List ByteG),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜CheckOk m bs⌝)

/-- The segment's file of the key `ko` as a generation starts with it: `DataGood`. -/
def startFile : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ f : OsFile, ⌜DataGood (some f)⌝ ∗ osFileStart (L := L) k f)

/-- A generation's start of the segment's file, split between the invariant and the program. -/
theorem startFile_split (ko : Option Ino) :
    startFile (L := L) ko ⊢ keyRes (L := L) ko ∗ segRes (L := L) ko := by
  cases ko with
  | none => unfold startFile keyRes segRes; iintro -; isplitl [] <;> iempintro
  | some k =>
    unfold startFile keyRes segRes osFileStart
    iintro ⟨%f, %hg, Hm, Hb⟩
    obtain ⟨hck, hcr⟩ := dataGood_start hg
    icases (osMeta_halves k (initMeta f)).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves k 0 (f.contents.map durB)).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases (osBytes_take_drop' k 0 8 _ (f.contents.map durB)
        (by rw [List.length_map, contents_length]; exact hck.1)).1 $$ Hb2
      with ⟨Hb2, -⟩
    isplitl [Hm1 Hb1]
    · iexists _, _
      iframe Hm1 Hb1
      ipureintro; exact hcr
    · iexists _, _
      iframe Hm2 Hb2
      ipureintro; exact hck

end res

/-! ## `dataOk`, `check` and `syncDir` -/

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem wp_dataOk (sl : GoSlice) (dq : DFrac) (vs : List w8) (h : vs = dataC) :
    {{ (sl ↦*{dq} vs : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.dataOk)) (Val #sl))
    {{ RET #true; sl ↦*{dq} vs }} := by
  wp_start as Hs
  icases ownSlice_len sl dq vs $$ Hs with %Hlen
  have hl : vs.length = 8 := by rw [h]; rfl
  have hv : ∀ i : Nat, i < 8 → vs[i]? = dataC[i]? := by
    intro i _; rw [h]
  have hs8 : sl.len = W64 8 := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  have hs8' : (8 : Int) ≤ sint.Z sl.len := by rw [hs8]; decide
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

/-- `check(w)`, `w/seg` the file `i`, with half of its `OsMeta` and of its first 8 bytes, the data:
it does not panic. -/
theorem wp_check (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (R : Roots) (w : GoString) (V : Hist) (q : Qp) (i : Ino)
    (hl : lookupH R V (child w segB) = some (.file i))
    (m : OsMeta) (bs : List ByteG) (hok : CheckOk m bs) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V ∗
        osMeta (GF := GF) i (DFrac.own (1 : Qp).half) m ∗
        osBytes (GF := GF) i 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.check)) (Val #w))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, Ht, Hm, Hb⟩
  wp_auto
  rw [show w ++ go!"/seg" = child w segB from rfl]
  wp_apply os.OpenFile.wp_nsRO (child w segB) (W32 0) q R V i hl $$ [Hos Ht]
    as %f %err ⟨Ht, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | %herr)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  subst herr
  obtain ⟨hsz, hbl, hbv⟩ := hok
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  have h8 : sint.nat (W64 8) = 8 := rfl
  wp_apply wp_ReadAt f fd (child w segB) (DFrac.own 1) buf
      (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0) (DFrac.own 1)
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨i, true, false⟩ m bs rfl (by decide)
      (by rw [List.length_replicate, h8]; decide) (by rw [List.length_replicate, h8]; decide)
      (by rw [List.length_replicate, h8]; simp; omega)
      (by rw [List.length_replicate, h8]; exact hbl) $$ [Hos Hf Hbuf Hfd Hm Hb]
    as %n %err ⟨Hf, Hfd, Hm, Hb, %vs', Hbuf, %Hres⟩
  · iframe; iexact Hos
  (try wp_auto)
  wp_apply wp_Close f fd (child w segB) ⟨i, true, false⟩ $$ [Hos Hf Hfd] as %e -
  · iframe; iexact Hos
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | hne⟩ := Hres
  · (try wp_auto)
    wp_apply wp_dataOk buf (DFrac.own 1) vs' (by rw [hvs', hbv]) $$ [Hbuf] as Hbuf
    · iframe
    (try wp_auto)
    iapply HΦ
    itrivial
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial

/-- `syncDir(d)`, `d` the root of `j`, with a fraction of the history: any result. -/
theorem wp_syncDir (R : Roots) (hR : RootsOk R) (d : GoString) (j : Ino) (hd : (d, j) ∈ R)
    (V : Hist) (q : Qp) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.syncDir)) (Val #d))
    {{ (ok : Bool), RET #ok; osTree (DFrac.own q) R V }} := by
  wp_start as ⟨#Hinv, Ht⟩
  ihave Ht := tree_half (L := hG.goose_localGS) q R V $$ Ht
  (try wp_auto)
  wp_apply os.Open.wp_dir d q.half q.half R V j (lookupH_root hR hd V) $$ [Hinv Ht] as %f %err Hr
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Ht, Hfd⟩ | ⟨%herr, Ht⟩)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iapply tree_unhalf; iexact Ht
  subst herr
  (try wp_auto)
  wp_apply os.File.Sync.wp_dir f fd d (DFrac.own 1) (DFrac.own 1) (j, .idle (dview V j) q.half)
    $$ [Hinv Hf Hfd] as %err ⟨Hf, Hfd⟩
  · iframe; iexact Hinv
  (try wp_auto)
  wp_apply os.File.Close.wp_dir f fd d (j, .idle (dview V j) q.half) $$ [Hinv Hf Hfd] as %e Hd
  · iframe; iexact Hinv
  ihave Ht := tree_back (L := hG.goose_localGS) q.half q.half R V _ rfl $$ Ht Hd
  ihave Ht := tree_unhalf (L := hG.goose_localGS) q R V $$ Ht
  cases err with
  | nil => (try wp_auto); iapply HΦ; iframe Ht
  | ok ie => (try wp_auto); iapply HΦ; iframe Ht

end prog

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
