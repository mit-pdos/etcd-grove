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

/-- What a crash may leave of the segment's file: no file, or the data at 0, clean. -/
def DataGood (fo : Option OsFile) : Prop :=
  ∀ f, fo = some f → 8 ≤ f.size ∧ ∀ b < 8, f.contents[b]? = dataC[b]? ∧ CleanPhys f b

/-- What the program knows of the segment's file, held at the fractions `m`, `bs`: its first 8
bytes in the page cache are the data. -/
def CheckOk (m : OsMeta) (bs : List (w8 × Bool)) : Prop :=
  8 ≤ m.size ∧ bs.length = 8 ∧ bs.map Prod.fst = dataC

/-- The data written and synced: every crash leaves it, clean. -/
theorem synced_good (m : OsMeta) (hok : m.ok = true) (hsz : m.size = 8) (ys : List (w8 × Bool))
    (hys : ys.map Prod.fst = dataC) :
    ∀ fo, FileCrashedR (m.synced 0 ys) [(0, DFrac.own (1 : Qp).half, syncedBytes m ys)] fo →
      DataGood fo := by
  intro fo hfc f hf
  obtain ⟨hlo, -, hr⟩ := hfc f hf
  have hl : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  refine ⟨by simpa [OsMeta.synced, hsz] using hlo, fun b hb => ?_⟩
  have hyb : b < ys.length := by omega
  have hx : (syncedBytes m ys)[b]? = some ((ys[b]'hyb).1, true) := by
    simp [syncedBytes, hok, List.getElem?_map, List.getElem?_eq_getElem hyb]
  obtain ⟨hc, hcl⟩ := hr _ (List.mem_singleton_self _) b _ hx rfl
  simp only [Nat.zero_add] at hc hcl
  refine ⟨?_, hcl⟩
  rw [hc, ← hys, List.getElem?_map, List.getElem?_eq_getElem hyb]; rfl

theorem pwBytes_data : (pwBytes 0 0 dataC 8 []).map Prod.fst = dataC := by decide

/-- A file a crash left `DataGood`, as a new generation starts with it (`osFileStartG`): its bytes'
first 8 the data, and every crash of it `DataGood` again. -/
theorem dataGood_start {f : OsFile} (h : DataGood (some f)) :
    CheckOk (metaOf f) ((bytesOf f).take 8) ∧
      ∀ fo, FileCrashedR (metaOf f) [(0, DFrac.own (1 : Qp).half, bytesOf f)] fo → DataGood fo := by
  obtain ⟨h8, hb⟩ := h f rfl
  have hraw : ∀ b < 8, dataC[b]? = some (f.rawAt b) := by
    intro b hb8
    rw [← (hb b hb8).1]
    simp [OsFile.contents, List.getElem?_map, List.getElem?_range (show b < f.size by omega)]
  have hcl : ∀ b < 8, (bytesOf f)[b]? = some (f.rawAt b, true) := by
    intro b hb8
    simp [bytesOf, List.getElem?_map, List.getElem?_range (show b < f.size by omega),
      (hb b hb8).2]
  refine ⟨⟨h8, by simp [bytesOf]; omega, ?_⟩, ?_⟩
  · apply List.ext_getElem?
    intro b
    by_cases hb8 : b < 8
    · rw [List.getElem?_map, List.getElem?_take, if_pos hb8, hcl b hb8, hraw b hb8]; rfl
    · rw [List.getElem?_map, List.getElem?_take, if_neg hb8]
      simp [dataC]; omega
  · intro fo hfc f' hf'
    obtain ⟨hlo, -, hr⟩ := hfc f' hf'
    have hlo8 : 8 ≤ f.sizeLo := (hb 7 (by omega)).2.1
    refine ⟨by simp [metaOf] at hlo; omega, fun b hb8 => ?_⟩
    obtain ⟨hc, hcl'⟩ := hr _ (List.mem_singleton_self _) b _ (hcl b hb8) rfl
    simp only [Nat.zero_add] at hc hcl'
    exact ⟨by rw [hc, hraw b hb8], hcl'⟩

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant's half of the segment's file of the key `ko`: of its `OsMeta` and bytes, every
crash of which is `DataGood`. -/
def keyRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List (w8 × Bool)),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗
      ⌜∀ fo, FileCrashedR m [(0, DFrac.own (1 : Qp).half, bs)] fo → DataGood fo⌝)

instance keyRes_timeless (ko : Option Ino) : Timeless (keyRes (L := L) ko) := by
  cases ko <;> unfold keyRes <;> unfold osMeta osBytes bytesG <;> infer_instance

/-- The program's half of the segment's file of the key `ko`, as `check` needs it. -/
def segRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List (w8 × Bool)),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜CheckOk m bs⌝)

/-- The segment's file of the key `ko` as a generation starts with it: `DataGood`. -/
def startFile : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ f : OsFile, ⌜DataGood (some f)⌝ ∗ osFileStartG (L := L) k f)

/-- A generation's start of the segment's file, split between the invariant and the program. -/
theorem startFile_split (ko : Option Ino) :
    startFile (L := L) ko ⊢ keyRes (L := L) ko ∗ segRes (L := L) ko := by
  cases ko with
  | none => unfold startFile keyRes segRes; iintro -; isplitl [] <;> iempintro
  | some k =>
    unfold startFile keyRes segRes osFileStartG
    iintro ⟨%f, %hg, Hm, Hb⟩
    obtain ⟨hck, hcr⟩ := dataGood_start hg
    icases (osMeta_halves k (metaOf f)).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves k 0 (bytesOf f)).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases (osBytes_take_drop' k 0 8 _ (bytesOf f) (by rw [bytesOf_length]; exact hck.1)).1 $$ Hb2
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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
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
    (m : OsMeta) (bs : List (w8 × Bool)) (hok : CheckOk m bs) :
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
