/-
The proofs of `examples/osfs/walfs`'s `segdir.go` (one generation): the crash invariant of the
directory `dir` and of the file its entry `seg` names, and the specs of `Boot` and its helpers.

The invariant (`bootInv`) holds half of `dir`'s ghost entry (`osDir`) and says what every crash
outcome of it may name `seg`: nothing, or the file of the key `ko`, a ghost variable whose other
half the program keeps, with half of that file's `OsMeta` and bytes, every crash of which leaves
the data (`DataGood`). Neither `seg` nor `seg.tmp` is ever a directory (`NoDirs`). The program
opens the invariant around each call that changes the directory (`unlink`, `open(O_CREAT)`,
`rename`), and before the rename deposits the new file, written and made durable, under the key
`seg.tmp` names.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs
public import Proof.os.Ns
public import Proof.os.CrashFile
public import Spec.os.File__ReadAt
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.os.File__Close
public import Spec.syscall.Fdatasync
public import Perennial.Std.Namespaces

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

/-! ## The names and the data -/

def segB : GoString := go!"seg"
def tmpB : GoString := go!"seg.tmp"

theorem segB_ok : NameOk segB := by decide
theorem tmpB_ok : NameOk tmpB := by decide
theorem tmp_ne_seg : tmpB ≠ segB := by decide

/-- The data of a committed segment (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

/-- What a crash may leave of the file `seg` names: no file, or the data. -/
def DataGood (fo : Option OsFile) : Prop := ∀ f, fo = some f → f.cur = dataC

/-! ## A directory's crash outcomes -/

/-- No crash outcome of `g` has a directory at `seg` or `seg.tmp`. -/
def NoDirs (g : DirG) : Prop :=
  ∀ e, g.CrashTo e → e !! segB ≠ some .dir ∧ e !! tmpB ≠ some .dir

/-- Every crash outcome of `g` has nothing at `seg`, or the file of the key `ko`. -/
def SegOut (g : DirG) (ko : Option GoString) : Prop :=
  ∀ e, g.CrashTo e → e !! segB = none ∨ ∃ k, ko = some k ∧ e !! segB = some (.file k)

/-- No crash outcome of `g` has anything at `seg`. -/
def SegNone (g : DirG) : Prop := ∀ e, g.CrashTo e → e !! segB = none

theorem crashTo_push_cases {g : DirG} {o : LOp} {e : Ents} (h : (g.push o).CrashTo e) :
    g.CrashTo e ∨ e = o.apply g.now := by
  obtain ⟨i, hi, rfl⟩ := h
  simp only [DirG.push, List.length_append, List.length_singleton] at hi
  by_cases hil : i ≤ g.pend.length
  · left; refine ⟨i, hil, ?_⟩
    simp only [DirG.push]; rw [List.take_append_of_le_length hil]
  · right
    have : i = g.pend.length + 1 := by omega
    subst this
    simp only [DirG.push]
    rw [show g.pend.length + 1 = (g.pend ++ [o]).length by simp, List.take_length, lreplay_snoc]
    rfl

theorem crashTo_nil {g : DirG} (hp : g.pend = []) {e : Ents} (h : g.CrashTo e) : e = g.dur := by
  obtain ⟨i, -, rfl⟩ := h
  rw [hp, List.take_nil]; rfl

theorem now_nil {g : DirG} (hp : g.pend = []) : g.now = g.dur := by
  unfold DirG.now; rw [hp]; rfl

/-- A change of `seg.tmp` leaves `seg` as it was. -/
theorem apply_tmp_seg (o : LOp) (ho : o = .del tmpB ∨ ∃ n, o = .put tmpB n) (e : Ents) :
    o.apply e !! segB = e !! segB := by
  rcases ho with rfl | ⟨n, rfl⟩
  · exact GMap.lookup_delete_ne _ tmp_ne_seg
  · exact GMap.lookup_insert_ne _ _ tmp_ne_seg

theorem noDirs_push_tmp {g : DirG} (h : NoDirs g) (o : LOp)
    (ho : o = .del tmpB ∨ ∃ k, o = .put tmpB (.file k)) : NoDirs (g.push o) := by
  intro e he
  rcases crashTo_push_cases he with he | rfl
  · exact h e he
  have hn := h g.now g.crashTo_now
  refine ⟨?_, ?_⟩
  · rw [apply_tmp_seg o (ho.imp id fun ⟨k, h⟩ => ⟨_, h⟩)]; exact hn.1
  · rcases ho with rfl | ⟨k, rfl⟩
    · show GMap.delete tmpB g.now !! tmpB ≠ _
      rw [GMap.lookup_delete_eq]; simp
    · show (<[tmpB := OsNode.file k]> g.now) !! tmpB ≠ _
      rw [GMap.lookup_insert_eq]; simp

theorem segOut_push_tmp {g : DirG} {ko : Option GoString} (h : SegOut g ko) (o : LOp)
    (ho : o = .del tmpB ∨ ∃ n, o = .put tmpB n) : SegOut (g.push o) ko := by
  intro e he
  rcases crashTo_push_cases he with he | rfl
  · exact h e he
  rw [apply_tmp_seg o ho]; exact h g.now g.crashTo_now

theorem segNone_push_tmp {g : DirG} (h : SegNone g) (o : LOp)
    (ho : o = .del tmpB ∨ ∃ n, o = .put tmpB n) : SegNone (g.push o) := by
  intro e he
  rcases crashTo_push_cases he with he | rfl
  · exact h e he
  rw [apply_tmp_seg o ho]; exact h g.now g.crashTo_now

theorem segOut_of_none {g : DirG} (h : SegNone g) (ko : Option GoString) : SegOut g ko :=
  fun e he => .inl (h e he)

/-- The rename of `seg.tmp`, the file of `k`, to `seg`, from no `seg` in any outcome. -/
theorem segOut_push_mv {g : DirG} {k : GoString} (h : SegNone g)
    (hk : g.now !! tmpB = some (.file k)) : SegOut (g.push (.mv tmpB segB)) (some k) := by
  intro e he
  rcases crashTo_push_cases he with he | rfl
  · exact .inl (h e he)
  right; refine ⟨k, rfl, ?_⟩
  show (match g.now !! tmpB with
    | some n => <[segB := n]> (GMap.delete tmpB g.now)
    | none => g.now) !! segB = _
  rw [hk]; exact GMap.lookup_insert_eq _ _ _

theorem noDirs_push_mv {g : DirG} {k : GoString} (h : NoDirs g)
    (hk : g.now !! tmpB = some (.file k)) : NoDirs (g.push (.mv tmpB segB)) := by
  intro e he
  rcases crashTo_push_cases he with he | rfl
  · exact h e he
  show (match g.now !! tmpB with
    | some n => <[segB := n]> (GMap.delete tmpB g.now)
    | none => g.now) !! segB ≠ _ ∧ (match g.now !! tmpB with
    | some n => <[segB := n]> (GMap.delete tmpB g.now)
    | none => g.now) !! tmpB ≠ _
  rw [hk]
  refine ⟨by rw [GMap.lookup_insert_eq]; simp, ?_⟩
  rw [GMap.lookup_insert_ne _ _ tmp_ne_seg.symm, GMap.lookup_delete_eq]; simp

/-! ## Crashes of the segment's file -/

/-- The new file after its write and `fdatasync`: a crash leaves the data, or no file (it is not
yet durably named: the rename and the directory's sync do that). -/
theorem synced_good (h : Nat) (ys : List (w8 × Bool)) (hys : ys.map Prod.fst = dataC) :
    ∀ fo, FileCrashedR (some (({ newMeta with size := 8, hi := h } : OsMeta).synced 0 ys))
      [(0, DFrac.own (1 : Qp).half, syncedBytes { newMeta with size := 8, hi := h } ys)] fo →
      DataGood fo := by
  have hlen : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  intro fo hfo
  rcases hfo with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hb⟩
  · intro f hf; cases hf
  intro f hf
  cases hf
  show img = dataC
  simp only [OsMeta.synced] at hlo hhi
  have hil : img.length = 8 := by
    replace hlo : 8 ≤ img.length := hlo
    replace hhi : img.length ≤ 8 := hhi
    omega
  apply List.ext_getElem?; intro i
  by_cases hi : i < 8
  · have hyi : i < ys.length := by omega
    have := hb _ (List.mem_singleton_self _) i (ys[i].1, true)
      (by simp [syncedBytes, newMeta, List.getElem?_eq_getElem hyi]) rfl
    simp only [Nat.zero_add] at this
    rw [this, ← hys, List.getElem?_map, List.getElem?_eq_getElem hyi]; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [dataC]; omega)]

/-- The file at `seg`'s key as a generation starts with it, as the invariant holds it. -/
def startMeta : Option OsFile → Option OsMeta
  | none => none
  | some f => some (initMeta f)

def startBytes : Option OsFile → List (w8 × Bool)
  | none => []
  | some f => f.cur.map (·, true)

/-- A `DataGood` file as a generation starts with it: a crash leaves it as it is. -/
theorem start_good (fo : Option OsFile) (hg : DataGood fo) :
    ∀ fo', FileCrashedR (startMeta fo) [(0, DFrac.own (1 : Qp).half, startBytes fo)] fo' →
      DataGood fo' := by
  intro fo' h
  cases fo with
  | none => cases h; intro f hf; cases hf
  | some f =>
    rcases h with ⟨-, h⟩ | ⟨img, rfl, hlo, hhi, hb⟩
    · cases h
    replace hlo : f.cur.length ≤ img.length := hlo
    replace hhi : img.length ≤ f.cur.length := hhi
    intro f' hf'
    cases hf'
    show img = dataC
    rw [← hg f rfl]
    apply List.ext_getElem?; intro k
    by_cases hk : k < f.cur.length
    · have := hb _ (List.mem_singleton_self _) k (f.cur[k], true)
        (by simp [startBytes, List.getElem?_eq_getElem hk]) rfl
      simp only [Nat.zero_add] at this
      rw [this, List.getElem?_eq_getElem hk]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## The invariant -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant's half of the file of the key `ko`: of its `OsMeta` and bytes, every crash of
which is `DataGood`. -/
def keyRes : Option GoString → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (mo : Option OsMeta) (bs : List (w8 × Bool)),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) mo ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗
      ⌜∀ fo, FileCrashedR mo [(0, DFrac.own (1 : Qp).half, bs)] fo → DataGood fo⌝)

instance osDir_timeless (d : GoString) (dq : DFrac) (g : DirG) : Timeless (osDir (L := L) d dq g) := by
  unfold osDir; infer_instance

instance keyRes_timeless (ko : Option GoString) : Timeless (keyRes (L := L) ko) := by
  cases ko <;> unfold keyRes <;> unfold osMeta osBytes bytesG <;> infer_instance

def bootN : Namespace := nroot .@ "walfs"

theorem bootN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑bootN := mask_ndot_ne' nroot "osfs" "walfs" (by decide)

/-- **The crash invariant** of the directory `d`. -/
def bootInv (d : GoString) (γ : GName) : IProp GF :=
  inv bootN iprop(∃ (g : DirG) (ko : Option GoString),
    osDir (L := L) d (DFrac.own (1 : Qp).half) g ∗ ghostVar γ (1 : Qp).half ko ∗
    ⌜NoDirs g ∧ SegOut g ko⌝ ∗ keyRes (L := L) ko)

instance bootInv_persistent (d : GoString) (γ : GName) : Persistent (bootInv (L := L) d γ) := by
  unfold bootInv; infer_instance

theorem osDir_halves (d : GoString) (g : DirG) :
    osDir (L := L) d (DFrac.own 1) g ⊣⊢
      osDir (L := L) d (DFrac.own (1 : Qp).half) g ∗ osDir (L := L) d (DFrac.own (1 : Qp).half) g := by
  have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd d (1 : Qp).half (1 : Qp).half g
  rw [Qp.half_add_half] at h
  exact h

theorem osDir_agree (d : GoString) (dq1 dq2 : DFrac) (g1 g2 : DirG) :
    ⊢ osDir (L := L) d dq1 g1 -∗ osDir (L := L) d dq2 g2 -∗ ⌜g1 = g2⌝ := by
  iintro H1 H2
  unfold osDir
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %h
  ipureintro; exact h.2

end res

/-! ## The helpers -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `readNames(d)`, with a fraction of `d`'s ghost entry `g`: the names of `g.now`, each once, or
`ok = false`. -/
theorem wp_readNames (d : GoString) (q : Qp) (g : DirG) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d (DFrac.own q) g }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readNames)) (Val #d))
    {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok); osDir d (DFrac.own q) g ∗
        (⌜ok = false⌝ ∨ ∃ names : List GoString, ⌜ok = true ∧ names.Nodup ∧
          ∀ b, b ∈ names ↔ (g.now !! b).isSome⌝ ∗ sl ↦* names) }} := by
  wp_start as ⟨#Hinv, Hd⟩
  (try wp_auto)
  wp_apply os.Open.wp_dir d (DFrac.own q) g $$ [Hinv Hd] as %f %err ⟨Hd, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | %herr)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hd
    ileft; ipureintro; rfl
  subst herr
  (try wp_auto)
  wp_apply os.File.Readdirnames.wp_dir f fd d (DFrac.own 1) d q g _ (by decide) $$ [Hinv Hf Hfd Hd]
    as %sl %err ⟨Hf, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%names, %hn, Hsl, Hfd, Hd⟩ | ⟨%herr, %rs, Hfd⟩)
  · obtain ⟨rfl, hnd, hmem⟩ := hn
    (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (d, .done) $$ [Hinv Hf Hfd] as %e -
    · iframe; iexact Hinv
    (try wp_auto)
    iapply HΦ
    iframe Hd
    iright
    iexists names
    iframe
    ipureintro; exact ⟨rfl, hnd, hmem⟩
  · (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (d, .reading rs g q) $$ [Hinv Hf Hfd] as %e Hd
    · iframe; iexact Hinv
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    simp only [rdBack, rdPart]
    unfold osDir
    iframe Hd
    ileft; itrivial

/-- `syncDir(d)`, with a fraction of `d`'s ghost entry: any result (a sync changes no ghost
state: it only narrows what a crash may leave). -/
theorem wp_syncDir (d : GoString) (dq : DFrac) (g : DirG) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.syncDir)) (Val #d))
    {{ (ok : Bool), RET #ok; osDir d dq g }} := by
  wp_start as ⟨#Hinv, Hd⟩
  (try wp_auto)
  wp_apply os.Open.wp_dir d dq g $$ [Hinv Hd] as %f %err ⟨Hd, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | %herr)
  rotate_left
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hd
  subst herr
  (try wp_auto)
  wp_apply os.File.Sync.wp_dir f fd d (DFrac.own 1) (DFrac.own 1) (d, .idle) $$ [Hinv Hf Hfd]
    as %err ⟨Hf, Hfd⟩
  · iframe; iexact Hinv
  (try wp_auto)
  wp_apply os.File.Close.wp_dir f fd d (d, .idle) $$ [Hinv Hf Hfd] as %e -
  · iframe; iexact Hinv
  cases err with
  | nil => (try wp_auto); iapply HΦ; iframe Hd
  | ok ie => (try wp_auto); iapply HΦ; iframe Hd

end proof

end osfs_walfs
end EtcdGrove
end Perennial
