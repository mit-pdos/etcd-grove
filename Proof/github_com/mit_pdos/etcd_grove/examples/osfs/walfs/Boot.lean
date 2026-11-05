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

instance : Inhabited DirG := ⟨⟨∅, []⟩⟩

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

/-! ## The calls that change the directory, with the invariant -/

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- `unlink(2)` of `seg.tmp`, the file of `k`, the invariant opened around it. -/
theorem wp_unlinkTmp (d k : GoString) (γ : GName) (g : DirG)
    (hk : g.now !! tmpB = some (.file k)) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) d γ -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.del tmpB)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.del tmpB)))⌝ -∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d tmpB)))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%g1, %ko, >Hd1, >Hv, >%Hp, >Hk⟩
  icases osDir_agree d _ _ g g1 $$ Hd Hd1 with %heq
  subst heq
  ihave Hdw := (osDir_halves d g).2 $$ [Hd Hd1]
  · iframe
  imodintro
  iapply wp_osUnlink d tmpB k g tmpB_ok hk bootN_disj $$ Hos Hdw Hz
  iintro %e %g' %hres Hdw Hz
  icases (osDir_halves d g').1 $$ Hdw with ⟨Hd, Hd1⟩
  have hp' : NoDirs g' ∧ SegOut g' ko := by
    have hg : g' = g ∨ g' = g.push (.del tmpB) := by
      rcases hres with ⟨-, h⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
    rcases hg with rfl | rfl
    · exact Hp
    · exact ⟨noDirs_push_tmp Hp.1 _ (.inl rfl), segOut_push_tmp Hp.2 _ (.inl rfl)⟩
  imod Hclose $$ [Hd1 Hv Hk] with -
  · inext; iexists g', ko; iframe; ipureintro; exact hp'
  imodintro
  iapply HΦ $$ %e %g' %hres Hd Hz

/-- `open(2)` with `O_RDWR | O_CREAT` of `seg.tmp`, absent, the invariant opened around it. -/
theorem wp_createTmp (d : GoString) (γ : GName) (g : DirG) (hn : g.now !! tmpB = none)
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) d γ -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g -∗ osNsBusy (GF := GF) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (GF := GF) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put tmpB (.file k))) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta) ∗
            osFd (GF := GF) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∨ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put tmpB (.file k))) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d tmpB)) (#flCreat)))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%g1, %ko, >Hd1, >Hv, >%Hp, >Hk⟩
  icases osDir_agree d _ _ g g1 $$ Hd Hd1 with %heq
  subst heq
  ihave Hdw := (osDir_halves d g).2 $$ [Hd Hd1]
  · iframe
  imodintro
  iapply wp_osNsOpenCreate d tmpB g tmpB_ok hn bootN_disj $$ Hos Hdw Hz
  iintro %fd %e Hz Hr
  have hpush : ∀ k, NoDirs (g.push (.put tmpB (.file k))) ∧ SegOut (g.push (.put tmpB (.file k))) ko :=
    fun k => ⟨noDirs_push_tmp Hp.1 _ (.inr ⟨k, rfl⟩), segOut_push_tmp Hp.2 _ (.inr ⟨_, rfl⟩)⟩
  icases Hr with (⟨%he, %k, %hk, Hdw, Hm, Hfd⟩ | ⟨%he, (Hdw | ⟨%k, %hk, Hdw, Hm⟩)⟩)
  · icases (osDir_halves d _).1 $$ Hdw with ⟨Hd, Hd1⟩
    imod Hclose $$ [Hd1 Hv Hk] with -
    · inext; iexists _, ko; iframe; ipureintro; exact hpush k
    imodintro
    iapply HΦ $$ %fd %e Hz
    ileft
    isplitr
    · ipureintro; exact he
    iexists k
    iframe
    ipureintro; exact hk
  · icases (osDir_halves d _).1 $$ Hdw with ⟨Hd, Hd1⟩
    imod Hclose $$ [Hd1 Hv Hk] with -
    · inext; iexists _, ko; iframe; ipureintro; exact Hp
    imodintro
    iapply HΦ $$ %fd %e Hz
    iright
    isplitr
    · ipureintro; exact he
    ileft; iexact Hd
  · icases (osDir_halves d _).1 $$ Hdw with ⟨Hd, Hd1⟩
    imod Hclose $$ [Hd1 Hv Hk] with -
    · inext; iexists _, ko; iframe; ipureintro; exact hpush k
    imodintro
    iapply HΦ $$ %fd %e Hz
    iright
    isplitr
    · ipureintro; exact he
    iright
    iexists k
    iframe
    ipureintro; exact hk

/-- `rename(2)` of `seg.tmp`, the file of `k`, to `seg`, from no `seg` in any outcome, the
invariant (whose key is `k`) opened around it. -/
theorem wp_renameTmp (d k : GoString) (γ : GName) (g : DirG)
    (hk : g.now !! tmpB = some (.file k)) (hs : SegNone g) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) d γ -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g -∗ osNsBusy (GF := GF) true -∗
      ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.mv tmpB segB)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.mv tmpB segB)))⌝ -∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g' -∗ osNsBusy (GF := GF) false -∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d tmpB)) (#(child d segB))))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz Hγ HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%g1, %ko, >Hd1, >Hv, >%Hp, >Hk⟩
  icases osDir_agree d _ _ g g1 $$ Hd Hd1 with %heq
  subst heq
  icases ghostVar_agree _ _ _ _ _ $$ Hγ Hv with %hko
  subst hko
  ihave Hdw := (osDir_halves d g).2 $$ [Hd Hd1]
  · iframe
  have hns : g.now !! segB ≠ some .dir := (Hp.1 g.now g.crashTo_now).1
  imodintro
  iapply wp_osRename d tmpB segB k g tmpB_ok segB_ok tmp_ne_seg hk hns bootN_disj $$ Hos Hdw Hz
  iintro %e %g' %hres Hdw Hz
  icases (osDir_halves d g').1 $$ Hdw with ⟨Hd, Hd1⟩
  have hp' : NoDirs g' ∧ SegOut g' (some k) := by
    have hg : g' = g ∨ g' = g.push (.mv tmpB segB) := by
      rcases hres with ⟨-, h⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
    rcases hg with rfl | rfl
    · exact Hp
    · exact ⟨noDirs_push_mv Hp.1 hk, segOut_push_mv hs hk⟩
  imod Hclose $$ [Hd1 Hv Hk] with -
  · inext; iexists g', (some k); iframe; ipureintro; exact hp'
  imodintro
  iapply HΦ $$ %e %g' %hres Hd Hz Hγ

end steps

/-! ## The retried calls: from the state before or after the change -/

section retry
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- `unlink(2)` of `seg.tmp`, the file of `k` in `g`, from `g` or after its removal. -/
theorem wp_unlinkTmp_any (d k : GoString) (γ : GName) (g g1 : DirG)
    (hk : g.now !! tmpB = some (.file k)) (h1 : g1 = g ∨ g1 = g.push (.del tmpB))
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) d γ -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g1 -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.del tmpB)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.del tmpB)))⌝ -∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d tmpB)))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz HΦ
  rcases h1 with rfl | rfl
  · iapply wp_unlinkTmp d k γ g1 hk $$ Hos Hinv Hd Hz HΦ
  · have hn : (g.push (.del tmpB)).now !! tmpB = none := by
      rw [DirG.push_now]; exact GMap.lookup_delete_eq _ _
    iapply wp_osUnlinkAbsent d tmpB _ _ tmpB_ok hn CoPset.subseteq_top $$ Hos Hd Hz
    iintro %e %he Hd Hz
    iapply HΦ $$ %e %(g.push (.del tmpB)) %(.inr ⟨he, .inr rfl⟩) Hd Hz

/-- `rename(2)` of `seg.tmp` to `seg`, from `g` or after the rename. -/
theorem wp_renameTmp_any (d k : GoString) (γ : GName) (g g1 : DirG)
    (hk : g.now !! tmpB = some (.file k)) (hs : SegNone g)
    (h1 : g1 = g ∨ g1 = g.push (.mv tmpB segB)) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) d γ -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g1 -∗ osNsBusy (GF := GF) true -∗
      ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.mv tmpB segB)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.mv tmpB segB)))⌝ -∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g' -∗ osNsBusy (GF := GF) false -∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d tmpB)) (#(child d segB))))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz Hγ HΦ
  rcases h1 with rfl | rfl
  · iapply wp_renameTmp d k γ g1 hk hs $$ Hos Hinv Hd Hz Hγ HΦ
  · have hn : (g.push (.mv tmpB segB)).now !! tmpB = none := by
      rw [DirG.push_now]
      show (match g.now !! tmpB with
        | some n => <[segB := n]> (GMap.delete tmpB g.now)
        | none => g.now) !! tmpB = none
      rw [hk, GMap.lookup_insert_ne _ _ tmp_ne_seg.symm]; exact GMap.lookup_delete_eq _ _
    have ht : (g.push (.mv tmpB segB)).now !! segB ≠ some .dir := by
      rw [DirG.push_now]
      show (match g.now !! tmpB with
        | some n => <[segB := n]> (GMap.delete tmpB g.now)
        | none => g.now) !! segB ≠ some .dir
      rw [hk, GMap.lookup_insert_eq]; simp
    iapply wp_osRenameAbsent d tmpB segB _ _ tmpB_ok segB_ok tmp_ne_seg hn ht CoPset.subseteq_top
      $$ Hos Hd Hz
    iintro %e %he Hd Hz
    iapply HΦ $$ %e %(g.push (.mv tmpB segB)) %(.inr ⟨he, .inr rfl⟩) Hd Hz Hγ

/-- What a retried `open(2)` with `O_CREAT` of `seg.tmp` sees: `g`, or the file created (under
the key `k`, whose `OsMeta` the caller holds). -/
def crState (d : GoString) (g : DirG) : Option GoString → IProp GF
  | none => osDir (GF := GF) d (DFrac.own (1 : Qp).half) g
  | some k => iprop(⌜IsInoKey k⌝ ∗ osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put tmpB (.file k))) ∗
      osMeta (GF := GF) k (DFrac.own 1) (some newMeta))

/-- `open(2)` with `O_RDWR | O_CREAT` of `seg.tmp`, absent from `g`, from `g` or after it was
created. -/
theorem wp_createTmp_any (d : GoString) (γ : GName) (g : DirG) (hn : g.now !! tmpB = none)
    (ko : Option GoString) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ bootInv (GF := GF) d γ -∗ crState d g ko -∗ osNsBusy (GF := GF) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (GF := GF) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put tmpB (.file k))) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta) ∗
            osFd (GF := GF) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ ∃ ko', crState d g ko')) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d tmpB)) (#flCreat)))) {{ Φ }} := by
  iintro #Hos #Hinv Hs Hz HΦ
  cases ko with
  | none =>
    unfold crState
    iapply wp_createTmp d γ g hn $$ Hos Hinv Hs Hz
    iintro %fd %e Hz Hr
    iapply HΦ $$ %fd %e Hz
    icases Hr with (⟨%he, Hr⟩ | ⟨%he, (Hd | ⟨%k, %hk, Hd, Hm⟩)⟩)
    · ileft; iframe; ipureintro; exact he
    · iright; isplitr; · ipureintro; exact he
      iexists none; iexact Hd
    · iright; isplitr; · ipureintro; exact he
      iexists (some k); dsimp only; iframe; ipureintro; exact hk
  | some k =>
    unfold crState
    icases Hs with ⟨%hk, Hd, Hm⟩
    have hf : (g.push (.put tmpB (.file k))).now !! tmpB = some (.file k) := by
      rw [DirG.push_now]; exact GMap.lookup_insert_eq _ _ _
    iapply wp_osNsOpenCreatExisting d tmpB k _ _ tmpB_ok hf _ _ CoPset.subseteq_top $$ Hos Hd Hm Hz
    iintro %fd %e %hmo %hres Hd Hm Hz Hfd
    iapply HΦ $$ %fd %e Hz
    rcases hres with ⟨rfl, hfd⟩ | ⟨he, rfl⟩
    · ileft
      isplitr; · ipureintro; exact ⟨rfl, hfd⟩
      iexists k
      rw [if_pos rfl]
      iframe
      ipureintro; exact hk
    · iright
      isplitr; · ipureintro; exact ⟨he, rfl⟩
      iexists (some k)
      dsimp only
      iframe
      ipureintro; exact hk

end retry

/-! ## `os` calls on `seg.tmp` and `seg`, with the invariant -/

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.Remove(d/seg.tmp)`, `seg.tmp` the file of `k`: on success removed. -/
theorem wp_removeTmp (d k : GoString) (γ : GName) (g : DirG)
    (hk : g.now !! tmpB = some (.file k)) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) d γ ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ osNsBusy (GF := GF) false }}
      (App (Val (@! os.Remove)) (Val #(child d tmpB)))
    {{ (err : GoInterface), RET #err; osNsBusy false ∗ ∃ g',
        osDir d (DFrac.own (1 : Qp).half) g' ∗ ⌜err = interface.nil → g' = g.push (.del tmpB)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz⟩
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 = g := ⟨_, rfl⟩
  ihave Hd : osDir d (DFrac.own (1 : Qp).half) g1 $$ [Hd]
  · subst hg1; iexact Hd
  ihave Hp : ⌜g1 = g ∨ g1 = g.push (.del tmpB)⌝ $$ []
  · ipureintro; exact .inl hg1
  clear hg1
  iloeb as IH generalizing %g1 Hp Hd Hz
  icases Hp with %Hp
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_unlinkTmp_any d k γ g g1 hk Hp $$ Hos Hinv Hd Hz as %e %g' %hres Hd Hz
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    have hg' : g' = g ∨ g' = g.push (.del tmpB) := by
      rcases hres with ⟨h0, -⟩ | ⟨-, h⟩
      · exact absurd (h0 ▸ he4) (by decide)
      · exact h
    iapply IH $$ %g' [] Hd Hz HΦ
    ipureintro; exact hg'
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hz
    iexists g'
    iframe Hd
    ipureintro; intro _
    rcases hres with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd he0 h
  rw [decide_eq_false he0]
  wp_auto
  have hnd : g'.now !! tmpB ≠ some .dir := by
    have hg' : g' = g ∨ g' = g.push (.del tmpB) := by
      rcases hres with ⟨-, h⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
    rcases hg' with rfl | rfl
    · rw [hk]; simp
    · rw [DirG.push_now]; show GMap.delete tmpB g.now !! tmpB ≠ _
      rw [GMap.lookup_delete_eq]; simp
  iloeb as IH2 generalizing Hd Hz
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_osRmdirNotDir d tmpB _ g' tmpB_ok hnd CoPset.subseteq_top $$ Hos Hd Hz
    as %e1 %he1 Hd Hz
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ Hd Hz HΦ
  rw [decide_eq_false he14]
  wp_auto
  rw [decide_eq_false (show ¬ e1 = W64 0 from he1)]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe Hz
    iexists g'
    iframe Hd
    ipureintro; intro h; cases h
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe Hz
    iexists g'
    iframe Hd
    ipureintro; intro h; cases h

/-- `Regime(d/seg.tmp)` in the state of a retried create: `1`. -/
theorem wp_crState_regime (d : GoString) (g : DirG) (ko : Option GoString) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ crState d g ko -∗ (crState d g ko -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "Regime" (Val (#(child d tmpB)))) {{ Φ }} := by
  iintro #Hos Hs HΦ
  cases ko with
  | none =>
    unfold crState
    iapply wp_osRegimeNs (child d tmpB) d _ g (.inr ⟨tmpB, tmpB_ok, rfl⟩) CoPset.subseteq_top
      $$ Hos Hs HΦ
  | some k =>
    unfold crState
    icases Hs with ⟨%hk, Hd, Hm⟩
    iapply wp_osRegimeNs (child d tmpB) d _ _ (.inr ⟨tmpB, tmpB_ok, rfl⟩) CoPset.subseteq_top
      $$ Hos Hd
    iintro Hd
    iapply HΦ
    dsimp only
    iframe
    ipureintro; exact hk

/-- `os.OpenFile(d/seg.tmp, O_RDWR|O_CREATE, perm)`, `seg.tmp` absent: on success a new file of a
fresh key `k`, `seg.tmp` names it. -/
theorem wp_openTmp (d : GoString) (γ : GName) (g : DirG) (hn : g.now !! tmpB = none) (perm : w32) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) d γ ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ osNsBusy (GF := GF) false }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d tmpB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osNsBusy false ∗
        ((∃ (fd : w64) (k : GoString), ⌜err = interface.nil ∧ IsInoKey k⌝ ∗
            os.ownFile f fd (child d tmpB) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨k, true, true⟩ ∗
            osMeta k (DFrac.own 1) (some newMeta) ∗
            osDir d (DFrac.own (1 : Qp).half) (g.push (.put tmpB (.file k)))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz⟩
  obtain ⟨ko, hko⟩ : ∃ ko : Option GoString, ko = none := ⟨_, rfl⟩
  ihave Hs : crState d g ko $$ [Hd]
  · subst hko; unfold crState; iexact Hd
  clear hko
  iloeb as IH generalizing %ko Hs Hz
  wp_apply wp_crState_regime d g ko $$ Hos Hs as Hs
  rw [os.file_ty_eq, os.File_ty_eq]
  (try wp_auto)
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  rw [show (W64 66 ||| W64 524288) = flCreat from by decide]
  wp_apply wp_createTmp_any d γ g hn ko $$ Hos Hinv Hs Hz as %fd %e Hz Hr
  icases Hr with (⟨%he, %k, %hk, Hd, Hm, Hfd⟩ | ⟨%he, %ko', Hs⟩)
  · obtain ⟨rfl, -⟩ := he
    rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hz
    ileft
    iexists fd, k
    iframe Hfd Hm Hd
    isplitr
    · ipureintro; exact ⟨rfl, hk⟩
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · obtain ⟨he0, rfl⟩ := he
    rw [decide_eq_false (show ¬ e = W64 0 from he0)]
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ %ko' Hs Hz HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hz
      iright
      ipureintro; intro h; cases h

/-- `os.Rename(d/seg.tmp, d/seg)`, `seg.tmp` the file of `k`, no `seg` in any outcome, the
invariant's key `k`: on success renamed. -/
theorem wp_renameSeg (d k : GoString) (γ : GName) (g : DirG)
    (hk : g.now !! tmpB = some (.file k)) (hs : SegNone g) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) d γ ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ osNsBusy (GF := GF) false ∗
        ghostVar (GF := GF) γ (1 : Qp).half (some k) }}
      (App (App (Val (@! os.Rename)) (Val #(child d tmpB))) (Val #(child d segB)))
    {{ (err : GoInterface), RET #err; osNsBusy false ∗ ghostVar γ (1 : Qp).half (some k) ∗
        ∃ g', osDir d (DFrac.own (1 : Qp).half) g' ∗
          ⌜err = interface.nil → g' = g.push (.mv tmpB segB)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz, Hγ⟩
  have hns : g.now !! segB ≠ some .dir := by
    rw [show g.now !! segB = none from hs g.now g.crashTo_now]; simp
  wp_apply wp_osNsLstatDir d segB _ g segB_ok hns CoPset.subseteq_top $$ Hos Hd as %e0 Hd
  (try wp_auto)
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 = g := ⟨_, rfl⟩
  ihave Hd : osDir d (DFrac.own (1 : Qp).half) g1 $$ [Hd]
  · subst hg1; iexact Hd
  ihave Hp : ⌜g1 = g ∨ g1 = g.push (.mv tmpB segB)⌝ $$ []
  · ipureintro; exact .inl hg1
  clear hg1
  iloeb as IH generalizing %g1 Hp Hd Hz Hγ
  icases Hp with %Hp
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_renameTmp_any d k γ g g1 hk hs Hp $$ Hos Hinv Hd Hz Hγ as %e %g' %hres Hd Hz Hγ
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    have hg' : g' = g ∨ g' = g.push (.mv tmpB segB) := by
      rcases hres with ⟨h0, -⟩ | ⟨-, h⟩
      · exact absurd (h0 ▸ he4) (by decide)
      · exact h
    iapply IH $$ %g' [] Hd Hz Hγ HΦ
    ipureintro; exact hg'
  rw [decide_eq_false he4]
  wp_auto
  by_cases he0 : e = W64 0
  · rw [decide_eq_true he0]
    wp_auto
    iapply HΦ
    iframe Hz Hγ
    iexists g'
    iframe Hd
    ipureintro; intro _
    rcases hres with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd he0 h
  rw [decide_eq_false he0]
  wp_auto
  wp_apply wp_errno
  unfold os.model.linkError
  rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
  wp_auto
  iapply HΦ
  iframe Hz Hγ
  iexists g'
  iframe Hd
  ipureintro; intro h; cases h

end oscalls

end osfs_walfs
end EtcdGrove
end Perennial
