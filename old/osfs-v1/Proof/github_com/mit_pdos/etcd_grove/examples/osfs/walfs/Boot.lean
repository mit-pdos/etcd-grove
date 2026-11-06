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

theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {b : α}
    (hb : l[i]? = some b) : b ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
  have hji : j < i := by simp at hj; omega
  have hil : i < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have hjl : j < l.length := by omega
  have e1 : l[j] = b := by rw [← hjb, List.getElem_take]
  have e2 : l[i] = b := (List.getElem?_eq_some_iff.1 hb).2
  exact List.pairwise_iff_getElem.1 h j i hjl hil hji (e1.trans e2.symm)

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
theorem synced_good (m : OsMeta) (hok : m.ok = true) (hsz : m.size = 8) (ys : List (w8 × Bool))
    (hys : ys.map Prod.fst = dataC) :
    ∀ fo, FileCrashedR (some (m.synced 0 ys))
      [(0, DFrac.own (1 : Qp).half, syncedBytes m ys)] fo → DataGood fo := by
  have hlen : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  intro fo hfo
  rcases hfo with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hb⟩
  · intro f hf; cases hf
  intro f hf
  cases hf
  show img = dataC
  simp only [OsMeta.synced, hsz] at hlo hhi
  have hil : img.length = 8 := by
    replace hlo : 8 ≤ img.length := hlo
    replace hhi : img.length ≤ 8 := hhi
    omega
  apply List.ext_getElem?; intro i
  by_cases hi : i < 8
  · have hyi : i < ys.length := by omega
    have := hb _ (List.mem_singleton_self _) i (ys[i].1, true)
      (by simp [syncedBytes, hok, List.getElem?_eq_getElem hyi]) rfl
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
  have h : ∀ V : NsMap × List NsOp, osNsAll (L := L) (DFrac.own 1) V ⊣⊢
      osNsAll (L := L) (DFrac.own (1 : Qp).half) V ∗ osNsAll (L := L) (DFrac.own (1 : Qp).half) V := by
    intro V
    have h := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd () (1 : Qp).half (1 : Qp).half V
    rw [Qp.half_add_half] at h
    exact h
  unfold osDir
  constructor
  · iintro ⟨%V, Hh, %hg⟩
    icases (h V).1 $$ Hh with ⟨H1, H2⟩
    isplitl [H1]
    · iexists V; iframe; ipureintro; exact hg
    · iexists V; iframe; ipureintro; exact hg
  · iintro ⟨⟨%V1, H1, %hg1⟩, ⟨%V2, H2, %hg2⟩⟩
    have hval : ⊢ osNsAll (L := L) (DFrac.own (1 : Qp).half) V1 -∗
        osNsAll (L := L) (DFrac.own (1 : Qp).half) V2 -∗ ⌜V1 = V2⌝ := by
      unfold osNsAll; iintro A B
      icases gElem_valid_2 _ _ _ _ _ _ _ $$ A B with %hv
      ipureintro; exact hv.2
    icases hval $$ H1 H2 with %hv
    subst hv
    iexists V1
    isplitl [H1 H2]
    · iapply (h V1).2; iframe
    · ipureintro; exact hg1

theorem osDir_agree (d : GoString) (dq1 dq2 : DFrac) (g1 g2 : DirG) :
    ⊢ osDir (L := L) d dq1 g1 -∗ osDir (L := L) d dq2 g2 -∗ ⌜g1 = g2⌝ := by
  iintro H1 H2
  unfold osDir osNsAll
  icases H1 with ⟨%V1, H1, %hg1⟩
  icases H2 with ⟨%V2, H2, %hg2⟩
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %h
  ipureintro; rw [hg1.1, hg2.1, h.2]

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
  wp_apply os.Open.wp_dir d q g $$ [Hinv Hd] as %f %err Hr
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | ⟨%herr, Hd⟩)
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
  wp_apply os.File.Readdirnames.wp_dir f fd d (DFrac.own 1) d q g _ (by decide) $$ [Hinv Hf Hfd]
    as %sl %err ⟨Hf, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%names, %hn, Hsl, Hfd⟩ | ⟨%herr, %rs, Hfd⟩)
  · obtain ⟨rfl, hnd, hmem⟩ := hn
    (try wp_auto)
    wp_apply os.File.Close.wp_dir f fd d (d, .done g q) $$ [Hinv Hf Hfd] as %e Hd
    · iframe; iexact Hinv
    simp only [rdBack, DirPh.q, DirPh.g] at *
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
    simp only [rdBack, DirPh.q, DirPh.g] at *
    iframe Hd
    ileft; itrivial

/-- `syncDir(d)`, with a fraction of `d`'s ghost entry: any result (a sync changes no ghost
state: it only narrows what a crash may leave). -/
theorem wp_syncDir (d : GoString) (q : Qp) (g : DirG) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d (DFrac.own q) g }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.syncDir)) (Val #d))
    {{ (ok : Bool), RET #ok; osDir d (DFrac.own q) g }} := by
  wp_start as ⟨#Hinv, Hd⟩
  (try wp_auto)
  wp_apply os.Open.wp_dir d q g $$ [Hinv Hd] as %f %err Hr
  · iframe; iexact Hinv
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | ⟨%herr, Hd⟩)
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
  wp_apply os.File.Sync.wp_dir f fd d (DFrac.own 1) (DFrac.own 1) (d, .idle g q) $$ [Hinv Hf Hfd]
    as %err ⟨Hf, Hfd⟩
  · iframe; iexact Hinv
  (try wp_auto)
  wp_apply os.File.Close.wp_dir f fd d (d, .idle g q) $$ [Hinv Hf Hfd] as %e Hd
  · iframe; iexact Hinv
  simp only [rdBack, DirPh.q, DirPh.g] at *
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

/-! ## The data -/

section data
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]

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

theorem wp_newData :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.newData)) (Val #()))
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

end data

/-! ## `check`, `commit` and `Boot` -/

/-- What the program knows of the file of `seg`'s key, held at the fractions `mo`, `bs`: if it
exists, its first 8 bytes in the page cache are the data. -/
def CheckOk (mo : Option OsMeta) (bs : List (w8 × Bool)) : Prop :=
  ∀ m, mo = some m → 8 ≤ m.size ∧ bs.length = 8 ∧ bs.map Prod.fst = dataC

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- `check(d)`, `seg` the file of `k`: it does not panic. -/
theorem wp_check (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (d k : GoString) (dq : DFrac) (g : DirG) (hk : g.now !! segB = some (.file k))
    (mo : Option OsMeta) (bs : List (w8 × Bool)) (hok : CheckOk mo bs) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g ∗
        osMeta (GF := GF) k (DFrac.own (1 : Qp).half) mo ∗
        osBytes (GF := GF) k 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.check)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, Hd, Hm, Hb⟩
  wp_auto
  rw [show d ++ go!"/seg" = child d segB from rfl]
  wp_apply os.OpenFile.wp_nsRO d segB k segB_ok (W32 0) dq g hk _ mo $$ [Hos Hd Hm]
    as %f %err ⟨%hmo, Hd, Hm, Hr⟩
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
  obtain ⟨m, rfl⟩ := Option.ne_none_iff_exists'.1 hmo
  obtain ⟨hsz, hbl, hbv⟩ := hok m rfl
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  have h8 : sint.nat (W64 8) = 8 := rfl
  wp_apply wp_ReadAt f fd (child d segB) (DFrac.own 1) buf
      (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0) (DFrac.own 1)
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) ⟨k, true, false⟩ m bs rfl (by decide)
      (by rw [List.length_replicate, h8]; decide) (by rw [List.length_replicate, h8]; simp; omega)
      (by rw [List.length_replicate, h8]; exact hbl) $$ [Hos Hf Hbuf Hfd Hm Hb]
    as %n %err ⟨Hf, Hfd, Hm, Hb, %vs', Hbuf, %Hres⟩
  · iframe; iexact Hos
  (try wp_auto)
  wp_apply wp_Close f fd (child d segB) ⟨k, true, false⟩ $$ [Hos Hf Hfd] as %e -
  · iframe; iexact Hos
  obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | ⟨rfl, hne⟩⟩ := Hres
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

theorem checkOk_synced (m : OsMeta) (hok : m.ok = true) (hsz : m.size = 8) (ys : List (w8 × Bool))
    (hys : ys.map Prod.fst = dataC) : CheckOk (some (m.synced 0 ys)) (syncedBytes m ys) := by
  intro m' hm
  cases hm
  have hl : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  refine ⟨by simp [OsMeta.synced, hsz], by simp [syncedBytes, hok, hl], ?_⟩
  simp only [syncedBytes, hok, ↓reduceIte, List.map_map]
  rw [← hys]; rfl

theorem pwBytes_data : (pwBytes 0 0 dataC 8 []).map Prod.fst = dataC := by decide

/-- `commit(d)`, `seg.tmp` absent and no `seg` in any crash outcome: it does not panic. -/
theorem wp_commit (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (d : GoString) (γ : GName) (g : DirG) (ko : Option GoString)
    (hn : g.now !! tmpB = none) (hs : SegNone g) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) d γ ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ osNsBusy (GF := GF) false ∗
        ghostVar (GF := GF) γ (1 : Qp).half ko }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.commit)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz, Hγ⟩
  wp_auto
  rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl, show (W64 2 ||| W64 64) = W64 66 from by decide]
  wp_apply wp_openTmp d γ g hn (W32 438) $$ [Hos Hinv Hd Hz] as %f %err ⟨Hz, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%fd, %k, %hek, Hf, Hfd, Hm, Hd⟩ | %herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hk⟩ := hek
  (try wp_auto)
  -- the data at 0
  wp_apply wp_newData as %sl Hsl
  (try wp_auto)
  ihave Hb0 : osBytes k (min (W64 0).toNat newMeta.size) (DFrac.own 1) [] $$ []
  · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
  ihave Hmc : mcellsAny newMeta.maps (min (W64 0).toNat newMeta.size) ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny newMeta; iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_WriteAt f fd (child d tmpB) (DFrac.own 1) sl dataC (DFrac.own 1) (W64 0) (DFrac.own 1)
      ⟨k, true, true⟩ 1 newMeta [] rfl (by decide) (by decide) (by decide) (by simp [newMeta])
      (fun _ => rfl) $$ [Hos Hf Hsl Hfd Hm Hb0 Hmc]
    as %n %err ⟨Hf, Hsl, Hfd, %j, %ys, %h, %Hres, Hm, Hys, -⟩
  · iframe; iexact Hos
  obtain ⟨hj, hys, -, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d tmpB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  have hsz : pwSize newMeta.size (W64 0).toNat dataC.length = 8 := rfl
  have hys' : ys.map Prod.fst = dataC := by rw [hys]; exact pwBytes_data
  rw [show pwSize 0 0 dataC.length = 8 from rfl, show min 0 0 = 0 from rfl]
  generalize hm1 : (⟨8, 0, h, false, true, ∅, [], 0⟩ : OsMeta) = m1
  have hm1ok : m1.ok = true := by rw [← hm1]
  have hm1sz : m1.size = 8 := by rw [← hm1]
  clear hm1
  dsimp only
  (try wp_auto)
  -- `fdatasync`
  wp_apply wp_Fd f fd (child d tmpB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd (DFrac.own 1) ⟨k, true, true⟩ _ 0 ys $$ [Hos Hfd Hm Hys]
    as %e ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm, Hys⟩ | ⟨%he, -, -⟩)
  rotate_left
  · rw [show errnoErr e = interface.mkOk syscall.Errno.ty #e from if_neg he.1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child d tmpB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  subst he
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply wp_Close f fd (child d tmpB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; iexact Hos
  (try wp_auto)
  -- the file, durable, goes into the invariant under the key `k`
  icases (osMeta_halves k _).1 $$ Hm with ⟨Hm, Hmi⟩
  icases (osBytes_halves k 0 _).1 $$ Hys with ⟨Hys, Hysi⟩
  have hs1 : SegNone (g.push (.put tmpB (.file k))) := segNone_push_tmp hs _ (.inr ⟨_, rfl⟩)
  have hk1 : (g.push (.put tmpB (.file k))).now !! tmpB = some (.file k) := by
    rw [DirG.push_now]; exact GMap.lookup_insert_eq _ _ _
  iapply fupd_wp
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%g', %ko', >Hd', >Hv, >%Hp, >Hk⟩
  icases osDir_agree d _ _ _ g' $$ Hd Hd' with %heq
  subst heq
  imod ghostVar_update_halves (some k) γ _ _ $$ Hγ Hv with ⟨Hγ, Hv⟩
  imod Hclose $$ [Hd' Hv Hmi Hysi] with -
  · inext
    iexists _, (some k)
    iframe Hd' Hv
    isplitr
    · ipureintro; exact ⟨Hp.1, segOut_of_none hs1 _⟩
    unfold keyRes
    iexists _, _
    iframe Hmi Hysi
    ipureintro; exact synced_good m1 hm1ok hm1sz ys hys'
  imodintro
  -- the rename
  try rw [show d ++ go!"/seg" = child d segB from rfl]
  try rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl]
  wp_apply wp_renameSeg d k γ _ hk1 hs1 $$ [Hos Hd Hz Hγ] as %err ⟨Hz, Hγ, %g2, Hd, %hg2⟩
  · iframe; unfold bootInv; iframe #
  cases err with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  obtain rfl := hg2 rfl
  (try wp_auto)
  -- the directory's sync
  wp_apply wp_syncDir d _ _ $$ [Hos Hd] as %ok Hd
  · iframe; iexact Hos
  cases ok with
  | false =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | true =>
  (try wp_auto)
  have hk2 : ((g.push (.put tmpB (.file k))).push (.mv tmpB segB)).now !! segB = some (.file k) := by
    rw [DirG.push_now]
    show (match (g.push (.put tmpB (.file k))).now !! tmpB with
      | some n => <[segB := n]> (GMap.delete tmpB (g.push (.put tmpB (.file k))).now)
      | none => (g.push (.put tmpB (.file k))).now) !! segB = _
    rw [hk1]; exact GMap.lookup_insert_eq _ _ _
  wp_apply wp_check wp_ReadAt wp_Close d k _ _ hk2 _ _ (checkOk_synced m1 hm1ok hm1sz ys hys')
    $$ [Hos Hd Hm Hys]
  · iframe; iexact Hos
  (try wp_auto)
  iapply HΦ
  itrivial

/-- The program's half of the file of `seg`'s key `ko`, as `check` needs it. -/
def segRes : Option GoString → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (mo : Option OsMeta) (bs : List (w8 × Bool)),
      osMeta (GF := GF) k (DFrac.own (1 : Qp).half) mo ∗
      osBytes (GF := GF) k 0 (DFrac.own (1 : Qp).half) bs ∗ ⌜CheckOk mo bs⌝)

/-- `Boot(d)`, from `d`'s ghost entry `g0` with nothing in flight, the invariant's key `ko0`: it
does not panic. -/
theorem wp_Boot (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (d : GoString) (γ : GName) (g0 : DirG) (ko0 : Option GoString)
    (hp0 : g0.pend = []) (hnd : NoDirs g0) (hso : SegOut g0 ko0) :
    {{ osInv (GF := GF) ∗ bootInv (GF := GF) d γ ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g0 ∗ osNsBusy (GF := GF) false ∗
        ghostVar (GF := GF) γ (1 : Qp).half ko0 ∗ segRes ko0 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz, Hγ, Hs⟩
  wp_auto
  wp_apply wp_readNames d (1 : Qp).half g0 $$ [Hos Hd] as %sl %ok ⟨Hd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hnodup, hmem⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString) (hv : Bool) (g : DirG),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗ "Hhv" ∷ have_ptr ↦ hv ∗
      "Hd" ∷ osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ "Hz" ∷ osNsBusy (GF := GF) false ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧
        hv = decide (segB ∈ names.take (sint.nat i)) ∧
        g = (if tmpB ∈ names.take (sint.nat i) then g0.push (.del tmpB) else g0)⌝) $$ [i n «have» Hd Hz]
  · iexists W64 0, _, false, g0
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_, ?_⟩ <;> rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hhv, hg⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat i < names.length := by word
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨b, hb⟩ : ∃ b, names[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z i) names (DFrac.own 1) b hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hb
    have htake : names.take (sint.nat (i + W64 1)) = names.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [List.take_add_one, hb]; rfl
    (try wp_auto)
    have hbt0 : b ∉ names.take (sint.nat i) := not_mem_take_of_nodup hnodup hb
    by_cases hbs : b = segB
    · subst hbs
      rw [decide_eq_true (show segB = go!"seg" from rfl)]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, segB, true, g
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, ?_⟩
      · rw [htake]; simp
      · rw [htake, hg]
        simp only [List.mem_append, List.mem_singleton, tmp_ne_seg, or_false]
    rw [decide_eq_false (show ¬ b = go!"seg" from hbs)]
    wp_auto
    by_cases hbt : b = tmpB
    · subst hbt
      rw [decide_eq_true (show tmpB = go!"seg.tmp" from rfl)]
      wp_auto
      rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl]
      have hg0 : g = g0 := by rw [hg, if_neg hbt0]
      subst hg0
      obtain ⟨x, hx⟩ : ∃ x, g.now !! tmpB = some x := by
        have := (hmem tmpB).1 (List.mem_of_getElem? hb)
        cases h : g.now !! tmpB with
        | none => rw [h] at this; cases this
        | some x => exact ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k, x = .file k := by
        cases x with
        | file k => exact ⟨k, rfl⟩
        | dir => exact absurd hx (hnd g.now g.crashTo_now).2
      wp_apply wp_removeTmp d k γ g hx $$ [Hos Hinv Hd Hz] as %err ⟨Hz, %g', Hd, %hg'⟩
      · iframe; iframe #
      cases err with
      | ok ie =>
        (try wp_auto)
        wp_for_post
        iapply HΦ
        itrivial
      | nil =>
      obtain rfl := hg' rfl
      (try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1, tmpB, hv, g.push (.del tmpB)
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, ?_⟩
      · rw [htake, hhv]; simp [tmp_ne_seg, Ne.symm tmp_ne_seg]
      · rw [htake]; simp
    rw [decide_eq_false (show ¬ b = go!"seg.tmp" from hbt)]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, b, hv, g
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, ?_⟩
    · rw [htake, hhv]; simp [Ne.symm hbs]
    · rw [htake, hg]; simp [Ne.symm hbt]
  · -- the loop is done
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hhv hg
    have hnow0 : ∀ e, g0.CrashTo e → e = g0.now := fun e he => by
      rw [crashTo_nil hp0 he, now_nil hp0]
    have hseg : g.now !! segB = g0.now !! segB := by
      rw [hg]; split
      · rw [DirG.push_now]; exact apply_tmp_seg _ (.inl rfl) _
      · rfl
    subst hhv
    by_cases hsin : segB ∈ names
    · rw [decide_eq_true hsin]
      (try wp_auto)
      obtain ⟨x, hx⟩ : ∃ x, g0.now !! segB = some x := by
        have := (hmem segB).1 hsin
        cases h : g0.now !! segB with
        | none => rw [h] at this; cases this
        | some x => exact ⟨x, rfl⟩
      rcases hso g0.now g0.crashTo_now with hn | ⟨k, rfl, hk⟩
      · rw [hn] at hx; cases hx
      unfold segRes
      icases Hs with ⟨%mo, %bs, Hm, Hb, %hok⟩
      wp_apply wp_check wp_ReadAt wp_Close d k _ g (by rw [hseg]; exact hk) mo bs hok
        $$ [Hos Hd Hm Hb]
      · iframe; iexact Hos
      (try wp_auto)
      iapply HΦ
      itrivial
    · rw [decide_eq_false hsin]
      (try wp_auto)
      have hs0 : g0.now !! segB = none := by
        cases h : g0.now !! segB with
        | none => rfl
        | some x => exact absurd ((hmem segB).2 (by rw [h]; rfl)) hsin
      have hs : SegNone g := by
        have h0 : SegNone g0 := fun e he => by rw [hnow0 e he]; exact hs0
        rw [hg]; split
        · exact segNone_push_tmp h0 _ (.inl rfl)
        · exact h0
      have hn : g.now !! tmpB = none := by
        rw [hg]; split
        · rw [DirG.push_now]; exact GMap.lookup_delete_eq _ _
        · rename_i ht
          cases h : g0.now !! tmpB with
          | none => rfl
          | some x => exact absurd ((hmem tmpB).2 (by rw [h]; rfl)) ht
      wp_apply wp_commit wp_ReadAt wp_Close wp_WriteAt wp_Fd wp_Fdatasync d γ g ko0 hn hs
        $$ [Hos Hinv Hd Hz Hγ]
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial

end prog

end osfs_walfs
end EtcdGrove
end Perennial
