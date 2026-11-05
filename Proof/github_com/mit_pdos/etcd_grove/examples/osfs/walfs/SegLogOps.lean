/-
The proofs of `examples/osfs/walfs`'s `seglog.go` (one generation), part 1: the crash invariant
of the directory `dir` for the segment `seg.log` (no crash outcome has a directory there), the
calls that change `dir` with it opened, and the `os` calls on `dir/seg.log`: `Remove`, and
`OpenFile` (new, existing, read-only), which also give the `*File`'s offset (`os.ownOff`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot
public import Proof.os.Off

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

def logB : GoString := go!"seg.log"

theorem logB_ok : NameOk logB := by decide

/-- No crash outcome of `g` has a directory at `seg.log`. -/
def NoDirL (g : DirG) : Prop := ∀ e, g.CrashTo e → e !! logB ≠ some .dir

theorem noDirL_push {g : DirG} (h : NoDirL g) (o : LOp)
    (ho : o = .del logB ∨ ∃ k, o = .put logB (.file k)) : NoDirL (g.push o) := by
  intro e he
  rcases crashTo_push_cases he with he | rfl
  · exact h e he
  rcases ho with rfl | ⟨k, rfl⟩
  · show GMap.delete logB g.now !! logB ≠ _
    rw [GMap.lookup_delete_eq]; simp
  · show (<[logB := OsNode.file k]> g.now) !! logB ≠ _
    rw [GMap.lookup_insert_eq]; simp

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

def logN : Namespace := nroot .@ "seglog"

theorem logN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑logN := mask_ndot_ne' nroot "osfs" "seglog" (by decide)

/-- **The crash invariant** of `seglog`'s directory `d`. -/
def logInv (d : GoString) : IProp GF :=
  inv logN iprop(∃ g : DirG, osDir (L := L) d (DFrac.own (1 : Qp).half) g ∗ ⌜NoDirL g⌝)

instance logInv_persistent (d : GoString) : Persistent (logInv (L := L) d) := by
  unfold logInv; infer_instance

end res

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]

/-- `unlink(2)` of `seg.log`, the file of `k`, the invariant opened around it. -/
theorem wp_unlinkLog (d k : GoString) (g : DirG) (hk : g.now !! logB = some (.file k))
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) d -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.del logB)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.del logB)))⌝ -∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d logB)))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑logN))
  unfold logInv
  imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%g1, >Hd1, >%Hp⟩
  icases osDir_agree d _ _ g g1 $$ Hd Hd1 with %heq
  subst heq
  ihave Hdw := (osDir_halves d g).2 $$ [Hd Hd1]
  · iframe
  imodintro
  iapply wp_osUnlink d logB k g logB_ok hk logN_disj $$ Hos Hdw Hz
  iintro %e %g' %hres Hdw Hz
  icases (osDir_halves d g').1 $$ Hdw with ⟨Hd, Hd1⟩
  have hp' : NoDirL g' := by
    have hg : g' = g ∨ g' = g.push (.del logB) := by
      rcases hres with ⟨-, h⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
    rcases hg with rfl | rfl
    · exact Hp
    · exact noDirL_push Hp _ (.inl rfl)
  imod Hclose $$ [Hd1] with -
  · inext; iexists g'; iframe; ipureintro; exact hp'
  imodintro
  iapply HΦ $$ %e %g' %hres Hd Hz

/-- `open(2)` with `O_RDWR | O_CREAT` of `seg.log`, absent, the invariant opened around it. -/
theorem wp_createLog (d : GoString) (g : DirG) (hn : g.now !! logB = none) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) d -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g -∗ osNsBusy (GF := GF) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (GF := GF) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k))) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta) ∗
            osFd (GF := GF) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∨ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k))) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d logB)) (#flCreat)))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑logN))
  unfold logInv
  imod inv_acc (E := ⊤) (show ↑logN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%g1, >Hd1, >%Hp⟩
  icases osDir_agree d _ _ g g1 $$ Hd Hd1 with %heq
  subst heq
  ihave Hdw := (osDir_halves d g).2 $$ [Hd Hd1]
  · iframe
  imodintro
  iapply wp_osNsOpenCreate d logB g logB_ok hn logN_disj $$ Hos Hdw Hz
  iintro %fd %e Hz Hr
  have hpush : ∀ k, NoDirL (g.push (.put logB (.file k))) :=
    fun k => noDirL_push Hp _ (.inr ⟨k, rfl⟩)
  icases Hr with (⟨%he, %k, %hk, Hdw, Hm, Hfd⟩ | ⟨%he, (Hdw | ⟨%k, %hk, Hdw, Hm⟩)⟩)
  · icases (osDir_halves d _).1 $$ Hdw with ⟨Hd, Hd1⟩
    imod Hclose $$ [Hd1] with -
    · inext; iexists _; iframe; ipureintro; exact hpush k
    imodintro
    iapply HΦ $$ %fd %e Hz
    ileft
    isplitr
    · ipureintro; exact he
    iexists k
    iframe
    ipureintro; exact hk
  · icases (osDir_halves d _).1 $$ Hdw with ⟨Hd, Hd1⟩
    imod Hclose $$ [Hd1] with -
    · inext; iexists _; iframe; ipureintro; exact Hp
    imodintro
    iapply HΦ $$ %fd %e Hz
    iright
    isplitr
    · ipureintro; exact he
    ileft; iexact Hd
  · icases (osDir_halves d _).1 $$ Hdw with ⟨Hd, Hd1⟩
    imod Hclose $$ [Hd1] with -
    · inext; iexists _; iframe; ipureintro; exact hpush k
    imodintro
    iapply HΦ $$ %fd %e Hz
    iright
    isplitr
    · ipureintro; exact he
    iright
    iexists k
    iframe
    ipureintro; exact hk

/-- `unlink(2)` of `seg.log` from `g` or after its removal. -/
theorem wp_unlinkLog_any (d k : GoString) (g g1 : DirG)
    (hk : g.now !! logB = some (.file k)) (h1 : g1 = g ∨ g1 = g.push (.del logB))
    (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) d -∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) g1 -∗ osNsBusy (GF := GF) true -∗
      (∀ (e : w64) (g' : DirG),
        ⌜(e = 0 ∧ g' = g.push (.del logB)) ∨ (e ≠ 0 ∧ (g' = g ∨ g' = g.push (.del logB)))⌝ -∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g' -∗ osNsBusy (GF := GF) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d logB)))) {{ Φ }} := by
  iintro #Hos #Hinv Hd Hz HΦ
  rcases h1 with rfl | rfl
  · iapply wp_unlinkLog d k g1 hk $$ Hos Hinv Hd Hz HΦ
  · have hn : (g.push (.del logB)).now !! logB = none := by
      rw [DirG.push_now]; exact GMap.lookup_delete_eq _ _
    iapply wp_osUnlinkAbsent d logB _ _ logB_ok hn CoPset.subseteq_top $$ Hos Hd Hz
    iintro %e %he Hd Hz
    iapply HΦ $$ %e %(g.push (.del logB)) %(.inr ⟨he, .inr rfl⟩) Hd Hz

/-- What a retried `open(2)` with `O_CREAT` of `seg.log` sees: `g`, or the file created. -/
def crStateL (d : GoString) (g : DirG) : Option GoString → IProp GF
  | none => osDir (GF := GF) d (DFrac.own (1 : Qp).half) g
  | some k => iprop(⌜IsInoKey k⌝ ∗
      osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k))) ∗
      osMeta (GF := GF) k (DFrac.own 1) (some newMeta))

/-- `open(2)` with `O_RDWR | O_CREAT` of `seg.log`, absent from `g`, from `g` or after it was
created. -/
theorem wp_createLog_any (d : GoString) (g : DirG) (hn : g.now !! logB = none)
    (ko : Option GoString) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ logInv (GF := GF) d -∗ crStateL d g ko -∗ osNsBusy (GF := GF) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (GF := GF) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osDir (GF := GF) d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k))) ∗
            osMeta (GF := GF) k (DFrac.own 1) (some newMeta) ∗
            osFd (GF := GF) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ ∃ ko', crStateL d g ko')) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d logB)) (#flCreat)))) {{ Φ }} := by
  iintro #Hos #Hinv Hs Hz HΦ
  cases ko with
  | none =>
    unfold crStateL
    iapply wp_createLog d g hn $$ Hos Hinv Hs Hz
    iintro %fd %e Hz Hr
    iapply HΦ $$ %fd %e Hz
    icases Hr with (⟨%he, Hr⟩ | ⟨%he, (Hd | ⟨%k, %hk, Hd, Hm⟩)⟩)
    · ileft; iframe; ipureintro; exact he
    · iright; isplitr; · ipureintro; exact he
      iexists none; iexact Hd
    · iright; isplitr; · ipureintro; exact he
      iexists (some k); dsimp only; iframe; ipureintro; exact hk
  | some k =>
    unfold crStateL
    icases Hs with ⟨%hk, Hd, Hm⟩
    have hf : (g.push (.put logB (.file k))).now !! logB = some (.file k) := by
      rw [DirG.push_now]; exact GMap.lookup_insert_eq _ _ _
    iapply wp_osNsOpenCreatExisting d logB k _ _ logB_ok hf _ _ CoPset.subseteq_top $$ Hos Hd Hm Hz
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

end steps

end osfs_walfs
end EtcdGrove
end Perennial
