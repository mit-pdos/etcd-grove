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

/-! ## `os` calls on `seg.log` -/

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.Remove(d/seg.log)`, `seg.log` the file of `k`: on success removed. -/
theorem wp_removeLog (d k : GoString) (g : DirG)
    (hk : g.now !! logB = some (.file k)) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) d ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ osNsBusy (GF := GF) false }}
      (App (Val (@! os.Remove)) (Val #(child d logB)))
    {{ (err : GoInterface), RET #err; osNsBusy false ∗ ∃ g',
        osDir d (DFrac.own (1 : Qp).half) g' ∗ ⌜err = interface.nil → g' = g.push (.del logB)⌝ }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz⟩
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 = g := ⟨_, rfl⟩
  ihave Hd : osDir d (DFrac.own (1 : Qp).half) g1 $$ [Hd]
  · subst hg1; iexact Hd
  ihave Hp : ⌜g1 = g ∨ g1 = g.push (.del logB)⌝ $$ []
  · ipureintro; exact .inl hg1
  clear hg1
  iloeb as IH generalizing %g1 Hp Hd Hz
  icases Hp with %Hp
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_unlinkLog_any d k g g1 hk Hp $$ Hos Hinv Hd Hz as %e %g' %hres Hd Hz
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    have hg' : g' = g ∨ g' = g.push (.del logB) := by
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
  have hnd : g'.now !! logB ≠ some .dir := by
    have hg' : g' = g ∨ g' = g.push (.del logB) := by
      rcases hres with ⟨-, h⟩ | ⟨-, h⟩
      · exact .inr h
      · exact h
    rcases hg' with rfl | rfl
    · rw [hk]; simp
    · rw [DirG.push_now]; show GMap.delete logB g.now !! logB ≠ _
      rw [GMap.lookup_delete_eq]; simp
  iloeb as IH2 generalizing Hd Hz
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  wp_apply wp_osRmdirNotDir d logB _ g' logB_ok hnd CoPset.subseteq_top $$ Hos Hd Hz
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

/-- `Regime(d/seg.log)` in the state of a retried create: `1`. -/
theorem wp_crStateL_regime (d : GoString) (g : DirG) (ko : Option GoString) (Φ : val → IProp GF) :
    ⊢ osInv (GF := GF) -∗ crStateL d g ko -∗ (crStateL d g ko -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "Regime" (Val (#(child d logB)))) {{ Φ }} := by
  iintro #Hos Hs HΦ
  cases ko with
  | none =>
    unfold crStateL
    iapply wp_osRegimeNs (child d logB) d _ g (.inr ⟨logB, logB_ok, rfl⟩) CoPset.subseteq_top
      $$ Hos Hs HΦ
  | some k =>
    unfold crStateL
    icases Hs with ⟨%hk, Hd, Hm⟩
    iapply wp_osRegimeNs (child d logB) d _ _ (.inr ⟨logB, logB_ok, rfl⟩) CoPset.subseteq_top
      $$ Hos Hd
    iintro Hd
    iapply HΦ
    dsimp only
    iframe
    ipureintro; exact hk

/-- `os.OpenFile(d/seg.log, O_RDWR|O_CREATE, perm)`, `seg.log` absent: on success a new file of a
fresh key `k`, `seg.log` names it. -/
theorem wp_openLog (d : GoString) (g : DirG) (hn : g.now !! logB = none) (perm : w32) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) d ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ osNsBusy (GF := GF) false }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d logB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osNsBusy false ∗
        ((∃ (fd : w64) (k : GoString), ⌜err = interface.nil ∧ IsInoKey k⌝ ∗
            os.ownFile f fd (child d logB) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) ⟨k, true, true⟩ ∗
            osMeta k (DFrac.own 1) (some newMeta) ∗
            osDir d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k)))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz⟩
  obtain ⟨ko, hko⟩ : ∃ ko : Option GoString, ko = none := ⟨_, rfl⟩
  ihave Hs : crStateL d g ko $$ [Hd]
  · subst hko; unfold crStateL; iexact Hd
  clear hko
  iloeb as IH generalizing %ko Hs Hz
  wp_apply wp_crStateL_regime d g ko $$ Hos Hs as Hs
  rw [os.file_ty_eq, os.File_ty_eq]
  (try wp_auto)
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hos Hz as Hz
  rw [show (W64 66 ||| W64 524288) = flCreat from by decide]
  wp_apply wp_createLog_any d g hn ko $$ Hos Hinv Hs Hz as %fd %e Hz Hr
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
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
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


end oscalls

section oscalls2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

/-- `os.OpenFile(d/seg.log, O_RDWR|O_CREATE, perm)` of the existing file of key `k`, with a
fraction of its `OsMeta`: a read-write fd on `k` (the directory unchanged), or an error. -/
theorem wp_openLogExisting (d k : GoString) (dq : DFrac) (g : DirG)
    (hk : g.now !! logB = some (.file k)) (dqm : DFrac) (mo : Option OsMeta) (perm : w32) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g ∗ osMeta (GF := GF) k dqm mo ∗
        osNsBusy (GF := GF) false }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d logB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); ⌜mo ≠ none⌝ ∗ osDir d dq g ∗
        osMeta k dqm mo ∗ osNsBusy false ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d logB) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗ osFd fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hinv, Hd, Hm, Hz⟩
  iloeb as IH generalizing Hd Hm Hz HΦ
  wp_apply wp_osRegimeNs (child d logB) d dq g (.inr ⟨logB, logB_ok, rfl⟩) CoPset.subseteq_top
    $$ Hinv Hd as Hd
  rw [os.file_ty_eq, os.File_ty_eq]
  (try wp_auto)
  wp_apply wp_osNsBegin CoPset.subseteq_top $$ Hinv Hz as Hz
  rw [show (W64 66 ||| W64 524288) = flCreat from by decide]
  wp_apply wp_osNsOpenCreatExisting d logB k dq g logB_ok hk dqm mo CoPset.subseteq_top
    $$ Hinv Hd Hm Hz as %fd %e %hmo %hres Hd Hm Hz Hfd
  rcases hres with ⟨rfl, -⟩ | ⟨he0, rfl⟩
  · rw [decide_eq_true (show (0 : w64) = W64 0 from rfl), if_pos rfl]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hd Hm Hz
    isplitr
    · ipureintro; exact hmo
    ileft
    iexists fd
    iframe Hfd
    isplitr
    · ipureintro; rfl
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · rw [decide_eq_false (show ¬ e = W64 0 from he0), if_neg (show ¬ e = (0 : w64) from he0)]
    iclear Hfd
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hd Hm Hz HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hd Hm Hz
      isplitr
      · ipureintro; exact hmo
      iright
      ipureintro; intro h; cases h

/-- `os.OpenFile(d/b, O_RDONLY, perm)` of the file `b` of `d` (of key `k`), with a fraction of
`k`'s `OsMeta`: as `os.OpenFile.wp_nsRO`, with the offset. -/
theorem wp_openRO (d b k : GoString) (hb : NameOk b) (perm : w32) (dq : DFrac)
    (g : DirG) (hf : g.now !! b = some (.file k)) (dqm : DFrac) (mo : Option OsMeta) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g ∗ osMeta (GF := GF) k dqm mo }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); ⌜mo ≠ none⌝ ∗ osDir d dq g ∗
        osMeta k dqm mo ∗
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗ osFd fd (DFrac.own 1) ⟨k, true, false⟩) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hinv, Hd, Hm⟩
  iloeb as IH generalizing Hd Hm HΦ
  wp_apply wp_osRegimeNs (child d b) d dq g (.inr ⟨b, hb, rfl⟩) CoPset.subseteq_top $$ Hinv Hd as Hd
  rw [os.file_ty_eq, os.File_ty_eq]
  rw [show (W64 0 ||| W64 524288) = flRO from by decide]
  wp_apply wp_osNsOpenFile d b k dq g hb hf dqm mo CoPset.subseteq_top $$ Hinv Hd Hm
    as %fd %e %hmo %hres Hd Hm Hfd
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    rw [if_pos (show W64 0 = (0 : w64) from rfl)]
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    iapply HΦ
    iframe Hd Hm
    isplitr
    · ipureintro; exact hmo
    ileft
    iexists fd
    iframe Hfd
    isplitr
    · ipureintro; rfl
    unfold os.ownFile os.ownOff
    isplitr [off]
    · iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · iexists inner_ptr
      iframe
      iassumption
  · rw [decide_eq_false he0, if_neg (show ¬ e = (0 : w64) from he0)]
    iclear Hfd
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      iapply IH $$ Hd Hm HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iframe Hd Hm
      isplitr
      · ipureintro; exact hmo
      iright
      ipureintro; intro h; cases h

end oscalls2

end osfs_walfs
end EtcdGrove
end Perennial
