/-
**The two-region test** of the shared mode (`notes/wal-fsext-i2-design.md`): two regions of one
directory, the claims on the names `b1` and `b2`, each with its own call (a fraction of the call
permission) and a fraction of the spine, create their files concurrently: the two WPs are separate
(`twoRegion_par`, what a fork of the two threads needs), whatever order the steps take. At a crash,
a region whose create is below the commit bound concludes alone that its file is there, whatever
the other region did (`twoRegion_crash`: `crashRest_region` with both claims, the other's history
unknown). Untrusted (a check of the shared specs' usability).
-/
module

public import GooseLang.Ext.Fs.TreeShared

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs
namespace SharedTests

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- After a kept entry writing `b`, last in a claim's history, `b` holds what that entry left. -/
theorem valAfter_last (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hK : K x) (hw : e.op.Writes j b) :
    (h.log x e c).valAfter j K b = c !! b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_pos (by simp [hK, hw])]
  simp

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- What a region has after its `open(O_CREAT)` of `b` (the name free): its permission back, and
the file created (logged, its claim updated, its `OsMeta`), or a failure with nothing done. -/
def createPost (j : Ino) (b : GoString) (h : NamesH) (s0 : Nat) (q : Qp) (v : val) : IProp GF :=
  iprop(osCallPerm (L := L) q ∗ ∃ fd e : w64, ⌜v = PairV (#fd) (#e)⌝ ∗
    ((∃ x i, osLogged (L := L) x (⟨.create j b i, s0⟩ : LogEntry) ∗
        osNames (L := L) j (.only [b]) (DFrac.own 1)
          (h.log x (⟨.create j b i, s0⟩ : LogEntry) (<[b := .file i]> h.cur)) ∗
        osMeta (L := L) i (DFrac.own 1) newMeta) ∨
     (⌜e ≠ 0⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h)))

/-- One region's create, from its own resources. -/
theorem region_create (R : Roots) (d b : GoString) (j : Ino) (q : Qp) (h : NamesH) (k s0 : Nat)
    (c : Qp) (hb : NameOk b) (hn : h.cur !! b = none) (hs : h.next ≤ s0) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d (DFrac.own q) j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 c -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#flCreat)))))
        @ s; E {{ createPost (L := L) j b h s0 c }} := by
  iintro #Hinv #Hsi Hp Hn Hk
  iapply wp_osOpenCreateS R d b j (DFrac.own q) h k s0 c hb (by rw [hn]; intro J hJ; cases hJ) hs
    hE hE' _ $$ Hinv Hsi Hp Hn Hk
  iintro %fd %e Hq - Hpost
  unfold createPost
  isplitl [Hq]
  · iexact Hq
  iexists fd, e
  isplitr
  · ipureintro; rfl
  icases Hpost with (⟨%i, %hi, -⟩ | ⟨-, %x, %i, Hlg, Hn, Hm, -⟩ | ⟨⟨%he, -⟩, Hn⟩)
  · rw [hn] at hi; cases hi
  · ileft
    iexists x, i
    isplitl [Hlg]
    · iexact Hlg
    isplitl [Hn]
    · iexact Hn
    · iexact Hm
  · iright
    isplitr
    · ipureintro; exact he
    · iexact Hn

/-- **Two regions create concurrently**: from disjoint resources (a claim, a call and a spine
fraction each), two separate WPs. -/
theorem twoRegion_par (R : Roots) (d b1 b2 : GoString) (j : Ino) (q1 q2 : Qp) (h1 h2 : NamesH)
    (k1 k2 s1 s2 : Nat) (c1 c2 : Qp) (hb1 : NameOk b1) (hb2 : NameOk b2)
    (hn1 : h1.cur !! b1 = none) (hn2 : h2.cur !! b2 = none) (hs1 : h1.next ≤ s1)
    (hs2 : h2.next ≤ s2) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d (DFrac.own (q1 + q2)) j -∗
      osNames (L := L) j (.only [b1]) (DFrac.own 1) h1 -∗
      osNames (L := L) j (.only [b2]) (DFrac.own 1) h2 -∗
      osCallS (L := L) k1 s1 c1 -∗ osCallS (L := L) k2 s2 c2 -∗
      (WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k1) (PairV (#(child d b1)) (#flCreat)))))
        @ s; E {{ createPost (L := L) j b1 h1 s1 c1 }}) ∗
      (WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k2) (PairV (#(child d b2)) (#flCreat)))))
        @ s; E {{ createPost (L := L) j b2 h2 s2 c2 }}) := by
  iintro #Hinv #Hsi Hp Hn1 Hn2 Hk1 Hk2
  icases (osPathS_frac R d q1 q2 j).1 $$ Hp with ⟨Hp1, Hp2⟩
  isplitl [Hp1 Hn1 Hk1]
  · iapply region_create R d b1 j q1 h1 k1 s1 c1 hb1 hn1 hs1 hE hE' $$ Hinv Hsi Hp1 Hn1 Hk1
  · iapply region_create R d b2 j q2 h2 k2 s2 c2 hb2 hn2 hs2 hE hE' $$ Hinv Hsi Hp2 Hn2 Hk2

end specs

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **A synced region concludes alone**: region 1's create, logged at `x1` below the commit bound
`n`, is in the crashed tree, whatever region 2's claim knows. -/
theorem twoRegion_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (j : Ino) (b1 b2 : GoString) (h1 h2 : NamesH) (x1 s1 : Nat)
    (i1 : Ino) (n : Nat) (hx : x1 < n) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osNames (L := L) j (.only [b1]) (DFrac.own 1)
        (h1.log x1 (⟨.create j b1 i1, s1⟩ : LogEntry) (<[b1 := .file i1]> h1.cur)) -∗
      osNames (L := L) j (.only [b2]) (DFrac.own 1) h2 -∗
      osCommitLb (L := L) n ={E}=∗
      ⌜V'.now.entry j b1 = some (.file i1)⌝ := by
  iintro #Hsi Hcr Hn1 Hn2 Hc
  let c1 : Claim × DFrac := ((j, .only [b1],
    h1.log x1 (⟨.create j b1 i1, s1⟩ : LogEntry) (<[b1 := .file i1]> h1.cur)), DFrac.own 1)
  let c2 : Claim × DFrac := ((j, .only [b2], h2), DFrac.own 1)
  imod crashRest_region Q L L' D tt V' R [c1, c2] n E hE $$ Hsi Hcr [Hn1 Hn2] Hc
    with ⟨%hreg, -, -⟩
  · unfold osClaims
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hn1]
    · iexact Hn1
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hn2]
    · iexact Hn2
    iapply (BigSepL.bigSepL_nil).2; iempintro
  imodintro
  ipureintro
  obtain ⟨K, -, hbelow, hval⟩ := hreg
  have hc1 : c1.1 ∈ [c1, c2].map (·.1) := by simp
  have hK : K x1 := hbelow c1.1 hc1 x1 ⟨.create j b1 i1, s1⟩ (<[b1 := .file i1]> h1.cur)
    (by simp [c1, NamesH.log]) hx
  rw [hval c1.1 hc1 b1 (by simp [c1, NameSet.Mem])]
  simp only [c1]
  rw [valAfter_last _ _ _ _ _ _ _ hK (.inl (by simp [MetaOp.slots]))]
  simp

end crash

end SharedTests
end Fs
end Perennial

end
