/-
The tree after a crash, with the committed prefix (`TreeCommit.lean`): from a lower bound
`osCommitLb n` of the old generation and (a fraction of) its history `W`, the restart learns that
the crash kept at least the first `n` entries of `W`'s log (`TreeCrashedLb W V' n`). What a path
names then (`lookupH`): what it named after every prefix of at least `n` entries (`lookupH_crashLb`).
A test: a file created, then its directory `fsync`ed, is in every tree a crash leaves. Untrusted.
-/
module

public import GooseLang.Ext.Fs.CrashTok
public import GooseLang.Ext.Fs.TreeCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Paths after a crash that kept a prefix -/

/-- What a path names depends on the tree now only. -/
theorem lookupH_now (R : Roots) (V : Hist) (p : GoString) :
    lookupH R (V.now, []) p = lookupH R V p := rfl

/-- **What a path names after a crash that kept at least `n` entries**: what it named after every
prefix of the log of at least `n` entries, if that is the same. -/
theorem lookupH_crashLb {R : Roots} {V V' : Hist} {n : Nat} (h : TreeCrashedLb V V' n)
    {p : GoString} {r : Option Node}
    (hp : ∀ k, n ≤ k → k ≤ V.2.length → lookupH R (V.1, V.2.take k) p = r) :
    lookupH R V' p = r := by
  obtain ⟨k, hnk, hk, rfl⟩ := h
  exact hp k hnk hk

/-- After a crash that kept every entry, every path names what it named. -/
theorem lookupH_crashLb_all {R : Roots} {V V' : Hist} (h : TreeCrashedLb V V' V.2.length)
    (p : GoString) : lookupH R V' p = lookupH R V p := by
  rw [h.all]; rfl

/-! ## The restart's resources -/

section crash
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- **The tree after a crash, with a lower bound on its committed prefix**: from (a fraction of)
the old generation's history `W` and a lower bound `n` of its committed prefix, the crash kept at
least the first `n` entries of `W`'s log. Everything is given back. -/
theorem crashRest_lb (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino) (tt : Bool)
    (V' : Hist) (dq : DFrac) (R : Roots) (W : Hist) (n : Nat) :
    ⊢ crashRest Q hL hL' D tt V' -∗ gElem hL hL.γd () dq (R, W) -∗ gCommitLb hL n -∗
      ⌜TreeCrashedLb W V' n⌝ ∗ crashRest Q hL hL' D tt V' ∗ gElem hL hL.γd () dq (R, W) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Htl, Hcc⟩
    Hd #Hlb
  icases gAuth_lookup hL _ _ _ _ _ $$ HAd Hd with %hh
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hh
  obtain ⟨hR, rfl⟩ := hh
  unfold crashMode crashShared crashCommit commitRes
  icases Hcc with (⟨⟨%hlb, %c, %hc, Ha⟩, Has⟩ | ⟨Hd1, -⟩)
  · icases gCommitLb_valid hL c n $$ Ha Hlb with %hn
    iframe Hd
    isplitr
    · ipureintro; exact (hlb c hc).mono hn
    iexists Γb, Γm, F, st, st', Γf, Γt, V
    iframe Hab Ham Hfs HAt Htok HAd Htl
    isplitr
    · ipureintro; exact hrel
    ileft
    iframe Has
    isplitr
    · ipureintro; exact hlb
    iexists c
    iframe Ha
    ipureintro; exact hc
  · icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hd Hd1 with %Hv
    exact absurd (DFrac.valid_op_own Hv.1) (by simp)

end crash

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- `crashRest_lb` from the old generation `L` to the new one `L'`. -/
theorem osTreeCrash_lb (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (dq : DFrac) (R : Roots) (W : Hist) (n : Nat) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osTree (L := L) dq R W -∗ osCommitLb (L := L) n -∗
      ⌜TreeCrashedLb W V' n⌝ ∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ∗
        osTree (L := L) dq R W := by
  unfold osTree osCommitLb
  iintro Hr Hd Hlb
  iapply crashRest_lb _ Q _ D tt V' dq R W n $$ Hr Hd Hlb

/-- **The tree after a crash, taken, with a lower bound on its committed prefix**: as
`osTreeCrash_take`, and the crash kept at least the first `n` entries of `W`'s log. -/
theorem osTreeCrash_take_lb (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (V' : Hist) (dq : DFrac) (R : Roots) (W : Hist) (n : Nat) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' -∗
      osTree (L := L) dq R W -∗ osCommitLb (L := L) n -∗
      ⌜TreeCrashedLb W V' n⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V' ∗
        osTree (L := L) dq R W := by
  iintro Hr Hd Hlb
  icases osTreeCrash_lb Q L L' D false V' dq R W n $$ Hr Hd Hlb with ⟨%h, Hr, Hd⟩
  icases osTreeCrash_take Q L L' D V' dq R W $$ Hr Hd with ⟨-, Hn, Hr, Hd⟩
  iframe Hn Hr Hd
  ipureintro; exact h

/-! ## A test: a file created, then its directory synced, survives every crash -/

/-- **A created file whose directory was then synced is in every tree a crash leaves**: the
history `W` with the `create` of `b` (inode `i`) in the directory `j` logged, and every entry of it
committed (`wp_osDirSync_lb`'s success): every crash keeps `b` in `j`. -/
theorem test_create_dirSync_keeps (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (dq : DFrac) (R : Roots) (W : Hist) (j : Ino)
    (b : GoString) (i : Ino) (s : Nat) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osTree (L := L) dq R (W.push ⟨.create j b i, s⟩) -∗
      osCommitLb (L := L) (W.push ⟨.create j b i, s⟩).2.length -∗
      ⌜V'.now.entry j b = some (.file i)⌝ := by
  iintro Hr Hd Hlb
  icases osTreeCrash_lb Q L L' D tt V' dq R _ _ $$ Hr Hd Hlb with ⟨%h, -, -⟩
  ipureintro
  rw [h.all]
  show (Hist.push W ⟨.create j b i, s⟩).now.entry j b = some (.file i)
  rw [Hist.push_now]
  show (W.now.upd j (fun d => <[b := .file i]> d)).entry j b = some (.file i)
  simp only [entry_upd, ↓reduceIte]
  exact GMap.lookup_insert _ _ _

end gen

end Fs
end Perennial

end
