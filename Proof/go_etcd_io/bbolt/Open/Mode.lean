/-
**`Open` chooses the file's mode** (W1 of `plans/bbolt-crash-plan.md` §7; Lean-first, no Rocq
counterpart): right before `loadFreelist` (the file opened, initialized or read, synced unless
`NoSync`, mapped; nothing carved yet), crash mode when `NoSync` and `NoGrowSync` are off, the file
system does not fail, and the file's meta pages' tails are zero (`metaTailsZero`: the crash
invariant's reference image needs them, `RefImg`; an interim condition, until the opened file is
known to have them). Then the sync left every byte durable, so the cut is cleared
(`wp_osClearCut`) and the file goes into its crash invariant (`bfile_alloc`), idle at the committed
state `C` with the file's own bytes as the reference image (`open_bDur`). Otherwise the file stays
outside one. Either way the file's resources come back for the record `{ p with cs := cs }`, with
its mode (`bMode`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt
public import Proof.go_etcd_io.bbolt.Open.Facts
public import Proof.go_etcd_io.bbolt.DB__loadFreelistSpec
public import Proof.go_etcd_io.bbolt.Crash.Phases
public import GooseLang.Ext.Fs.ClearCut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The opened file, synced, is durable for its committed state**: its own bytes are a reference
image of `C` (with zero meta tails), every byte synced. -/
theorem open_bDur (C : CommitSt) (D : Data) (m0 m : OsMeta) (xs : List ByteG)
    (hok : openOK C D m0 xs) (hsz : m.size = m0.size)
    (htz : metaTailsZero (xs.map Prod.fst)) (hl : xs.length = m.size) (h8 : 8192 ≤ m.size)
    (hdur : ∀ y ∈ xs, y = durB y.1) (hlo : m.lo = m.size) (hhi : m.hi = m.size)
    (hxs : m.xs = some [m.size]) (hal : m.size % 4096 = 0) :
    BDur ⟨C, C, xs.map Prod.fst, xs.map Prod.fst, .idle⟩ ⟨m, xs, 0, 0, .idle⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hok
  have hR : RefImg (xs.map Prod.fst) C :=
    ⟨h1, h2, h3, h4, by rw [List.length_map, hl, hsz]; exact h5, h6, h7, htz⟩
  have hps : ∀ b, b < m.size →
      PSync ⟨m, xs, 0, 0, .idle⟩ b (xb (xs.map Prod.fst) b) := by
    intro b hb
    refine ⟨?_, by intro t off data n h; cases h⟩
    have hb' : b < xs.length := by omega
    show xs[b]? = some (durB (xb (xs.map Prod.fst) b))
    rw [List.getElem?_eq_getElem hb']
    refine congrArg some ((hdur _ (List.getElem_mem hb')).trans ?_)
    unfold xb
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb']
    rfl
  have hbw : BWf ⟨m, xs, 0, 0, .idle⟩ :=
    ⟨hl, trivial, by show m.lo ≤ m.size; omega, by show m.size ≤ m.hi; omega⟩
  have hI1 : ∀ b < 8192, PSync ⟨m, xs, 0, 0, .idle⟩ b (xb (xs.map Prod.fst) b) :=
    fun b hb => hps b (by omega)
  have hI2 : ∀ b, protData (xs.map Prod.fst) C b →
      PSync ⟨m, xs, 0, 0, .idle⟩ b (xb (xs.map Prod.fst) b) := by
    intro b hb
    have h1 := (protData_range hR hb).2
    exact hps b (by omega)
  have hI3 : C.hwm * 4096 ≤ m.lo := by rw [hlo, hsz]; exact h5
  have hI4 : WrIn ⟨m, xs, 0, 0, .idle⟩ := by
    intro t off data n h; cases h
  have hI5 : XsAl ⟨m, xs, 0, 0, .idle⟩ := by
    refine ⟨[m.size], hxs, ?_, ?_, ?_⟩
    · intro x hx; simp only [List.mem_singleton] at hx; rw [hx]; exact hal
    · intro t sz n h; cases h
    · intro t off data n h; cases h
  exact ⟨hbw, hR, hI1, hI2, hI3, hal, hI4, hI5⟩

/-- `lfOK` reads the `OsMeta`'s size and mappings only. -/
theorem lfOK_congr [ExtSemantics fsExt] {N : Namespace} {db : Loc} {C : CommitSt} {b : Loc} {L : Nat} {m m' : OsMeta}
    {xs : List ByteG} (h : lfOK N db C b L m xs) (hs : m'.size = m.size) (hm : m'.maps = m.maps) :
    lfOK N db C b L m' xs := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h
  refine ⟨a1, a2, a3, a4, a5, a6, by rw [hs]; exact a7, by rw [hs]; exact a8, ?_, by rw [hm]; exact a10,
    a11, a12, a13, a14⟩
  unfold wdbSz at a9 ⊢; rw [hs]; exact a9

end pure

section mode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`Open`'s choice of the file's mode** (see the file header), before a step `e`: crash mode
when `NoSync` (`nos`) and `NoGrowSync` (`ngs`) are off, the file system does not fail and the file's
meta tails are zero; there the sync's facts (`hcr`) hold. -/
theorem wp_open_mode (s : Stuckness) (E : CoPset) (e : Expr) (Φ : val → IProp GF)
    (he : toVal e = none) (gbq : GName) (N : Namespace) (db : Loc) (p : BFile) (fd : w64)
    (C : CommitSt) (m : OsMeta) (xs : List ByteG) (nos ngs : Bool) (hxl : xs.length = m.size)
    (hcr : FsNoErr → metaTailsZero (xs.map Prod.fst) → nos = false → ngs = false →
      m.dhi ≤ m.dlo ∧ (∀ y ∈ xs, y = durB y.1) ∧ XsOne m ∧
      BDur ⟨C, C, xs.map Prod.fst, xs.map Prod.fst, .idle⟩ ⟨{ m with cut := none }, xs, 0, 0, .idle⟩)
    (hfo : ∃ D, fileOK (xs.map Prod.fst) (xs.map Prod.fst).length D) :
    db.[DB, go!"NoSync"] ↦□ nos ∗ db.[DB, go!"NoGrowSync"] ↦□ ngs ∗ dbPathLk (GF := GF) db p fd ∗
      osMeta p.ino (DFrac.own 1) m ∗ osBytes p.ino 0 (DFrac.own 1) xs ∗ ⧖ C.txid ∗
      (∀ (cs : Option CsN) (gcn : GName) (m' : OsMeta), ⌜m'.size = m.size ∧ m'.maps = m.maps⌝ -∗
        bMode gbq gcn N db { p with cs := cs } -∗ cpart (cs.map CsN.cg) 1 (treeData C) C.txid -∗
        dbPathLk db { p with cs := cs } fd -∗
        bMeta { p with cs := cs } C [] m' -∗ bBytes { p with cs := cs } 0 (DFrac.own 1) xs -∗
        WP e @ s; E {{ Φ }}) ⊢
    WP e @ s; E {{ Φ }} := by
  iintro ⟨#Hns, #Hngs, Hpath, Hm, Hb, #Hrc, Hk⟩
  iunfold dbPathLk at Hpath
  icases Hpath with ⟨Hp, Htok, -⟩
  by_cases hc : FsNoErr ∧ metaTailsZero (xs.map Prod.fst) ∧ nos = false ∧ ngs = false
  · -- crash mode
    obtain ⟨hfs, htz, hnos, hngs⟩ := hc
    obtain ⟨hdd, hdur, hone, hD⟩ := hcr hfs htz hnos hngs
    subst hnos hngs
    iapply wp_osClearCut e Φ he p.ino m xs hxl hdur hdd
    iframe Hm Hb
    iintro Hm Hb
    imod bfile_alloc p.path p.ino gbq (N .@ "crash") C { m with cut := none } xs
      ⟨C, C, xs.map Prod.fst, xs.map Prod.fst, .idle⟩ E hxl rfl ⟨rfl, rfl, rfl⟩ (fun _ => hD) hdur hfs
      (fun l hl x hx => hone l hl x hx) $$ Hm Hb Hrc with ⟨%c, %hcn, #Hci, Hm, Hb, Hcv, #Hh⟩
    ihave #Hsy : bSyncs (GF := GF) db { p with cs := some c } $$ []
    · unfold bSyncs; dsimp only; iframe #
    imod dghostVar_alloc (GF := GF) (some c.cg) with ⟨%gcn, Hreg⟩
    imod dghostVar_persist gcn 1 (some c.cg) $$ Hreg with #Hreg
    iapply Hk $$ %(some c) %gcn %{ m with cut := none } [] [] [Hcv] [Hp Htok] Hm Hb
    · ipureintro; exact ⟨rfl, rfl⟩
    · unfold bMode; dsimp only
      iframe Hci Hsy Hreg
      ipureintro; exact ⟨hcn.1, hcn.2, hfs⟩
    · dsimp only [Option.map]; iapply (cpart_some c.cg 1 _ _).2; iframe Hcv Hh
    · unfold dbPathLk; iframe; iframe #
  · -- outside a crash invariant
    imod dghostVar_alloc (GF := GF) (none : Option CsG) with ⟨%gcn, Hreg⟩
    imod dghostVar_persist gcn 1 (none : Option CsG) $$ Hreg with #Hreg
    iapply Hk $$ %none %gcn %m [] [] [] [Hp Htok] [Hm] [Hb]
    · ipureintro; exact ⟨rfl, rfl⟩
    · unfold bMode; dsimp only
      iframe Hreg
      iexists nos, ngs, xs.map Prod.fst
      iframe #
      ipureintro
      refine ⟨?_, hfo⟩
      intro hfs htz
      rcases nos with _ | _
      · rcases ngs with _ | _
        · exact absurd ⟨hfs, htz, rfl, rfl⟩ hc
        · exact Or.inr rfl
      · exact Or.inl rfl
    · unfold cpart; dsimp only [Option.map]; iempintro
    · unfold dbPathLk; iframe; iapply bSyncs_none (p := { p with cs := none }) rfl
    · rw [bMeta_none (p := { p with cs := none }) rfl]; iexact Hm
    · iapply (bBytes_none (p := { p with cs := none }) rfl 0 (DFrac.own 1) xs).2; iexact Hb

end mode

end bbolt
end EtcdGrove
end Perennial
