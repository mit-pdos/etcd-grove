/- Lean-first (no Rocq counterpart).

# An etcd member machine's crash law (etcd-dist D6, task T7; `notes/etcd-dist-d6.md`, "T7")

The assembly of T2 (`rnDurK_crash`), T5 (`walFilesC_crash`), T6 (`snapDir_crash.law`) and A1 (`dbCrash`)
into `memberGen_crash.law` (`MemberGen.lean`). This file holds, so far, item 2 of the plan: **the two
premises T6's law takes of T7**, proved from what Go's `TouchDirAll` does (it syncs the parent of the
directory it makes, `fileutil.go:49-85`, F-N2, so the entries naming `member` and `snap` are committed):

* `osSpineDur j cs J`, `osPathDur R p J` (persistent): **a durable path**, `osPathS` with each component's
  claim held at a discarded fraction (so it is never written again: Go never writes those names after
  `TouchDirAll`) and its name's crash promise `nameCrash h j c (· = some (.dir J))` (`backend/FileDur.lean`).
  Made from roots (`osPathDur_root`) and `TouchDirAll`'s post (`osPathDur_child`: the claim with
  `h.next ≤ n` and `osCommitLb n`).
* `osPathDur_lookup`: after a crash, **the crashed tree resolves the path to the same directory**
  (`lookupH R V' p = some (.dir J)`): T6's premise `hJ`.
* `osPathDur_agree`: every spine of the path at the same roots ends at `J`; so `snapDirKeptR` (T6's
  `snapDirKept` at the law's own roots `R`) holds (`snapDirKeptR_of`). T6's `snapDirKept` quantifies over the
  roots `R0` of any shared invariant and is a plain wand, which cannot see that `R0 = R` (two shared
  invariants agree only under an update): the restatement at `R` is proposed (`notes/specs-only/ledger.md`,
  2026-11-25, "T7"), with `crashRest_roots` (below), which gives `old_dir` its `R0 = R`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberGen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapDirCrash
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.FileDur
public import GooseLang.Ext.Fs.TreeSharedCrash
public import GooseLang.Ext.Fs.TreeSharedCoh
public import GooseLang.Ext.Fs.TreeStepLemmas
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace memberCrash

open Iris Iris.BI Iris.ProofMode Fs backend

/-! ## Durable paths -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The components `cs` lead durably from the directory `j` to `J`** (persistent): each component's claim
at a discarded fraction, naming the next directory, with the crash promise that every crash leaves the
name naming it. -/
def osSpineDur : Ino → List GoString → Ino → IProp GF
  | j, [], j' => iprop(⌜j = j'⌝)
  | j, c :: cs, j' => iprop(∃ (h : NamesH) (J : Ino), osNames j (.only [c]) DFrac.discard h ∗
      ⌜h.cur !! c = some (.dir J)⌝ ∗ nameCrash h j c (· = some (.dir J)) ∗ osSpineDur J cs j')

/-- **The path `p` names the directory `J` durably** (persistent; `osPathS` with a durable spine). -/
def osPathDur (R : Roots) (p : GoString) (J : Ino) : IProp GF :=
  iprop(∃ (r : GoString) (j0 : Ino) (cs : List GoString),
    ⌜RootsOk R ∧ (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs⌝ ∗ osSpineDur j0 cs J)

/-- **The crash kept the directory of `sd`** at the roots `R` (persistent): `snapDirKeptF`
(`SnapDirCrash.lean`) at `R0 := R`. -/
def snapDirKeptR (R : Roots) (V' : Hist) (sd : GoString) : IProp GF :=
  iprop(□ ∀ (dq : DFrac) (j : Ino), osPathS R sd dq j -∗ ⌜lookupH R V' sd = some (.dir j)⌝)

theorem osSpineDur_nil (j j' : Ino) : osSpineDur (GF := GF) j [] j' = iprop(⌜j = j'⌝) := by
  simp only [osSpineDur]

theorem osSpineDur_cons (j : Ino) (c : GoString) (cs : List GoString) (j' : Ino) :
    osSpineDur (GF := GF) j (c :: cs) j' = iprop(∃ (h : NamesH) (J : Ino),
      osNames j (.only [c]) DFrac.discard h ∗ ⌜h.cur !! c = some (.dir J)⌝ ∗
      nameCrash h j c (· = some (.dir J)) ∗ osSpineDur J cs j') := by
  simp only [osSpineDur]

instance osNames_discard_persistent (j : Ino) (N : NameSet) (h : NamesH) :
    Persistent (osNames (GF := GF) j N DFrac.discard h) := by
  unfold osNames; split
  · infer_instance
  · unfold gElem; letI := (gooseOsGS (GF := GF)).osAllG; infer_instance

instance osSpineDur_persistent (j : Ino) (cs : List GoString) (j' : Ino) :
    Persistent (osSpineDur (GF := GF) j cs j') := by
  induction cs generalizing j with
  | nil => rw [osSpineDur_nil]; infer_instance
  | cons c cs ih =>
    rw [osSpineDur_cons]
    haveI : ∀ J, Persistent (osSpineDur (GF := GF) J cs j') := ih
    infer_instance

instance osPathDur_persistent (R : Roots) (p : GoString) (J : Ino) :
    Persistent (osPathDur (GF := GF) R p J) := by
  unfold osPathDur; infer_instance

instance snapDirKeptR_persistent (R : Roots) (V' : Hist) (sd : GoString) :
    Persistent (snapDirKeptR (GF := GF) R V' sd) := by
  unfold snapDirKeptR; infer_instance

end defs

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- A durable spine and any spine of the same components from the same directory end at the same
directory (the claims' fragments agree). -/
theorem osSpineDur_agree (L : GooseLocalGS GF) (cs : List GoString) (j J j' : Ino) (dq : DFrac) :
    ⊢ osSpineDur (hG := ⟨G, L⟩) j cs J -∗ osSpine (L := L) j cs dq j' -∗ ⌜j' = J⌝ := by
  induction cs generalizing j with
  | nil =>
    rw [osSpineDur_nil (hG := ⟨G, L⟩), osSpine_nil]
    iintro %h1 %h2
    ipureintro; exact h2.symm.trans h1
  | cons c cs ih =>
    rw [osSpineDur_cons (hG := ⟨G, L⟩), osSpine_cons]
    iintro ⟨%h1, %J1, Hn1, %hJ1, -, Hs1⟩ ⟨%h2, %J2, Hn2, %hJ2, Hs2⟩
    icases osNames_agree (L := L) _ _ _ _ _ _ $$ Hn1 Hn2 with %he
    subst he
    have hJ : J1 = J2 := by rw [hJ1] at hJ2; cases hJ2; rfl
    subst hJ
    iapply ih J1 $$ Hs1 Hs2

/-- **Every spine of a durable path at its roots ends at its directory.** -/
theorem osPathDur_agree (L : GooseLocalGS GF) (R : Roots) (p : GoString) (J j : Ino) (dq : DFrac) :
    ⊢ osPathDur (hG := ⟨G, L⟩) R p J -∗ osPathS (L := L) R p dq j -∗ ⌜j = J⌝ := by
  unfold osPathDur osPathS
  iintro ⟨%r, %j0, %cs, %hp, Hs⟩ ⟨%r', %j0', %cs', %hp', Hs'⟩
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  obtain ⟨-, hm', hcs', hpe⟩ := hp'
  obtain ⟨he, rfl⟩ := root_split_unique hR hm hm' hcs hcs' hpe
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  iapply osSpineDur_agree L cs j0 J j dq $$ Hs Hs'

/-- **After a crash, a durable spine is a walk of the crashed tree.** -/
theorem osSpineDur_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) (cs : List GoString)
    (j J : Ino) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osSpineDur (hG := ⟨G, L⟩) j cs J ={E}=∗
      ⌜walk V'.now (.dir j) cs = some (.dir J)⌝ ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  induction cs generalizing j with
  | nil =>
    rw [osSpineDur_nil (hG := ⟨G, L⟩)]
    iintro #Hsi Hr %h
    subst h
    imodintro; iframe Hr; ipureintro; rfl
  | cons c cs ih =>
    rw [osSpineDur_cons (hG := ⟨G, L⟩)]
    iintro #Hsi Hr ⟨%h, %J1, #Hn, %hJ1, #Hc, #Hs⟩
    imod nameCrash_crash Q L L' D tt V' R j c DFrac.discard h (· = some (.dir J1)) E hE $$
      Hsi Hr Hn Hc with ⟨%he, Hr, -⟩
    imod ih J1 $$ Hsi Hr Hs with ⟨%hw, Hr⟩
    imodintro
    iframe Hr
    ipureintro
    simp only [walk, he]
    exact hw

/-- **After a crash, the crashed tree resolves a durable path to its directory** (T6's premise
`lookupH R V' sd = some (.dir J)`). -/
theorem osPathDur_lookup (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) (p : GoString) (J : Ino) :
    ⊢ osSharedInv (L := L) R -∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗
      osPathDur (hG := ⟨G, L⟩) R p J ={E}=∗
      ⌜lookupH R V' p = some (.dir J)⌝ ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  unfold osPathDur
  iintro #Hsi Hr ⟨%r, %j0, %cs, %hp, #Hs⟩
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  imod osSpineDur_crash Q L L' D tt V' R E hE cs j0 J $$ Hsi Hr Hs with ⟨%hw, Hr⟩
  imodintro
  iframe Hr
  ipureintro
  unfold lookupH
  rw [lookup_joinPath (st := Hist.st R V') hR hm hcs, histSt_tree]
  exact hw

/-- **T6's `snapDirKept` at the law's roots** (`snapDirKeptR`), from the durable path of `sd` and what the
crashed tree resolves it to. -/
theorem snapDirKeptR_of (L : GooseLocalGS GF) (R : Roots) (V' : Hist) (sd : GoString) (J : Ino)
    (hJ : lookupH R V' sd = some (.dir J)) :
    ⊢ osPathDur (hG := ⟨G, L⟩) R sd J -∗ snapDirKeptR (hG := ⟨G, L⟩) R V' sd := by
  unfold snapDirKeptR
  iintro #Hd
  imodintro
  iintro %dq %j Hp
  icases osPathDur_agree L R sd J j dq $$ Hd Hp with %hj
  ipureintro; rw [hj]; exact hJ

/-- **The shared invariants of one generation have the crash's roots** (with its restart resources):
two of them agree on their roots. What T6's `old_dir` needs to use `snapDirKeptR` (D-T7-1). -/
theorem crashRest_roots (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (R R0 : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ osSharedInv (L := L) R0 -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' ={E}=∗
      ⌜R0 = R⌝ ∗ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' := by
  iintro #Hsi #Hsi0 Hr
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %hrel, Hab, Ham, Hfs, HAt, Htok, Htl, Hcc⟩
  unfold crashShared
  icases Hcc with ⟨Has, %hsh, Hcm⟩
  unfold osSharedInv
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs with %hVs
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs
  obtain ⟨hR, rfl⟩ := hVs
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists _, Γn; iframe; ipureintro; exact hcoh
  imod inv_acc hE $$ Hsi0 with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs0, %Γn0, Hs0, HAn0, %hcoh0, Halen0, HAlog0⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ Has Hs0 with %hVs0
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hVs0
  obtain ⟨hR0, rfl⟩ := hVs0
  imod Hclose $$ [Hs0 HAn0 Halen0 HAlog0] with -
  · inext; iexists _, Γn0; iframe; ipureintro; exact hcoh0
  imodintro
  isplitr
  · ipureintro; rw [← hR0, hR]
  iexists Γb, Γm, F, st, st', Γf, Γt
  iframe Hab Ham Hfs HAt Htok Htl Has Hcm
  isplitr
  · ipureintro; exact hrel
  ipureintro; exact hsh

/-! ### Making durable paths -/

/-- A root is a durable path to its directory. -/
theorem osPathDur_root (L : GooseLocalGS GF) (R : Roots) (r : GoString) (j0 : Ino) (hr : (r, j0) ∈ R)
    (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R ={E}=∗ osPathDur (hG := ⟨G, L⟩) R r j0 := by
  iintro #Hsi
  imod osSharedInv_rootsOk (L := L) R hE $$ Hsi with %hR
  imodintro
  unfold osPathDur
  iexists r, j0, []
  rw [osSpineDur_nil (hG := ⟨G, L⟩)]
  isplitl [] <;> ipureintro
  · exact ⟨hR, hr, by simp, by simp [joinPath]⟩
  · rfl

/-- A durable spine extended by a durable component. -/
theorem osSpineDur_snoc (L : GooseLocalGS GF) (cs : List GoString) (j j' : Ino) (b : GoString)
    (h : NamesH) (J : Ino) (hJ : h.cur !! b = some (.dir J)) :
    ⊢ osSpineDur (hG := ⟨G, L⟩) j cs j' -∗ osNames (L := L) j' (.only [b]) DFrac.discard h -∗
      nameCrash (hG := ⟨G, L⟩) h j' b (· = some (.dir J)) -∗
      osSpineDur (hG := ⟨G, L⟩) j (cs ++ [b]) J := by
  induction cs generalizing j with
  | nil =>
    rw [osSpineDur_nil (hG := ⟨G, L⟩), List.nil_append, osSpineDur_cons (hG := ⟨G, L⟩)]
    iintro %hj Hn Hc
    subst hj
    iexists h, J
    rw [osSpineDur_nil (hG := ⟨G, L⟩)]
    iframe Hn Hc
    isplit <;> ipureintro
    · exact hJ
    · rfl
  | cons c cs ih =>
    rw [osSpineDur_cons (hG := ⟨G, L⟩), List.cons_append, osSpineDur_cons (hG := ⟨G, L⟩)]
    iintro ⟨%h1, %J1, Hn1, %hJ1, Hc1, Hs⟩ Hn Hc
    iexists h1, J1
    iframe Hn1 Hc1
    isplitl []
    · ipureintro; exact hJ1
    iapply ih J1 $$ Hs Hn Hc

/-- **A durable path extended by a directory `TouchDirAll` made** (its post: the claim on `b` naming `J`,
every entry writing `b` below `n`, `osCommitLb n`), the claim's fraction discarded. -/
theorem osPathDur_child (L : GooseLocalGS GF) (R : Roots) (d b : GoString) (j J : Ino) (h : NamesH)
    (n : Nat) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) (hn : h.next ≤ n) (E : CoPset)
    (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗ osPathDur (hG := ⟨G, L⟩) R d j -∗
      osNames (L := L) j (.only [b]) DFrac.discard h -∗ osCommitLb (L := L) n ={E}=∗
      osPathDur (hG := ⟨G, L⟩) R (child d b) J := by
  iintro #Hsi #Hd #Hn #Hlb
  imod osNames_histCoh (L := L) R j (.only [b]) DFrac.discard h hE $$ Hsi Hn with ⟨-, %hcoh⟩
  have hc : CrashLeaves h j b (· = some (.dir J)) n :=
    crashLeaves_mono (crashLeaves_of_coh hcoh (by simp [NameSet.Mem])
      (fun xe hxe => Nat.lt_of_lt_of_le (hcoh.1 xe hxe) hn))
      (fun v hv => by rw [hv, hJ])
  imodintro
  unfold osPathDur
  icases Hd with ⟨%r, %j0, %cs, %hp, Hs⟩
  obtain ⟨hR, hm, hcs, rfl⟩ := hp
  iexists r, j0, cs ++ [b]
  isplitl []
  · ipureintro
    refine ⟨hR, hm, ?_, (joinPath_snoc r cs b).symm⟩
    intro c hc'
    simp only [List.mem_append, List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · exact hcs c hc'
    · exact hb
  iapply osSpineDur_snoc L cs j0 j b h J hJ $$ Hs Hn
  unfold nameCrash
  iexists n
  iframe Hlb
  ipureintro; exact hc

end laws

end memberCrash
end EtcdGrove
end Perennial
