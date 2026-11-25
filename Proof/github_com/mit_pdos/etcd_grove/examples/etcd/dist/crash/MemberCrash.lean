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

And, for the assembly's `Keep` (decision D-T7-3 of the plan): `rnTakenK_stop`, T2's crash law's second case
(the stop took the records) is refuted by the stop's token, which the member's run keeps (it never stops its
server).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberGen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapDirCrash
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrash
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsHGen
public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsCrash
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash
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
  iintro #Hsi #Hd Hn #Hlb
  imod osNames_histCoh (L := L) R j (.only [b]) DFrac.discard h hE $$ Hsi Hn with ⟨Hn, %hcoh⟩
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

/-! ## The stop excluded (D-T7-3) -/

section stop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver in
/-- **A run that keeps the stop's token was not stopped**: the stop's mark (`rnTakenK`, the second case of
T2's crash law `rnDurK_crash.law`) contradicts the invariant once the stop's token is held elsewhere. -/
theorem rnTakenK_stop (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (E : CoPset)
    (hE : ↑rnDurKN ⊆ E) :
    letI := srvStor (GF := GF) γn;
    ⊢ rnDurInvK γn id νk h -∗ rnTakenK νk -∗ token νk.ν.stop ={E}=∗ False := by
  iintro #Hinv Htk Hst
  iunfold rnDurInvK at Hinv; icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  -- (no credit: the contradiction is pure, under the later)
  ihave Hf : iprop(▷ ⌜False⌝) $$ [Hi Htk Hst]
  · inext
    icases Hi with (Hb | ⟨Hst', -, -, -⟩)
    · iunfold rnDurBodyK at Hb
      icases Hb with ⟨%vk, %σ, %Hs, %n, -, -, Htn, -⟩
      iunfold rnTakenK at Htk
      ihave %Hbad := dghostVar_valid_2 νk.tkn _ _ _ _ $$ Htn Htk
      exfalso; have h1 := DFrac.valid_own_op Hbad.1; exact absurd h1 (by decide)
    · iexfalso; iapply token_exclusive $$ Hst Hst'
  icases Hf with >%hF
  exact hF.elim

end stop

/-! ## Raft's durable state and the WAL's files across the crash (T2 + T5)

The resources of each generation are named by definitions over one `HeapGS` (`memberDurKeep`,
`memberWalCrash`, `memberDurOut`): a statement over two generations `L`, `L'` has both, and the
global ghost state `G`, as local instances, and the instances Lean finds for a predicate written in it
directly (`nodeCrashTok`'s `InvGS`, through `L'`) are not those of the law it is passed to. -/

section durDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **What the member keeps of its raft durability across a crash** (D-T7-3): T2's crash-aware
invariant, its crash tokens (the invariant's and the node's arm's), and the graceful stop's token,
which the member never spends (it never stops its server), so T2's stop case is refuted. -/
def memberDurKeep (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) : IProp GF :=
  letI := srvStor (GF := GF) γn
  iprop(rnDurInvK γn id νk h ∗ token νk.tk ∗ nodeCrashTok γn.cl id νk.x ∗ token νk.ν.stop)

/-- **What the member keeps of its WAL area across a crash**: the area's invariant at the WAL names
`h.W` (`walInv`, at the server's codec and marshaller) with its crash token, and the shared mode's
invariant at the roots `h.R` (over `h`'s file system instances). -/
def memberWalKeep (h : WalH GF) : IProp GF :=
  letI := h.ext; letI := h.semOk; letI := h.has
  iprop(WalFs.walInv (W := h.W) walCodec walSrvMr h.R h.jr h.r ∗ WalFs.walCrashTok (W := h.W) ∗
    Fs.osSharedInv h.R)

/-- **The WAL's crash view** (`walInv_crash`'s outputs T5's `walRecsH_crash` takes, but the call
permission): the crash view from the WAL names `h.W` to `W'`, `W'`'s lock token. -/
def memberWalCrashW (h : WalH GF) (W' : WalFs.WalGS GF) : IProp GF :=
  letI := h.ext; letI := h.semOk; letI := h.has
  iprop(WalFs.walCrashWal h.W W' ∗ WalFs.walUnlockedTok (W := W'))

/-- **The WAL's crash at the new generation** (all of `walRecsH_crash`'s inputs but the records):
`memberWalCrashW` and the WAL directory's call permission's half at the generation. -/
def memberWalCrash (h : WalH GF) (W' : WalFs.WalGS GF) : IProp GF :=
  letI := h.ext; letI := h.semOk; letI := h.has
  iprop(memberWalCrashW h W' ∗ Fs.osCallPerm (Fs.callKey h.R h.dir) (1 : Qp).half)

/-- **Raft's durable state after the crash** (T2's outputs): the id's state `S` and vacancy, records
`σ` that hold it and meet I1-I4, their snapshot's certificates, a committed log `l` they agree with. -/
def memberDurOut (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (S : RaftState) (σ : StorContents)
    (l : List LogEntry) : IProp GF :=
  iprop(raftState γn.cl id S ∗ nodeVacant γn.cl id ∗
    ⌜StorageHolds S σ ∧ σ.b ≤ l.length ∧ DurAgrees S l ∧ walReadFacts σ⌝ ∗
    walSnapCert γn.cl σ ∗ walSnapDur νk.sd σ ∗ isCommittedLogLb γn.cl l)

/-- The cluster's persistent facts (`memberGen`'s first row) at the generation. -/
def memberClusterFacts (C : etcd_dist.MemberCl) : IProp GF :=
  etcdstart.clusterFacts C.γ C.γk C.issued C.cnt C.wn C.fs C.gen

end durDefs

section dur
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable {GF : BundledGFunctors} {G : GooseGlobalGS HasLC.hasLC GF}
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **Raft's durable state is the same at any generation** (it names only global ghost state). -/
theorem memberDurOut_gen (L L' : GooseLocalGS GF) (γn : SrvRaft) (id : w64) (νk : WalNamesK GF)
    (S : RaftState) (σ : StorContents) (l : List LogEntry) :
    memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) γn id νk S σ l ⊣⊢
      memberDurOut (hG := ⟨G, etcd_dist.atCtx L'⟩) γn id νk S σ l := .rfl

/-- **The member's durable raft state and its WAL's files after a crash** (the T2 and T5 part of the
assembly): from the old generation `L`'s `memberDurKeep`, the cluster, a later credit, `crashed`, and
the WAL's crash at the new generation `L'` (`memberWalCrash`, from `walInv_crash`; both at the
statement's Go context, `atCtx`): raft's durable state `memberDurOut` and the new generation's WAL files
holding its records (`walFilesC`). T2's callback runs T5's `walRecsH_crash` at the new generation
(`walRecsH_gen`); T2's stop case is refuted by the stop's token (`rnTakenK_stop`). -/
theorem memberDur_crash (L L' : GooseLocalGS GF) (γn : SrvRaft) (id cid : w64) (νk : WalNamesK GF)
    (h : WalH GF) (W' : WalFs.WalGS GF) (hmd : h.md = walMetaEnc id cid) (E : CoPset)
    (hE : ↑rnDurKN ⊆ E) (hE' : ↑srvClusterN ⊆ E \ ↑rnDurKN) :
    ⊢ memberDurKeep (hG := ⟨G, etcd_dist.atCtx L⟩) γn id νk h -∗
      isCluster γn.cl srvClusterN -∗ £ 1 -∗
      crashed (hC := (etcd_dist.atCtx L).goose_crashGS) -∗
      memberWalCrash (hG := ⟨G, etcd_dist.atCtx L'⟩) h W' ={E}=∗
      ∃ (S : RaftState) (σ : StorContents) (l : List LogEntry),
        walFilesC (hG := ⟨G, etcd_dist.atCtx L'⟩) { h.toWalA with W := W' } id cid σ true ∗
        memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) γn id νk S σ l := by
  iintro Hk #Hcl Hlc1 Hcr Hw
  iunfold memberDurKeep at Hk
  icases Hk with ⟨#Hinv, Htk, Hx, Hst⟩
  imod rnDurK_crash_law_holds (hG := ⟨G, etcd_dist.atCtx L⟩) γn id νk h E
    (fun σ => walFilesC (hG := ⟨G, etcd_dist.atCtx L'⟩) { h.toWalA with W := W' } id cid σ true) hE hE' $$
    Hinv Hcl Hlc1 Hcr Htk Hx [Hw] with (⟨%S, %σ, %l, Hf, HrS, Hvac, %hp, #Hsc, #Hsd, #Hl⟩ | Htaken)
  · iintro %σr %Hs %n Hr Hsy
    ihave Hr := (walRecsH_gen (G := G) L L' h σr Hs true).1 $$ Hr
    iunfold memberWalCrash at Hw
    icases Hw with ⟨Hw, Hc⟩
    iunfold memberWalCrashW at Hw
    icases Hw with ⟨Hcw, Hu⟩
    icases walRecsH_crash (hG := ⟨G, etcd_dist.atCtx L'⟩) h W' σr Hs n id cid hmd $$
      [Hcw Hr Hsy Hu Hc] with ⟨Hr, %j, %hj, Hf⟩
    · iframe Hcw Hr Hsy Hu Hc
    ihave Hr := (walRecsH_gen (G := G) L L' h σr Hs true).2 $$ Hr
    imodintro
    iframe Hr
    iexists j
    isplitr
    · ipureintro; exact hj
    iintro %σ' %hr
    iapply Hf
    ipureintro; exact hr
  · imodintro
    iexists S, σ, l
    iframe Hf
    iunfold memberDurOut
    iframe HrS Hvac Hsc Hsd Hl
    ipureintro; exact hp
  · imod rnTakenK_stop (hG := ⟨G, etcd_dist.atCtx L⟩) γn id νk h E hE $$ Hinv Htaken Hst with %hF
    exact hF.elim

/-- **The WAL area's crash** (`walInv_crash` at the member's WAL, first of the crash lemmas: no file
taken before it): from `memberWalKeep` at the old generation `L`, its `crashed` and the crash rest
(whose premise `Q` gives W1, `hQ`), a new generation `W'` of the WAL's names with the crash view and
its lock token (`memberWalCrashW`, at `L'`), the crashed tree well formed, and the crash rest with the
area's files taken. (The new generation's area resources, `walStart` and its boot files, are dropped:
`memberGen`'s restart case holds only the files, `srvFilesC`; the restarted server's WAL area is
`bootstrap`'s crash contract's.) -/
theorem memberWal_crash (L L' : GooseLocalGS GF) (h : WalH GF) (Q : Fs.OsState → Fs.OsState → Prop)
    (hQ : ∀ st st', Q st st' → WalFs.W1 walCodec st st') (V' : Fs.Hist) (E : CoPset)
    (hE : ↑WalFs.walN ⊆ E) (hE' : ↑Fs.osShN ⊆ E) :
    letI := h.ext; letI := h.semOk; letI := h.has;
    ⊢ memberWalKeep (hG := ⟨G, etcd_dist.atCtx L⟩) h -∗
      crashed (hC := (etcd_dist.atCtx L).goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := etcd_dist.atCtx L)) (Fs.gooseOsGS (L := etcd_dist.atCtx L'))
        [] false V' ={E}=∗
      ∃ (W' : WalFs.WalGS GF) (D : List Fs.Ino),
        memberWalCrashW (hG := ⟨G, etcd_dist.atCtx L'⟩) h W' ∗ ⌜W'.roots = h.R ∧ Fs.TreeWf h.R V'.now⌝ ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := etcd_dist.atCtx L)) (Fs.gooseOsGS (L := etcd_dist.atCtx L'))
          D false V' := by
  letI := h.ext; letI := h.semOk; letI := h.has
  iintro Hk Hcr Hrest
  iunfold memberWalKeep at Hk
  icases Hk with ⟨Hinv, Hct, #Hsh⟩
  imod WalFs.walInv_crash walCodec walCodec_ok walSrvMr Q hQ ⟨G.gooseAllG⟩ (etcd_dist.atCtx L)
    (etcd_dist.atCtx L') h.W h.R h.jr h.r V' [] (fun _ h => absurd h (List.not_mem_nil)) E hE hE' $$
    Hinv Hcr Hct Hsh Hrest with ⟨%W', %s', %D', Hcw, %hp, -, -, Hu, -, -, Hrest⟩
  imodintro
  iexists W', D' ++ []
  iframe Hrest
  isplitl [Hcw Hu]
  · iunfold memberWalCrashW
    iframe Hcw Hu
  · ipureintro; exact ⟨hp.1, hp.2.2.2.2.2.1⟩

/-- **The cluster's facts are the same at any generation** (persistent ghost and invariant facts). -/
theorem memberClusterFacts_gen (L L' : GooseLocalGS GF) (C : etcd_dist.MemberCl) :
    memberClusterFacts (hG := ⟨G, etcd_dist.atCtx L⟩) C ⊣⊢
      memberClusterFacts (hG := ⟨G, etcd_dist.atCtx L'⟩) C := .rfl

/-- **A restart's facts carry over to any generation** (the lease configuration's is the one sealed
fact that names the generation: at the lease mode `none` it holds at every generation). -/
theorem memberRestartFacts_gen (L L' : GooseLocalGS GF) (γ : SrvRaft) (ρ : ReqNames) (id : w64) :
    etcdstart.memberRestartFacts (hG := ⟨G, etcd_dist.atCtx L⟩) γ ρ id ⊢
      etcdstart.memberRestartFacts (hG := ⟨G, etcd_dist.atCtx L'⟩) γ ρ id := by
  unfold etcdstart.memberRestartFacts
  refine sep_mono (BI.pure_mono ?_) ?_
  rotate_left
  · iintro ⟨%hns, #H1, #H2, #H3, #H4, #H5, #H6, #H7, %x, #H8⟩
    isplitr; · ipureintro; exact hns
    isplitr; · iexact H1
    isplitr; · iexact H2
    isplitr; · iexact H3
    isplitr; · iexact H4
    isplitr; · iexact H5
    isplitr; · iexact H6
    isplitr; · iexact H7
    iexists x; iexact H8
  rintro ⟨a, b, c, d, e, f, g⟩
  refine ⟨a, b, c, d, e, f, ?_⟩
  rw [lease.runCfg_lm g]
  exact lease.runCfg_none (hG := ⟨G, etcd_dist.atCtx L'⟩)

end dur

end memberCrash
end EtcdGrove
end Perennial
