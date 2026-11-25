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
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrashRes
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CrashInterim

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

/-- **A restart's facts carry over to another generation but one** (B6, found 2026-11-25): the
lease configuration (sealed, generation-named) holds at every generation at the lease mode `none`, and
every other row is ghost-only, except **`idPfxInv`**, which is heap-level: its invariant holds
persistent points-to facts of the prefix's generators (`structFieldRef … ↦□`) on the old machine's heap,
which no later generation has. So the new generation's `idPfxInv` (at the old incarnation's names
`ρo.ids.gen`, whose map authorities the old invariant keeps) is an input here. -/
theorem memberRestartFacts_gen (L L' : GooseLocalGS GF) (γ : SrvRaft) (ρ : ReqNames) (id : w64) :
    etcdstart.memberRestartFacts (hG := ⟨G, etcd_dist.atCtx L⟩) γ ρ id ∗
      idPfxInv (hG := ⟨G, etcd_dist.atCtx L'⟩) ρ.ids.gen ρ.ids.pfx ⊢
      etcdstart.memberRestartFacts (hG := ⟨G, etcd_dist.atCtx L'⟩) γ ρ id := by
  unfold etcdstart.memberRestartFacts
  iintro ⟨⟨%hp, %hns, #H1, #H2, -, #H4, #H5, #H6, #H7, %x, #H8⟩, #H3⟩
  isplitr
  · ipureintro
    obtain ⟨a, b, c, d, e, f, g⟩ := hp
    refine ⟨a, b, c, d, e, f, ?_⟩
    rw [lease.runCfg_lm (hG := ⟨G, etcd_dist.atCtx L⟩) g]
    exact lease.runCfg_none (hG := ⟨G, etcd_dist.atCtx L'⟩)
  isplitr; · ipureintro; exact hns
  isplitr; · iexact H1
  isplitr; · iexact H2
  isplitr; · iexact H3
  isplitr; · iexact H4
  isplitr; · iexact H5
  isplitr; · iexact H6
  isplitr; · iexact H7
  iexists x; iexact H8

end dur

/-! ## The snapshot directory's claims at the new generation (D-T7-4)

`snapDir_crash.law` takes, at the new generation, `snap.snapDirOwn` and one fresh claim per index
(`snapSlot`). Both come from the new generation's whole claim on the snapshot directory `J`
(`osShared`'s, `crashRest_treeS'`): split along `snap.snapDirNames` (`WalFs.osNames_split_only`), the
index names' claims turned into slots by induction over the index list, each slot taking half of what the
previous one left of the path's and the call permission's shares. Nothing unfolds `snap.allW64` (a
choice) and no step searches the context while a `[∗list]` over it is there (CLAUDE.md, "Large
contexts"). -/

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Slots from the index names' claims** (by induction over the indices `l`; the path's and the call
permission's shares halved at each index, the rest returned). -/
theorem snapSlots_of (R : Roots) (sd : GoString) (J : Ino) (V : Hist)
    (hfit : ∀ i, PathFits (snap.snapDBPath sd i)) : ∀ (l : List w64) (q qc : Qp),
    ⊢ osInv (GF := GF) -∗ osSharedInv R -∗ osPathS R sd (DFrac.own q) J -∗
      osCallPerm (callKey R sd) qc -∗
      ([∗list] i ∈ l, osNames J (.only [snap.snapDBName i]) (DFrac.own 1)
        (namesOf V J (.only [snap.snapDBName i]))) -∗
      ([∗list] i ∈ l, snapCrash.snapSlotF sd J V i) ∗
      ∃ (q' qc' : Qp), osPathS R sd (DFrac.own q') J ∗ osCallPerm (callKey R sd) qc'
  | [], q, qc => by
    iintro #Hinv #Hsh Hp Hc -
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iexists q, qc
    isplitl [Hp]
    · iexact Hp
    · iexact Hc
  | i :: l, q, qc => by
    iintro #Hinv #Hsh Hp Hc Hl
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hi, Hl⟩
    rw [← Qp.half_add_half q, ← Qp.half_add_half qc]
    icases (osPathS_frac R sd q.half q.half J).1 $$ Hp with ⟨Hp1, Hp2⟩
    icases (osCallPerm_split (callKey R sd) qc.half qc.half).1 $$ Hc with ⟨Hc1, Hc2⟩
    icases snapSlots_of R sd J V hfit l q.half qc.half $$ Hinv Hsh Hp2 Hc2 Hl with ⟨Hl, Hrest⟩
    isplitl [Hi Hp1 Hc1 Hl]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hi Hp1 Hc1]
      · unfold snapCrash.snapSlotF
        iexists R, DFrac.own q.half, qc.half
        isplitr; · iexact Hinv
        isplitr; · iexact Hsh
        isplitl [Hp1]; · iexact Hp1
        isplitl [Hc1]; · iexact Hc1
        isplitl [Hi]; · iexact Hi
        ipureintro; exact hfit i
      · iexact Hl
    · iexact Hrest

/-- **The new generation's claim on the snapshot directory, carved** (D-T7-4): its whole claim on `J`
(with a share of `sd`'s path and of its call permission) gives every index's slot (`snapSlotF`, what
`snapDir_crash.law`'s `snapSlot` is at the program's instances), the claim on the backend file's name
`db` (the backend's, B1), and the claim on the rest with shares of the path and the call permission
(`snap.snapDirOwn`'s body). -/
theorem snapDir_split (R : Roots) (sd : GoString) (J : Ino) (V : Hist) (q qc : Qp) (E : CoPset)
    (hE : ↑osShN ⊆ E) (hfit : ∀ i, PathFits (snap.snapDBPath sd i)) :
    ⊢ osInv (GF := GF) -∗ osSharedInv R -∗ osPathS R sd (DFrac.own q) J -∗
      osCallPerm (callKey R sd) qc -∗
      osNames J (.except []) (DFrac.own 1) (namesOf V J (.except [])) ={E}=∗
      ([∗list] i ∈ snap.allW64, snapCrash.snapSlotF sd J V i) ∗
      osNames J (.only [go!"db"]) (DFrac.own 1) (namesOf V J (.only [go!"db"])) ∗
      ∃ (q' qc' : Qp), osPathS R sd (DFrac.own q') J ∗ osCallPerm (callKey R sd) qc' ∗
        osNames J (.except snap.snapDirNames) (DFrac.own 1) (namesOf V J (.except snap.snapDirNames)) := by
  iintro #Hinv #Hsh Hp Hc Hn
  imod WalFs.osNames_split_only _ R V J E hE snap.snapDirNames [] bootSnap.snapNames_nodup
    (fun _ _ h => by simp at h) $$ Hsh Hn with ⟨Hr, Hl⟩
  rw [List.nil_append]
  unfold snap.snapDirNames
  icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hdb, Hl⟩
  rw [BigSepL.bigSepL_map]
  icases snapSlots_of R sd J V hfit snap.allW64 q qc $$ Hinv Hsh Hp Hc Hl with ⟨Hs, Hrest⟩
  imodintro
  isplitl [Hs]
  · iexact Hs
  isplitl [Hdb]
  · iexact Hdb
  icases Hrest with ⟨%q', %qc', Hp, Hc⟩
  iexists q', qc'
  isplitl [Hp]; · iexact Hp
  isplitl [Hc]; · iexact Hc
  iexact Hr

end slots

/-! ## The member's keep and the named hypotheses (T7, session 4)

`memberKeep`: what a run keeps for its crash. Its restart case (`memberKeepR`) is over the run's names
(`MemberKN`); the parts no task delivers yet are the abstract pieces `KeepF` (B4: the first generation's
boot phases) and `KeepB` (B1: the backend's image facts, the snapshot directory's counter authority).
The second later credit is `snapDir_crash.law`'s (T8 deposits it). Each blocker enters the law as one
named hypothesis below (`abbrev <name>.law : Prop`), its docstring naming it. -/

section kn
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver in
/-- **The names a member's run keeps for its crash** (the restart case's witnesses). -/
structure MemberKN (GF : BundledGFunctors) where
  γ : SrvRaft
  ρo : ReqNames
  h : WalH GF
  νk : WalNamesK GF
  cid : w64
  γb : backend.DBNames
  i0 : Ino
  Dl : backend.Data
  Dn : backend.Data
  pd : Option backend.Data
  J : Ino
  γd : GName
  γm : GName

end kn

section keepDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- The snapshot directory's invariant's parameters in the member's image (`srvCrashImageAt`'s row). -/
abbrev memberSnapKeep (k : MemberKN GF) (dd : GoString) : IProp GF :=
  snapDirKeep (config.snapDirOf dd) k.γd (srvImageM k.γ.authOn k.γ)
    (fun j => monoNatLbOwn k.γm (uint.nat j + 1))

/-- **What a restartable run of member `id` keeps for a crash** (the restart case of `memberKeep`): the
restart's facts at the run's names, raft's durability (`memberDurKeep`, with the stop's token: D-T7-3),
the WAL area (`memberWalKeep`), the backend file's crash record (`dbCrashKeep`, A1), the snapshot
directory's invariant with its token (`snapDirKeep`), the snapshot directory's durable path
(`osPathDur`, D-T7-4: T8's boot makes it), the program's file-system context (B7: `snapDir_crash.law`
and `onFs` are at `theFs`), and the abstract piece `KeepB k` (B1). -/
def memberKeepR (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepB : MemberKN GF → IProp GF) : IProp GF :=
  iprop(∃ k : MemberKN GF,
    ⌜(∃ r : GName, k.γ = { C.γ with reg := r }) ∧ k.h.dir = srvWalDirOf cfg.DataDir' ∧
      k.h.md = walMetaEnc id k.cid ∧ k.γ.snapLoc id = some k.γd ∧ (∃ c, theFs GF = some c)⌝ ∗
    etcdstart.memberRestartFacts k.γ k.ρo id ∗ memberDurKeep k.γ id k.νk k.h ∗ memberWalKeep k.h ∗
    backend.dbCrashKeep k.γb (config.backendPathOf cfg.DataDir') k.i0 k.Dl k.Dn k.pd ∗
    memberSnapKeep k cfg.DataDir' ∗ osPathDur k.h.R (config.snapDirOf cfg.DataDir') k.J ∗ KeepB k)

/-- **The image rows the backend owes** (B1's output; `srvCrashImageAt`'s backend rows at the run's names):
a committed prefix `A` reaching the backend's index `i`, the backend's data `D` its image (`imageRestAt`,
`imageStOk`, `mvccImage`), the membership `m` at `i`, the backend file holding `D` under its name, and the
snapshot directory's counter's authority at most `i + 1`. -/
def memberImageRows (k : MemberKN GF) (dd : GoString) (i : w64) (A : List EntryModel) (D : backend.Data)
    (m : Membership) : IProp GF :=
  iprop(srvRLogLb k.ρo.rd.raft A ∗
    ⌜uint.Z i = uint.Z k.ρo.rd.raft.ai0 + A.length ∧
      imageRestAt k.ρo.rd.kv k.γ.boot i (k.ρo.rd.raft.pre ++ A) D ∧
      imageStOk (kvModel k.ρo.rd.kv A) (crevOf k.ρo.rd.kv A)⌝ ∗
    (∃ u : Bool, mvcc.api.mvccImage D (kvModel k.ρo.rd.kv A) (crevOf k.ρo.rd.kv A) u) ∗
    confAt k.γ.cl (uint.nat i) m ∗ ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝ ∗
    backend.fileHolds (config.backendPathOf dd) D ∗
    (∃ c : Nat, ⌜c ≤ uint.nat i + 1⌝ ∗ monoNatAuthOwn k.γm 1 c))

/-- **B2** (Q3, the received-snapshot window): the WAL's snapshot is at or below the backend's index.
**False in some runs as stated** (a crash between `SaveSnap` and the rename of `<k>.snap.db` onto `db`);
replaced by T4's restatement of `srvCrashImageAt` (ledger 2026-11-25). -/
def memberImageB (σ : StorContents) (i : w64) : Prop := σ.b ≤ uint.nat i

/-- **B3** (C-I1 checkpoint item 7): the backend's index is at least the bootstrap log's length. **False
in some runs as stated** (after the first `Save`, before the backend's first commit, `i = 0`); replaced by
T4's restatement of `srvCrashImageAt` (ledger 2026-11-25). -/
def memberImageBoot (γ : SrvRaft) (i : w64) : Prop := γ.cl.bootLen ≤ uint.nat i

end keepDefs

section keep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **What the run of generation `L` keeps for its crash** (`memberGen_crash.law`'s `Keep`): the cluster's
facts, a second later credit (`snapDir_crash.law`'s; T8's obligation), and the first generation's keep
`KeepF L` (B4) or a restartable run's (`memberKeepR`). -/
def memberKeep (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepF : GooseLocalGS GF → IProp GF) (KeepB : GooseLocalGS GF → MemberKN GF → IProp GF)
    (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS HasLC.hasLC GF := ⟨G, etcd_dist.atCtx L⟩
  iprop(memberClusterFacts C ∗ £ 1 ∗ (KeepF L ∨ memberKeepR C cfg id (KeepB L)))

/-- **B4, the first generation's boot phases** (named hypothesis): a crash of a first generation (before
`newRaftNode` allocates raft's durability, or with an unsaved first `Save`) leaves a data directory from
which the next generation starts as a first one (`memberFirst`, with T3's leftovers). Needs T3 and T8's
boot (kvnet's `kd_boot_choose`). -/
abbrev memberFirstCrash.law (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (id : w64) (KeepF : GooseLocalGS GF → IProp GF) (Q : OsState → OsState → Prop) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (V' : Hist),
    L.goose_go_local_context = lctx → L'.goose_go_local_context = lctx →
    letI : HeapGS .hasLC GF := ⟨G, L⟩;
    (⊢ KeepF L -∗ £ 1 -∗ crashed (hC := L.goose_crashGS) -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] false V' -∗
      osInv (L := L') ={⊤}=∗ etcd_dist.memberFirst (hG := ⟨G, etcd_dist.atCtx L'⟩) C cfg id)

/-- **B1, the backend's image invariant** (named hypothesis; T10's): the run's keep `KeepB` and what the
crash left of the backend file (`dbCrash`'s `fileHoldsM i0 D'`, `D'` one of the record's data) and of raft
(`memberDurOut`), with the new generation's claim on the name `db` and shares of the snapshot directory's
path and call permission, give the image rows (`memberImageRows`) at some index `i`, with B2's and B3's
bounds (`memberImageB`, `memberImageBoot`: false in some runs as stated, see each). -/
abbrev memberImage.law (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepB : GooseLocalGS GF → MemberKN GF → IProp GF) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (V' : Hist) (k : MemberKN GF) (S : RaftState) (σ : StorContents)
    (l : List LogEntry) (D' : backend.Data) (q qc : Qp),
    (D' = k.Dl ∨ D' = k.Dn ∨ k.pd = some D') →
    ⊢ KeepB L k -∗ memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) k.γ id k.νk S σ l -∗
      bbolt.fileHoldsM (hG := ⟨G, etcd_dist.atCtx L'⟩) k.i0 D' -∗
      osPathS (L := etcd_dist.atCtx L') k.h.R (config.snapDirOf cfg.DataDir') (DFrac.own q) k.J -∗
      osCallPerm (L := etcd_dist.atCtx L') (callKey k.h.R (config.snapDirOf cfg.DataDir')) qc -∗
      osNames (L := etcd_dist.atCtx L') k.J (.only [go!"db"]) (DFrac.own 1)
        (namesOf V' k.J (.only [go!"db"])) ={⊤}=∗
      ∃ (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership),
        memberImageRows (hG := ⟨G, etcd_dist.atCtx L'⟩) k cfg.DataDir' i A D m ∗
        ⌜memberImageB σ i ∧ memberImageBoot k.γ i⌝

/-- **B6, the prefix generators' invariant at the new generation** (named hypothesis; ledger 2026-11-25,
"`memberGen`'s restart case asks for the old incarnation's `idPfxInv`"): `idPfxInv` is heap-level, so the
old incarnation's cannot be carried; `memberRestart` asks for it at the new generation. D7's / T8's to
restate. -/
abbrev memberPfx.law : Prop :=
  ∀ (L' : GooseLocalGS GF) (ρo : ReqNames),
    ⊢ |={⊤}=> idPfxInv (hG := ⟨G, etcd_dist.atCtx L'⟩) ρo.ids.gen ρo.ids.pfx

/-- **D-T7-1, T6's `snapDirKept` from the fixed-root form** (named hypothesis; ledger 2026-11-25, "T6's
`snapDirKept` is unprovable as stated"): the restatement makes `snapDirKeptF` `snapDirKeptR`'s body, and
this an identity. -/
abbrev snapDirKeptOf.law : Prop :=
  ∀ (L : GooseLocalGS GF) (R : Roots) (V' : Hist) (sd : GoString),
    ⊢ snapDirKeptR (hG := ⟨G, etcd_dist.atCtx L⟩) R V' sd -∗
      snapCrash.snapDirKeptF (hG := ⟨G, etcd_dist.atCtx L⟩) R V' sd

end keep

end memberCrash
end EtcdGrove
end Perennial
