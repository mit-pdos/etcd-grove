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
  `snapDirKept` at the law's own roots `R`) holds (`snapDirKeptR_of`). (D-T7-1, applied 2026-11-25 on
  `etcd-safe-t10`: T6's `snapDirKept` is now stated at `R`; its callers get `R0 = R` from `crashRest_roots`,
  moved to `SnapDirCrash.lean`.)

And, for the assembly's `Keep` (decision D-T7-3 of the plan): `rnTakenK_stop`, T2's crash law's second case
(the stop took the records) is refuted by the stop's token, which the member's run keeps (it never stops its
server).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberGen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapDirCrash
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrash
public import Proof.go_etcd_io.etcd.pkg.v3.idutil.PfxCrash
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

/-- **The crash kept the directory of `sd`** at the roots `R` (persistent): T6's `snapDirKeptF`
(`SnapDirCrash.lean`), since D-T7-1's restatement (2026-11-25) at the law's own roots: the same body. -/
def snapDirKeptR (R : Roots) (V' : Hist) (sd : GoString) : IProp GF :=
  iprop(□ ∀ (dq : DFrac) (j : Ino), osPathS R sd dq j -∗ ⌜lookupH R V' sd = some (.dir j)⌝)

instance snapDirKeptR_persistent (R : Roots) (V' : Hist) (sd : GoString) :
    Persistent (snapDirKeptR (GF := GF) R V' sd) := by
  unfold snapDirKeptR; infer_instance

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

/-- **The WAL area's crash** (`walInv_crash` at the member's WAL; the files `D` taken before it, none in
the area's directories): from `memberWalKeep` at the old generation `L`, its `crashed` and the crash rest
(whose premise `Q` gives W1, `hQ`), a new generation `W'` of the WAL's names with the crash view and
its lock token (`memberWalCrashW`, at `L'`), the crashed tree well formed, and the crash rest with the
area's files taken. (The new generation's area resources, `walStart` and its boot files, are dropped:
`memberGen`'s restart case holds only the files, `srvFilesC`; the restarted server's WAL area is
`bootstrap`'s crash contract's.) -/
theorem memberWal_crash (L L' : GooseLocalGS GF) (h : WalH GF) (Q : Fs.OsState → Fs.OsState → Prop)
    (hQ : ∀ st st', Q st st' → WalFs.W1 walCodec st st') (V' : Fs.Hist) (D : List Fs.Ino)
    (hD : ∀ i ∈ D, ¬ WalFs.InAreaDir V'.now h.jr i) (E : CoPset)
    (hE : ↑WalFs.walN ⊆ E) (hE' : ↑Fs.osShN ⊆ E) :
    letI := h.ext; letI := h.semOk; letI := h.has;
    ⊢ memberWalKeep (hG := ⟨G, etcd_dist.atCtx L⟩) h -∗
      crashed (hC := (etcd_dist.atCtx L).goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := etcd_dist.atCtx L)) (Fs.gooseOsGS (L := etcd_dist.atCtx L'))
        D false V' ={E}=∗
      ∃ (W' : WalFs.WalGS GF) (D' : List Fs.Ino),
        memberWalCrashW (hG := ⟨G, etcd_dist.atCtx L'⟩) h W' ∗
        ⌜W'.roots = h.R ∧ Fs.TreeWf h.R V'.now ∧ ∀ i ∈ D', WalFs.InAreaDir V'.now h.jr i⌝ ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := etcd_dist.atCtx L)) (Fs.gooseOsGS (L := etcd_dist.atCtx L'))
          (D' ++ D) false V' := by
  letI := h.ext; letI := h.semOk; letI := h.has
  iintro Hk Hcr Hrest
  iunfold memberWalKeep at Hk
  icases Hk with ⟨Hinv, Hct, #Hsh⟩
  imod WalFs.walInv_crash walCodec walCodec_ok walSrvMr Q hQ ⟨G.gooseAllG⟩ (etcd_dist.atCtx L)
    (etcd_dist.atCtx L') h.W h.R h.jr h.r V' D hD E hE hE' $$
    Hinv Hcr Hct Hsh Hrest with ⟨%W', %s', %D', Hcw, %hp, -, -, Hu, -, -, Hrest⟩
  imodintro
  iexists W', D'
  iframe Hrest
  isplitl [Hcw Hu]
  · iunfold memberWalCrashW
    iframe Hcw Hu
  · ipureintro; exact ⟨hp.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2⟩

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

/-! ## The snapshot directory's geometry after the crash (T7, session 5)

The member's snapshot directory `J` is `snap` in `member` in the data directory (a root `jd`): the keep holds that
spine durably (`osSpineDur jd [member, snap] J`), so the crashed tree has it (`walk_two`). Then (pure) no file of
`J` is in the WAL area's directories (`notInArea`: `J`'s parent is no root, the area `jr` is one), and the three
directories are distinct members of the tree (`spineDirs`); at the new generation their whole claims give the
path's spine at the fraction `1` and `J`'s whole claim (`snapClaims_new`). -/

section geom
variable [GooseExts]

theorem walk_two {m : Tree} {j J : Ino} {a b : GoString}
    (h : walk m (.dir j) [a, b] = some (.dir J)) :
    ∃ jm, m.entry j a = some (.dir jm) ∧ m.entry jm b = some (.dir J) := by
  simp only [walk] at h
  split at h
  · rename_i n hn
    cases n with
    | dir jm =>
      simp only [walk] at h
      split at h
      · rename_i n' hn'
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨jm, hn, hn'⟩
      · cases h
    | file f => simp [walk] at h
  · cases h

/-- **No file of the snapshot directory is in a WAL area's directory**: `J` is `b` in `jm`, itself a
child, and the area `jr` is a root. -/
theorem notInArea {R : Roots} {m : Tree} (hwf : TreeWf R m) {jd jm J jr x : Ino} {rw a b c : GoString}
    (h1 : m.entry jd a = some (.dir jm)) (h2 : m.entry jm b = some (.dir J)) (hr : (rw, jr) ∈ R)
    (hx : m.entry J c = some (.file x)) : ¬ WalFs.InAreaDir m jr x := by
  rintro ⟨J', b', a', he, hj⟩
  obtain ⟨rfl, -⟩ := hwf.2.2.2.2 J c J' b' _ hx he
  obtain ⟨hjm, -⟩ := hwf.2.2.2.2 jm b jr a' _ h2 hj
  subst hjm
  exact hwf.2.2.2.1 jd a jm h1 rw hr

/-- A directory of the tree is in `dirsOf`. -/
theorem mem_dirsOf {V : Hist} {j : Ino} (hm : j ∈ V.now) : j ∈ dirsOf V := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hm
  exact List.mem_map.2 ⟨(j, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩

/-- **The spine's directories**: in the tree and pairwise distinct. -/
theorem spineDirs {R : Roots} {m : Tree} (hwf : TreeWf R m) {jd jm J : Ino} {rd a b : GoString}
    (hd : (rd, jd) ∈ R) (h1 : m.entry jd a = some (.dir jm)) (h2 : m.entry jm b = some (.dir J)) :
    jd ∈ m ∧ jm ∈ m ∧ J ∈ m ∧ jd ≠ jm ∧ jd ≠ J ∧ jm ≠ J := by
  have hjd : jd ∈ m := hwf.1 jd (.root rd jd hd)
  have hjm : jm ∈ m := (hwf.2.2.1 jd a _ h1).2 jm (by simp [Node.dirIno])
  have hJ : J ∈ m := (hwf.2.2.1 jm b _ h2).2 J (by simp [Node.dirIno])
  refine ⟨hjd, hjm, hJ, ?_, ?_, ?_⟩
  · intro e; subst e; exact hwf.2.2.2.1 jd a jd h1 rd hd
  · intro e; subst e; exact hwf.2.2.2.1 jm b jd h2 rd hd
  · intro e; subst e
    obtain ⟨e, -⟩ := hwf.2.2.2.2 jd a jm b _ h1 h2
    subst e; exact hwf.2.2.2.1 jd a jd h1 rd hd

/-- The cur of a fresh claim on one name is the tree's entry. -/
theorem namesOf_only_cur (V : Hist) (j : Ino) (b : GoString) :
    (namesOf V j (.only [b])).cur !! b = V.now.entry j b := by
  unfold namesOf
  simp only
  rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), entsOf_lookup]

end geom

section newClaims
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

theorem nameOk_member : NameOk go!"member" := by unfold NameOk; decide

/-- **The new generation's claims on the snapshot directory's spine** (D-T7-4): out of the whole claims of
`osShared`, the path `dd/member/snap` at the fraction `1` and the snapshot directory's whole claim. -/
theorem snapClaims_new (R : Roots) (V : Hist) (dd sd : GoString) (jd jm J : Ino) (E : CoPset)
    (hE : ↑osShN ⊆ E) (hwf : TreeWf R V.now) (hR : RootsOk R) (hd : (dd, jd) ∈ R)
    (hsd : sd = joinPath dd [go!"member", go!"snap"])
    (h1 : V.now.entry jd go!"member" = some (.dir jm)) (h2 : V.now.entry jm go!"snap" = some (.dir J)) :
    ⊢ osSharedInv (GF := GF) R -∗
      ([∗list] j ∈ dirsOf V, osNames j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E}=∗
      osPathS R sd (DFrac.own 1) J ∗
      osNames J (.except []) (DFrac.own 1) (namesOf V J (.except [])) := by
  subst hsd
  obtain ⟨hjd, hjm, hJ, hne1, hne2, hne3⟩ := spineDirs hwf hd h1 h2
  iintro #Hsh Hall
  icases (BigSepL.bigSepL_perm (List.perm_cons_erase (mem_dirsOf hjd))).1 $$ Hall with Hall
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨Hd, Hall⟩
  icases (BigSepL.bigSepL_perm (List.perm_cons_erase
    ((List.mem_erase_of_ne (Ne.symm hne1)).2 (mem_dirsOf hjm)))).1 $$ Hall with Hall
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨Hm, Hall⟩
  icases (BigSepL.bigSepL_perm (List.perm_cons_erase
    ((List.mem_erase_of_ne (Ne.symm hne3)).2
      ((List.mem_erase_of_ne (Ne.symm hne2)).2 (mem_dirsOf hJ))))).1 $$ Hall with Hall
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨HJ, -⟩
  imod WalFs.osNames_split_only _ R V jd E hE [go!"member"] [] (by simp) (by simp) $$ Hsh Hd
    with ⟨-, Hd⟩
  icases BigSepL.bigSepL_singleton.1 $$ Hd with Hd
  imod WalFs.osNames_split_only _ R V jm E hE [go!"snap"] [] (by simp) (by simp) $$ Hsh Hm
    with ⟨-, Hm⟩
  icases BigSepL.bigSepL_singleton.1 $$ Hm with Hm
  imodintro
  iframe HJ
  unfold osPathS
  iexists dd, jd, [go!"member", go!"snap"]
  isplitl []
  · ipureintro
    refine ⟨hR, hd, ?_, rfl⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact nameOk_member
    · exact bootSnap.nameOk_snap
  simp only [osSpine]
  iexists _, jm
  iframe Hd
  isplitl []
  · ipureintro; rw [namesOf_only_cur]; exact h1
  iexists _, J
  iframe Hm
  isplitl [] <;> ipureintro
  · rw [namesOf_only_cur]; exact h2
  · rfl

/-- A root's path is not `[]`. -/
theorem root_ne_nil {R : Roots} (hR : RootsOk R) {r : GoString} {j : Ino} (hr : (r, j) ∈ R) :
    ([] : GoString) ≠ r := by
  obtain ⟨cs, hcs, -, hrc⟩ := (hR.2.2 _ hr).1
  intro h0
  rw [← h0] at hrc
  cases cs with
  | nil => exact hcs rfl
  | cons c cs => simp [joinPath] at hrc

/-- **Two roots' whole call permissions**, out of a generation's (`osCallPerms`), each at the key of a
path below it. -/
theorem osCallPerms_two (R : Roots) (r1 r2 p1 p2 : GoString) (j1 j2 : Ino) (hR : RootsOk R)
    (h1 : (r1, j1) ∈ R) (h2 : (r2, j2) ∈ R) (hne : r1 ≠ r2) (hu1 : IsUnder r1 p1) (hu2 : IsUnder r2 p2) :
    osCallPerms (GF := GF) R ⊢ osCallPerm (callKey R p1) 1 ∗ osCallPerm (callKey R p2) 1 := by
  rw [callKey_eq hR h1 hu1, callKey_eq hR h2 hu2]
  iintro Hp
  icases osCallPerms_root R r1 j1 hR h1 $$ Hp with ⟨H1, Hp⟩
  rw [callKey_eq hR h1 (.inl rfl)]
  have hl : GMap.delete r1 (GMap.delete [] (permMap R)) !! r2 = some () := by
    rw [GMap.lookup_delete_ne _ hne, GMap.lookup_delete_ne _ (root_ne_nil hR h2)]
    exact permMap_lookup R r2 (.inr ⟨j2, h2⟩)
  icases (BigSepM.bigSepM_delete (M := GMap GoString)
    (Φ := fun (r' : GoString) (_u : Unit) => osCallPerm (GF := GF) r' 1) (x := ()) hl).1 $$ Hp
    with ⟨H2, -⟩
  iframe H1 H2

/-- A whole call permission in halves. -/
theorem osCallPerm_halve (k : GoString) :
    osCallPerm (GF := GF) k 1 ⊢ osCallPerm k (1 : Qp).half ∗ osCallPerm k (1 : Qp).half := by
  have h := (osCallPerm_split (GF := GF) k (1 : Qp).half (1 : Qp).half).1
  rwa [Qp.half_add_half] at h

end newClaims

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
  J : Ino
  γd : GName
  γm : GName
  /-- the data directory's root inode (the snapshot directory's spine starts there) -/
  jd : Ino

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
directory's invariant with its token (`snapDirKeep`), the snapshot directory's durable spine
`member/snap` from the data directory's root `jd` (`osSpineDur`, D-T7-4: T8's boot makes it after the two
`TouchDirAll`s, as `osPathDur_child` does; session 5: the spine and not `osPathDur`, so that the crash law
knows `J`'s parent is no root), the program's file-system context (B7: `snapDir_crash.law` and `onFs` are at
`theFs`), and the abstract piece `KeepB k` (B1). Pure geometry (session 5, T8's from the boot's roots):
the data directory `dd` is a root at `jd`, the WAL area `h.r` a root at `h.jr`, other than `dd`, the WAL
directory below it, `snapDirOf dd` the path `dd/member/snap`, and its index files' paths fit
(`snapDir_split`'s premise). -/
def memberKeepR (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepB : MemberKN GF → IProp GF) : IProp GF :=
  iprop(∃ k : MemberKN GF,
    ⌜(∃ r : GName, k.γ = { C.γ with reg := r }) ∧ k.h.dir = srvWalDirOf cfg.DataDir' ∧
      k.h.md = walMetaEnc id k.cid ∧ k.γ.snapLoc id = some k.γd ∧ (∃ c, theFs GF = some c) ∧
      (cfg.DataDir', k.jd) ∈ k.h.R ∧ (k.h.r, k.h.jr) ∈ k.h.R ∧ k.h.r ≠ cfg.DataDir' ∧
      IsUnder k.h.r k.h.dir ∧
      config.snapDirOf cfg.DataDir' = joinPath cfg.DataDir' [go!"member", go!"snap"] ∧
      ∀ i, PathFits (snap.snapDBPath (config.snapDirOf cfg.DataDir') i)⌝ ∗
    etcdstart.memberRestartFacts k.γ k.ρo id ∗ memberDurKeep k.γ id k.νk k.h ∗ memberWalKeep k.h ∗
    backend.dbCrashKeep k.γb k.i0 k.Dl k.Dn ∗
    memberSnapKeep k cfg.DataDir' ∗ osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ KeepB k)

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
path and call permission, give the image rows (`memberImageRows`) at some index `i` (raft's state back), with B2's and B3's
bounds (`memberImageB`, `memberImageBoot`: false in some runs as stated, see each). -/
abbrev memberImage.law (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepB : GooseLocalGS GF → MemberKN GF → IProp GF) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (V' : Hist) (k : MemberKN GF) (S : RaftState) (σ : StorContents)
    (l : List LogEntry) (D' : backend.Data) (q qc : Qp),
    (D' = k.Dl ∨ D' = k.Dn) →
    ⊢ KeepB L k -∗ memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) k.γ id k.νk S σ l -∗
      bbolt.fileHoldsM (hG := ⟨G, etcd_dist.atCtx L'⟩) k.i0 D' -∗
      osPathS (L := etcd_dist.atCtx L') k.h.R (config.snapDirOf cfg.DataDir') (DFrac.own q) k.J -∗
      osCallPerm (L := etcd_dist.atCtx L') (callKey k.h.R (config.snapDirOf cfg.DataDir')) qc -∗
      osNames (L := etcd_dist.atCtx L') k.J (.only [go!"db"]) (DFrac.own 1)
        (namesOf V' k.J (.only [go!"db"])) ={⊤}=∗
      ∃ (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership),
        memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) k.γ id k.νk S σ l ∗
        memberImageRows (hG := ⟨G, etcd_dist.atCtx L'⟩) k cfg.DataDir' i A D m ∗
        ⌜memberImageB σ i ∧ memberImageBoot k.γ i⌝

/-- **B1's durable name of the backend file** (named hypothesis; T10's, with `memberImage.law`; session 5's
decision: in B1's keep `KeepB`, not in `memberKeepR`): every crash leaves the snapshot directory's name `db`
naming the record's inode `i0` (`dbCrash`'s premise `Named V'.now i0`, and where the file is for the
snapshot directory's crash). The backend's record `dbCrashKeep` claims no name (C-I1 restated 2026-11-25,
`notes/axiom-review/c-i1-nopath.md`), so the name's crash promise (a `nameCrash`) can be kept beside it; the
name's commits are the backend's run's (bbolt's `Open`, the
snapshot's rename `OpenSnapshotBackend` with `renamedDur`), which T10's invariant tracks. -/
abbrev memberDbNamed.law (KeepB : GooseLocalGS GF → MemberKN GF → IProp GF) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (k : MemberKN GF) (Q : OsState → OsState → Prop) (D : List Ino)
    (tt : Bool) (V' : Hist),
    ⊢ KeepB L k -∗
      crashRest Q (gooseOsGS (L := etcd_dist.atCtx L)) (gooseOsGS (L := etcd_dist.atCtx L')) D tt V' ={⊤}=∗
      ⌜V'.now.entry k.J go!"db" = some (.file k.i0)⌝ ∗ KeepB L k ∗
      crashRest Q (gooseOsGS (L := etcd_dist.atCtx L)) (gooseOsGS (L := etcd_dist.atCtx L')) D tt V'

end keep

/-! ## The restart's facts and image at the new generation (T7, session 6) -/

section restartImage
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- The restart's facts give the incarnation's raft names and the cluster. -/
theorem memberRestartFacts_cluster (γ : SrvRaft) (ρ : ReqNames) (id : w64) :
    etcdstart.memberRestartFacts (GF := GF) γ ρ id ⊢
      ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.c0 = W64 0⌝ ∗ isCluster γ.cl srvClusterN := by
  unfold etcdstart.memberRestartFacts
  iintro ⟨%hp, -, #Hs, -⟩
  obtain ⟨h1, h2, -⟩ := hp
  isplitr
  · ipureintro; exact ⟨h1, h2⟩
  rw [show γ = ρ.rd.raft.raft by rw [h1]]
  iunfold srvRaftLogInv at Hs
  icases Hs with ⟨-, Hok, -⟩
  iunfold srvClusterOk at Hok
  icases Hok with ⟨Hc, -⟩
  iexact Hc

/-- **The restart's facts at a fresh storage registry `r`** (Q4): none of them reads the registry. -/
theorem memberRestartFacts_reg (γ : SrvRaft) (ρ : ReqNames) (id : w64) (r : GName)
    (hr : ρ.rd.raft = ⟨γ, [], W64 0⟩) :
    etcdstart.memberRestartFacts (GF := GF) γ ρ id ⊢
      etcdstart.memberRestartFacts { γ with reg := r }
        { ρ with rd := { ρ.rd with raft := ⟨{ γ with reg := r }, [], W64 0⟩ } } id := by
  unfold etcdstart.memberRestartFacts
  rw [hr]
  refine BI.sep_mono (BI.pure_mono ?_) .rfl
  rintro ⟨-, a, b, c, d, e, f⟩
  exact ⟨rfl, a, b, c, d, e, f⟩

/-- **The crash image** (`srvCrashImageAt`) at the fresh registry `r'`, from raft's durable state (T2), the
backend's rows (B1, with B2's and B3's bounds), the WAL's files (T5), the snapshot directory's invariant
with its crash token (T6; D-T7-2) and the fresh registry's authority. -/
theorem crashImage_of (k : MemberKN GF) (id : w64) (dd : GoString) (r' : GName) (S : RaftState)
    (σ : StorContents) (l : List LogEntry) (i : w64) (A : List EntryModel) (D : backend.Data)
    (m : Membership) (W' : WalFs.WalGS GF)
    (hρ : k.ρo.rd.raft = ⟨k.γ, [], W64 0⟩) (hc0 : k.ρo.rd.kv.c0 = W64 0)
    (hdir : k.h.dir = srvWalDirOf dd) (hsl : k.γ.snapLoc id = some k.γd)
    (hB : memberImageB σ i ∧ memberImageBoot k.γ i) :
    memberDurOut k.γ id k.νk S σ l ∗ memberImageRows k dd i A D m ∗
      walFilesC { k.h.toWalA with W := W' } id k.cid σ true ∗
      snapDirKeep (config.snapDirOf dd) k.γd (srvImageM k.γ.authOn k.γ)
        (fun j => monoNatLbOwn k.γm (uint.nat j + 1)) ∗
      ghostMapAuth r' 1 (∅ : GMap Loc MemStorNamesRec) ⊢
    srvCrashImageAt { k.γ with reg := r' }
      { k.ρo with rd := { k.ρo.rd with raft := ⟨{ k.γ with reg := r' }, [], W64 0⟩ } } id dd S σ i A D m ∅ := by
  have e1 : srvRLogLb (GF := GF) ⟨k.γ, [], W64 0⟩ A ⊢
      srvRLogLb ({ k.ρo with rd := { k.ρo.rd with raft := ⟨{ k.γ with reg := r' }, [], W64 0⟩ } } : ReqNames).rd.raft
        A := .rfl
  have e2 : ghostMapAuth (GF := GF) r' 1 (∅ : GMap Loc MemStorNamesRec) ⊢
      (letI : MemStorReg GF := ⟨({ k.γ with reg := r' } : SrvRaft).reg⟩; memStorRegAuth ∅) := .rfl
  have e3 : snapDirKeep (GF := GF) (config.snapDirOf dd) k.γd (srvImageM k.γ.authOn k.γ)
        (fun j => monoNatLbOwn k.γm (uint.nat j + 1)) ⊢
      snapDirKeep (config.snapDirOf dd) k.γd
        (srvImageM ({ k.γ with reg := r' } : SrvRaft).authOn { k.γ with reg := r' })
        (fun j => monoNatLbOwn k.γm (uint.nat j + 1)) := .rfl
  unfold memberDurOut memberImageRows srvCrashImageAt wal.crashImageR srvFilesC confRowW snapRowB2
  rw [hρ]
  iintro ⟨⟨HrS, Hvac, %hp, Hsc, -, Hl⟩, ⟨HA, %hi, Hmv, Hconf, %hcs, Hfh, %c, %hc, Hauth⟩, Hwf, Hinv, Hreg⟩
  obtain ⟨hS, hb, hag, hrf⟩ := hp
  obtain ⟨hB2, -⟩ := hB
  isplitl [Hvac]; · iexact Hvac
  isplitl [HrS]; · iexact HrS
  isplitr; · ipureintro; exact ⟨rfl, hc0⟩
  isplitl [HA]; · iapply e1; iexact HA
  isplitr; · ipureintro; exact hi
  isplitl [Hmv]; · iexact Hmv
  isplitl [Hconf]; · iexact Hconf
  isplitr; · ileft; ipureintro; exact hcs
  isplitl [Hsc Hl]
  · isplitr
    · ipureintro; exact ⟨hS, hrf⟩
    isplitl [Hsc]; · iexact Hsc
    iexists l
    isplitl [Hl]; · iexact Hl
    ipureintro; exact ⟨hb, hag⟩
  isplitl [Hreg]; · iapply e2; iexact Hreg
  isplitl [Hwf Hfh]
  · isplitl [Hwf]
    · iexists { k.h.toWalA with W := W' }, k.cid
      isplitr; · ipureintro; exact hdir
      iexact Hwf
    iexact Hfh
  iexists k.γd, k.γm, c
  isplitr; · ipureintro; exact hsl
  isplitr; · ileft; ipureintro; exact ⟨hB2, hc⟩
  isplitl [Hinv]; · iapply e3; iexact Hinv
  iexact Hauth

end restartImage

/-! ## The member's crash law (T7) -/

section main
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [Sf : ExtSemantics fsExt] [Of : FsSemOk] [Hf : HasExt fsExt] [Hi : HasExt idIssueExt]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **The member's crash law** (T7; `memberGen_crash.law` at `memberKeep`), over the named hypotheses of
the tasks still open: the crash premise `Q`'s W1 (`hQ`) and bbolt's (`hA1`, until `etcdCQ` has it), B4
(`hB4`) and B1 (`hB1`, `hB1n`); D-T7-1 needs none since its restatement (2026-11-25), B6 none since (b)
(2026-11-26: the issue record's crash rest cancels the old prefix ids' invariant, `idPfxInv_crash`). -/
theorem memberGen_crash_law_holds (C : etcd_dist.MemberCl)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepF : GooseLocalGS GF → IProp GF) (KeepB : GooseLocalGS GF → MemberKN GF → IProp GF)
    (Q : OsState → OsState → Prop)
    (hQ : ∀ st st', Q st st' → WalFs.W1 walCodec st st')
    (hA1 : ∀ i0 st st', Q st st' → backend.BoltCrashWhole (· = i0) st st')
    (hB4 : memberFirstCrash.law C cfg id KeepF Q) (hB1 : memberImage.law cfg id KeepB)
    (hB1n : memberDbNamed.law KeepB) :
    etcd_dist.memberGen_crash.law C cfg id (memberKeep C cfg id KeepF KeepB) Q := by
  intro L L' V' hL hL'
  obtain ⟨fl, lc, nh, gs, th, cr⟩ := L
  obtain ⟨fl', lc', nh', gs', th', cr'⟩ := L'
  simp only at hL hL'
  subst hL hL'
  letI hG : HeapGS .hasLC GF := ⟨G, ⟨fl, lc', nh, gs, th, cr⟩⟩
  iintro Hk Hlc #Hcr Hrest Hic #Hosi
  iunfold memberKeep at Hk
  icases Hk with ⟨Hcf, Hlc2, (HF | HR)⟩
  · imod hB4 ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ V' rfl rfl $$ HF Hlc Hcr Hrest Hosi
      with Hm
    imodintro
    iunfold etcd_dist.memberGen
    isplitl [Hcf]
    · iunfold memberClusterFacts at Hcf; iexact Hcf
    ileft; iexact Hm
  -- the restart case
  iunfold memberKeepR at HR
  icases HR with ⟨%k, %hk, #Hrf, Hdur, Hwal, Hdb, Hsnap, #Hsp, HKB⟩
  obtain ⟨γ, ρo, ⟨⟨ext, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩,
    νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ := k
  obtain ⟨⟨rr, hγ⟩, hdir, hmd, hsl, ⟨c, hfs⟩, hdR, hrR, hrne, hunder, hsd, hfit⟩ := hk
  have hS : ext = Sf := has.sem_eq.symm.trans Hf.sem_eq
  subst hS
  obtain ⟨Sc, okc, hasc, fac, fsac, nec⟩ := c
  have hSc : Sc = ext := hasc.sem_eq.symm.trans Hf.sem_eq
  subst hSc
  haveI := inj
  -- the old generation's tree: the roots, the crashed tree well formed, the snapshot directory's spine
  iunfold memberWalKeep at Hwal
  icases Hwal with ⟨Hwi, Hwt, #Hsh⟩
  imod osSharedInv_rootsOk (L := ⟨fl, lc', nh, gs, th, cr⟩) R (E := ⊤) (by simp) $$ Hsh with %hRok
  imod crashRest_treeWf' Q ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ [] false V' R ⊤ (by simp) $$ Hsh Hrest with ⟨%hwf, Hrest⟩
  imod osSpineDur_crash Q ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ [] false V' R ⊤ (by simp) [go!"member", go!"snap"] jd J $$ Hsh Hrest Hsp
    with ⟨%hw, Hrest⟩
  obtain ⟨jm, h1, h2⟩ := walk_two hw
  -- the backend file (A1), at its durable name (B1's)
  imod hB1n ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ ⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ Q [] false V' $$ HKB Hrest with ⟨%hdb, HKB, Hrest⟩
  imod backend.dbCrash Q ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ γb i0 Dl Dn (hA1 i0) [] (by simp) V'
    ⟨J, _, hdb⟩ ⊤ $$ Hdb Hcr Hrest with ⟨%D', %hD', Hfm, Hrest⟩
  -- the WAL area (T5's crash)
  have hDw : ∀ i ∈ [i0], ¬ WalFs.InAreaDir V'.now jr i := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact notInArea hwf h1 h2 hrR hdb
  imod memberWal_crash ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩ Q hQ V' [i0] hDw ⊤ (by simp) (by simp) $$ [Hwi Hwt] Hcr Hrest
    with ⟨%W', %Dw, HwC, %hwp, Hrest⟩
  · iunfold memberWalKeep; iframe Hwi Hwt Hsh
  -- the new generation's tree
  imod crashRest_treeS' Q ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ (Dw ++ [i0]) V' R ⊤ (by simp) $$ Hsh Hrest with ⟨%hV2, Hsh', Hrest⟩
  iunfold osShared at Hsh'
  icases Hsh' with ⟨#Hsh1, -, Hperms, -, Hall⟩
  imod snapClaims_new (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) R V' cfg.DataDir' (config.snapDirOf cfg.DataDir') jd jm J ⊤ (by simp)
    hwf hRok hdR hsd h1 h2 $$ Hsh1 Hall with ⟨Hp, HJ⟩
  icases osCallPerms_two (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) R cfg.DataDir' r (config.snapDirOf cfg.DataDir') dir jd jr hRok hdR
    hrR hrne.symm (by rw [hsd]; exact isUnder_joinPath _ _) hunder $$ Hperms with ⟨Hcs, Hcw⟩
  icases osCallPerm_halve (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) _ $$ Hcw with ⟨Hcw1, Hcw2⟩
  -- the snapshot directory's claims at the new generation (D-T7-4)
  have hfs' := backend.theFs_eq GF (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (S := Sc) (ok := okc)
    (has := hasc) (fa := fac) (fsa := fsac) (ne := nec)
  imod snapDir_split (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) R (config.snapDirOf cfg.DataDir') J V' 1 1 ⊤ (by simp) hfit
    $$ Hosi Hsh1 Hp Hcs HJ with ⟨Hslots, Hdbn, %q', %qc', Hp', Hcs', Hex⟩
  rw [← Qp.half_add_half q', ← Qp.half_add_half qc']
  icases (osPathS_frac (L := ⟨fl', lc', nh', gs', th', cr'⟩) R _ q'.half q'.half J).1 $$ Hp' with ⟨Hpa, Hpb⟩
  icases (osCallPerm_split (L := ⟨fl', lc', nh', gs', th', cr'⟩) (callKey R (config.snapDirOf cfg.DataDir')) qc'.half qc'.half).1
    $$ Hcs' with ⟨Hca, Hcb⟩
  ihave Hown : snap.snapDirOwn (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (snap.snapDBPath (config.snapDirOf cfg.DataDir')) $$
    [Hpa Hca Hex]
  · iunfold snap.snapDirOwn
    rw [backend.onFs_some (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) hfs']
    iexists config.snapDirOf cfg.DataDir', R, J, q'.half, qc'.half, _
    isplitr; · ipureintro; rfl
    isplitr; · iexact Hosi
    isplitr; · iexact Hsh1
    iframe Hpa Hca Hex
  -- the snapshot directory kept (T7's premise of T6), and the files taken not in it
  ihave #Hpd : osPathDur (hG := ⟨G, ⟨fl, lc', nh, gs, th, cr⟩⟩) R (config.snapDirOf cfg.DataDir') J $$ [Hsp]
  · iunfold osPathDur
    iexists cfg.DataDir', jd, [go!"member", go!"snap"]
    isplitr
    · ipureintro
      refine ⟨hRok, hdR, ?_, hsd⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hc
      rcases hc with rfl | rfl
      · exact nameOk_member
      · exact bootSnap.nameOk_snap
    iexact Hsp
  imod osPathDur_lookup Q ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ (Dw ++ [i0]) true V' R ⊤ (by simp) _ J $$ Hsh Hrest Hpd
    with ⟨%hJ, Hrest⟩
  ihave #Hkr := snapDirKeptR_of ⟨fl, lc', nh, gs, th, cr⟩ R V' _ J hJ $$ Hpd
  ihave #Hkf : snapCrash.snapDirKeptF (hG := ⟨G, ⟨fl, lc', nh, gs, th, cr⟩⟩) R V' (config.snapDirOf cfg.DataDir') $$ []
  · iunfold snapCrash.snapDirKeptF; iunfold snapDirKeptR at Hkr; iexact Hkr
  have hD : ∀ x ∈ Dw ++ [i0], ∀ i, V'.now.entry J (snap.snapDBName i) ≠ some (.file x) := by
    intro x hx i hxi
    rcases List.mem_append.1 hx with hx | hx
    · exact notInArea hwf h1 h2 hrR hxi (hwp.2.2 x hx)
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨-, hn⟩ := hwf.2.2.2.2 J _ J _ _ hxi hdb
      have hl := congrArg List.length hn
      rw [bootSnap.snapDBName_length] at hl
      simp at hl
  have hlaw := snapCrash.snapDir_crash_law_holds (GF := GF) ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ _ _ Q true V' (Dw ++ [i0]) R J
    (config.snapDirOf cfg.DataDir') γd (srvImageM γ.authOn γ) (srvImageM (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) γ.authOn γ)
    (fun j => monoNatLbOwn γm (uint.nat j + 1)) (fun j => monoNatLbOwn γm (uint.nat j + 1)) hfs hfs' hV2 hJ hD
  have hslot : ∀ i, snapCrash.snapSlot (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (config.snapDirOf cfg.DataDir') J V' i =
      snapCrash.snapSlotF (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (config.snapDirOf cfg.DataDir') J V' i :=
    fun i => backend.onFs_some (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) hfs' _
  have hkept : snapCrash.snapDirKept (hG := ⟨G, ⟨fl, lc', nh, gs, th, cr⟩⟩) R V' (config.snapDirOf cfg.DataDir') =
      snapCrash.snapDirKeptF (hG := ⟨G, ⟨fl, lc', nh, gs, th, cr⟩⟩) R V' (config.snapDirOf cfg.DataDir') :=
    backend.onFs_some hfs _
  simp only [hslot, hkept] at hlaw
  ihave #Hrm : iprop(□ ∀ j : w64, monoNatLbOwn γm (uint.nat j + 1) -∗ monoNatLbOwn γm (uint.nat j + 1)) $$ []
  · imodintro; iintro %j Hj; iexact Hj
  -- the image certificate at the new generation's ghost state (mvcc's `mvccImage_gen`, lifted)
  ihave #Himgg : iprop(□ ∀ (j : w64) (Dt : backend.Data), srvImageM γ.authOn γ j Dt -∗
      srvImageM (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) γ.authOn γ j Dt) $$ []
  · imodintro; iintro %j %Dt Hj
    iapply (show srvImageM γ.authOn γ j Dt ⊢ srvImageM (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) γ.authOn γ j Dt from
      srvImageM_gen G ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ γ.authOn γ j Dt)
    iexact Hj
  imod hlaw $$ Hlc2 Hsnap Hcr Hrm Himgg Hkf [Hrest] Hown Hslots with ⟨%Dk, Hsnap', Hrest⟩
  · isplitr
    · iexact Hsh
    · iexact Hrest
  -- raft's durable state and the WAL's files (T2 + T5)
  ihave ⟨%hρ, #Hcl⟩ := memberRestartFacts_cluster γ ρo id $$ Hrf
  imod memberDur_crash (G := G) ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ γ id cid νk ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩ W' hmd ⊤ CoPset.subseteq_top
    (fun x h => mask_ndot_ne' nroot "raft_commit" "rnDurK" (by decide) x (srvClusterN_sub x h))
    $$ Hdur Hcl Hlc Hcr [HwC Hcw2] with ⟨%S, %σ, %l, Hwf, Hdo⟩
  · iunfold memberWalCrash; iframe HwC Hcw2
  -- the backend's image (B1)
  imod hB1 ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ V' ⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ S σ l D' q'.half qc'.half hD' $$ HKB Hdo Hfm Hpb Hcb Hdbn
    with ⟨%i, %A, %D, %m, Hdo, Himg, %hbnd⟩
  -- the fresh registry (Q4) and the prefix generators' invariant (B6)
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%r', Hreg⟩
  ihave #Hpfo : idPfxInv ρo.ids.gen ρo.ids.pfx $$ []
  · iunfold etcdstart.memberRestartFacts at Hrf
    icases Hrf with ⟨-, -, -, -, #Hp, -⟩
    iexact Hp
  imod (idPfxInv_crash (Gg := G) ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩
      (semL := sem) (semL' := sem) ρo.ids.gen ρo.ids.pfx)
    $$ Hpfo Hic with Hpfx
  ihave Hrf' := memberRestartFacts_gen (G := G) ⟨fl, lc', nh, gs, th, cr⟩ ⟨fl', lc', nh', gs', th', cr'⟩ γ ρo id $$ [Hpfx]
  · isplitr
    · iexact Hrf
    · iexact Hpfx
  ihave Hrf'' := memberRestartFacts_reg (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) γ ρo id r' hρ.1 $$ Hrf'
  imodintro
  iunfold etcd_dist.memberGen
  isplitl [Hcf]
  · iunfold memberClusterFacts at Hcf; iexact Hcf
  iright
  iunfold etcd_dist.memberRestart
  iexists { ρo with rd := { ρo.rd with raft := ⟨{ γ with reg := r' }, [], W64 0⟩ } }, { γ with reg := r' }
  isplitr
  · ipureintro; exact ⟨r', by subst hγ; rfl⟩
  isplitl [Hrf'']
  · iexact Hrf''
  iunfold srvCrashImage
  iexists S, σ, i, A, D, m, ∅
  iapply crashImage_of (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) ⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ id cfg.DataDir' r' S σ l i A D m W' hρ.1 hρ.2 hdir hsl hbnd
  isplitl [Hdo]
  · iapply (show memberDurOut (hG := ⟨G, etcd_dist.atCtx ⟨fl, lc', nh, gs, th, cr⟩⟩) γ id νk S σ l ⊢
      memberDurOut (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ : MemberKN GF).γ id (⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ : MemberKN GF).νk S σ l from .rfl)
    iexact Hdo
  isplitl [Himg]; · iexact Himg
  isplitl [Hwf]; · iexact Hwf
  isplitl [Hsnap']
  · iapply (show snapDirKeep (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (config.snapDirOf cfg.DataDir') γd
        (srvImageM (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) γ.authOn γ) (fun j => monoNatLbOwn γm (uint.nat j + 1)) ⊢
      snapDirKeep (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (config.snapDirOf cfg.DataDir') (⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ : MemberKN GF).γd (srvImageM (hG := ⟨G, ⟨fl', lc', nh', gs', th', cr'⟩⟩) (⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ : MemberKN GF).γ.authOn (⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ : MemberKN GF).γ)
        (fun j => monoNatLbOwn (⟨γ, ρo, ⟨⟨Sc, semOk, has, W, Sio, sat, satL, cov, R, jr, r, dir, fits, covP⟩, inj, w, γw, md, γh⟩, νk, cid, γb, i0, Dl, Dn, J, γd, γm, jd⟩ : MemberKN GF).γm (uint.nat j + 1)) from .rfl)
    iexact Hsnap'
  iexact Hreg

end main

end memberCrash
end EtcdGrove
end Perennial
