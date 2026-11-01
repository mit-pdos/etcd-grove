/-
**The backend's specs for the auth split (Draft; `notes/backend-auth-split-plan.md`).** Imported by
nothing. Statements top-down; the laws of the new opaque predicates are statements (`sorry`), the
glue and the compatibility corollaries are proved over them.

The user's decisions of 2026-11-01 (`notes/snapshot-auth-on-plan.md` on `snap-auth-on-draft`, "The
user's decisions on the restated Draft's questions"), what this module drafts for each:

1. **A read in progress needs no open share; `Close` waits for the readers.** The guard is at the
   acquisition: `readTx.RLock` (and `ConcurrentReadTx`, the batch locks) take an open share and give
   it back at once, as today; the held read (`BksDraft.backend.rtHeldF`, today's `rtHeldF` and "the
   read interval is live") needs none, so `readTx.UnsafeRange` takes none
   (`BksDraft.backend.readTx.UnsafeRange.spec`). `Close`'s statement is today's (`bOpen γ 1`): with
   no reader holding a share, the clients' whole open token is all it needs, and the reads begun
   before it (a held `readTx`, a `ConcurrentReadTx`) finish first in Go (`commit` takes
   `readTx.Lock()`; bbolt's `Close` waits for the read transactions). Today's specs are corollaries
   (`BksDraft.readTx.RLock.spec_old`, `BksDraft.readTx.UnsafeRange.spec_old`).
2. **Readers backed by thread tokens.** The backend's pool of reader slots (`BksDraft.backend.rdPool`,
   a `threadPool` of `rdTok`), from which a thread token borrows a slot for one read
   (`rdTok_borrow`, `rdTok_giveBack`); the glue `BksDraft.reader_RLock`/`reader_RUnlock`. Where the
   pool is built is a question for the user (the plan note, Q2): the candidate drafted here is
   `New`'s post (`BksDraft.backend.newPostK`, under `[ThreadBoundLe GF (2 ^ 29)]`, with the counted
   remainder `rdStock` for the clients that still count slots).
3. **Per-bucket idleness.** The client's part of the tracked buckets in a set `S`, possibly with a
   write of its own session pending (`BksDraft.backend.rbPart`: the writer's contents, what `rbOwn`
   is today), and the idle part (`BksDraft.backend.rbOwnIn`: no write to `S` pending, so the readers
   see it too). `rbOwn γ r` becomes `rbPart γ ⊤ r` (its text and meaning kept). A put needs its
   bucket's part only (`BksDraft.backend.rbPut`); `Unlock` turns any part the caller hands it into
   the idle part (`BksDraft.backend.batchTxBuffered.Unlock.spec`: Go writes the session back and
   commits a pending delete); `New` gives the whole idle (`newPostK`). The draft auth premise's split
   `backend.rbOwn_split_in`, restated over the idle part (`BksDraft.backend.rbOwnIn_split_compl`),
   and its use for the premise (`BksDraft.premise_buckets`).

Definitions redefining an existing one carry its name under `BksDraft.` (the merge drops it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeDelete
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Perennial.Proof.ThreadPool
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

/-! ## 1. The readers and `Close` (decision 1) -/

section readers
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The shared read transaction held, its interval live** (`rtHeldF`, redefined: today's and
`rd.live`). `RLock` takes an open share to know the backend has not stopped and gives it back; from
then on the interval stays live until `RUnlock`, since the stop's commit (`CommitAndStop` →
`commit`) takes `readTx.Lock()`, which waits for every reader. So a read in progress needs no open
share of its own (decision 1). -/
def BksDraft.backend.rtHeldF (γ : BNames) (P : BParams) (b : Loc) (rtx : Loc) (rv : RView) (p : Qp) :
    IProp GF :=
  iprop(∃ (rt : Loc) (rd : RdSt) (H : GMap (w64 × Nat) RView) (L : VData), bF go!"readTx" b ↦□ rt ∗
    sync.ownRWMutexRLocked (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
    rtResAt γ P rt sync.rfrac rd rv H p L ∗ ⌜rd.rtx = rtx ∧ rd.live = true⌝ ∗ crTok γ b)

/-- `BksDraft.backend.rtHeldF` at the reader's own share of bbolt's transaction. -/
abbrev BksDraft.backend.rtHeld (γ : BNames) (P : BParams) (b : Loc) (rtx : Loc) (rv : RView) :
    IProp GF :=
  BksDraft.backend.rtHeldF γ P b rtx rv sync.rfrac.half

/-- The live read is today's held read. -/
theorem BksDraft.rtHeldF_old (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (p : Qp) :
    BksDraft.backend.rtHeldF (GF := GF) γ P b rtx rv p ⊢ rtHeldF γ P b rtx rv p := by
  unfold BksDraft.backend.rtHeldF rtHeldF
  iintro ⟨%rt, %rd, %H, %L, #Hrt, Hl, HR, %Hx, Hc⟩
  iexists rt, rd, H, L
  iframe Hl HR Hc; iframe #
  ipureintro; exact Hx.1

/-- `readTx.mu`'s resource at a layout that is not live holds the stop's mark, which an open share
refutes. -/
theorem BksDraft.rtResAt_live (γ : BNames) (P : BParams) (rt : Loc) (q : Qp) (rd : RdSt) (rv : RView)
    (H : GMap (w64 × Nat) RView) (p : Qp) (L : VData) (qo : Qp) :
    rtResAt (GF := GF) γ P rt q rd rv H p L ∗ bOpen γ qo ⊢
      rtResAt γ P rt q rd rv H p L ∗ bOpen γ qo ∗ ⌜rd.live = true⌝ := by
  cases hl : rd.live
  · unfold rtResAt rtRest rtCore rtIntv
    simp only [hl, Bool.false_eq_true, ↓reduceIte]
    iintro ⟨⟨%m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs, Hcur, Hcln, Hhist, Hrtxf, Hwg, %Hfacts,
      #Hha, #Hcv, Hpo, #Hauth, ⟨-, #Hst⟩, #Hfk⟩, Ho⟩
    iexfalso
    iapply bOpen_stopped γ qo $$ [$Ho $Hst]
  · iintro ⟨HR, Ho⟩
    iframe HR Ho
    ipureintro; rfl

/-- Today's held read, with an open share, is live. -/
theorem BksDraft.rtHeldF_of_open (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView) (p qo : Qp) :
    rtHeldF (GF := GF) γ P b rtx rv p ∗ bOpen γ qo ⊢
      BksDraft.backend.rtHeldF γ P b rtx rv p ∗ bOpen γ qo := by
  unfold BksDraft.backend.rtHeldF rtHeldF
  iintro ⟨⟨%rt, %rd, %H, %L, #Hrt, Hl, HR, %Hx, Hc⟩, Ho⟩
  icases BksDraft.rtResAt_live γ P rt sync.rfrac rd rv H p L qo $$ [$HR $Ho] with ⟨HR, Ho, %Hlive⟩
  iframe Ho
  iexists rt, rd, H, L
  iframe Hl HR Hc; iframe #
  ipureintro; exact ⟨Hx, Hlive⟩

/-- **`rt.RLock()`, restated** (decision 1: the guard is here): an open share in and back at once,
the read held over the readers' state now, its interval live. -/
abbrev BksDraft.backend.readTx.RLock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (rt : Loc) (qo : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"readTx" b ↦□ rt ∗ rdTok γ P b ∗ bOpen γ qo }}
    (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RLock")) (Val #()))
  {{ RET #(); ∃ (rtx : Loc) (rv : RView), BksDraft.backend.rtHeld γ P b rtx rv ∗ bOpen γ qo }}

/-- **`rt.UnsafeRange(bucket, key, endKey, limit)`, restated** (decision 1): of the held, live read,
with any share `p` of bbolt's transaction, and **no open share**: `rtRange` of the readers' state (an
end key nil or not empty; no limit above 1 on a bucket that is not safe-range: that panics). Go: the
interval's bbolt transaction stays open while `readTx.mu` is read-locked (the commit that would roll
it back, and the stop's, take `readTx.Lock()`). -/
abbrev BksDraft.backend.readTx.UnsafeRange.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (rt : Loc) (rtx : Loc) (rv : RView) (p : Qp)
    (bk : GoInterface) (bi : BucketInfo) (key endKey : GoSlice) (kb eb : GoString) (dk de : DFrac)
    (limit : w64),
  (endKey = slice.nil ↔ eb = []) → (sint.Z (rangeLimit eb limit) ≤ 1 ∨ bi.safe = true) → P.has bi →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"readTx" b ↦□ rt ∗ BksDraft.backend.rtHeldF γ P b rtx rv p ∗ isBucket bk bi ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb }}
    (App (App (App (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"UnsafeRange")) (Val #bk))
      (Val #key)) (Val #endKey)) (Val #limit))
  {{ (keys vals : GoSlice), RET (PairV #keys #vals); BksDraft.backend.rtHeldF γ P b rtx rv p ∗
      key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗ kvsOutRd rtx keys vals (rtRange rv bi kb eb limit) }}

/-- **Today's `RLock` is a corollary** (the live read is today's held read). -/
theorem BksDraft.readTx.RLock.spec_old (h : BksDraft.backend.readTx.RLock.spec (GF := GF) (hG := hG)) :
    Perennial.EtcdGrove.backend.readTx.RLock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b rt qo
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, Hrd, Ho⟩ HΦ
  iapply (h γ P W Pk b rt qo) $$ %Φ [Hrd Ho]
  · iframe Hrd Ho; iframe #
  inext
  iintro ⟨%rtx, %rv, Hh, Ho⟩
  iapply HΦ
  iexists rtx, rv
  iframe Ho
  ihave Hh := BksDraft.rtHeldF_old γ P b rtx rv _ $$ Hh
  rw [Perennial.EtcdGrove.backend.rtHeld_eq]
  iexact Hh

/-- **Today's `UnsafeRange` is a corollary** (spot-check 1: every caller of today's statement, mvcc's
bridge `rtUR_held`, `rt_rangeLimF`, the restore's and the install's reads, goes through unchanged:
the open share it passes makes today's held read live, `rtHeldF_of_open`, and is framed). -/
theorem BksDraft.readTx.UnsafeRange.spec_old
    (h : BksDraft.backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG)) :
    Perennial.EtcdGrove.backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b rt rtx rv p qo bk bi key endKey kb eb dk de limit h1 h2 h3
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, Hh, Ho, #Hbk, Hk, He⟩ HΦ
  icases BksDraft.rtHeldF_of_open γ P b rtx rv p qo $$ [$Hh $Ho] with ⟨Hh, Ho⟩
  iapply (h γ P W Pk b rt rtx rv p bk bi key endKey kb eb dk de limit h1 h2 h3) $$ %Φ [Hh Hk He]
  · iframe Hh Hk He; iframe #
  inext
  iintro %keys %vals ⟨Hh, Hk, He, Hout⟩
  iapply HΦ
  iframe Hk He Hout Ho
  iapply BksDraft.rtHeldF_old γ P b rtx rv p $$ Hh

end readers

/-! ## 2. The reader pool (decision 2) -/

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The namespace of a backend's pool of reader slots. -/
def BksDraft.backend.rdPoolN : Namespace := nroot .@ "backend_readers"

/-- **The backend's pool of reader slots** (persistent; decision 2, the Bounds rule): a thread
token borrows one slot (`rdTok`: a slot of `readTx.mu`, of `txMu`, and a reader's budget token)
for one read and gives it back after (`rdTok_borrow`, `rdTok_giveBack`), so a reader holds its
thread token between reads and no pre-split share of the slots. -/
def BksDraft.backend.rdPool (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ γp : GName, threadPool.isThreadPool BksDraft.backend.rdPoolN γp (rdTok (GF := GF) γ P b))

instance BksDraft.backend.rdPool_persistent (γ : BNames) (P : BParams) (b : Loc) :
    Persistent (BksDraft.backend.rdPool (GF := GF) γ P b) := by
  unfold BksDraft.backend.rdPool; infer_instance

/-- A reader slot lent out by the backend's pool, for which the pool holds the borrower's thread
token. -/
def BksDraft.backend.rdLoan (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ γp : GName, threadPool.isThreadPool BksDraft.backend.rdPoolN γp (rdTok (GF := GF) γ P b) ∗
    threadPool.ownThreadLoan γp)

/-- **A pool from `n` reader slots**, enough for every thread but one (`threadBound GF ≤ n + 1`):
what the owner of the slots (the candidate: `New`) builds. -/
theorem BksDraft.backend.rdPool_init (γ : BNames) (P : BParams) (b : Loc) (E : CoPset) (n : Nat)
    (hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), rdTok (GF := GF) γ P b) ⊢
      |={E}=> BksDraft.backend.rdPool γ P b := by
  iintro Hs
  imod threadPool.init BksDraft.backend.rdPoolN (rdTok (GF := GF) γ P b) E n hn $$ Hs with
    ⟨%γp, #Hp⟩
  imodintro
  unfold BksDraft.backend.rdPool
  iexists γp
  iexact Hp

/-- **Borrow a reader slot with a thread token.** -/
theorem BksDraft.backend.rdTok_borrow (γ : BNames) (P : BParams) (b : Loc) (E : CoPset)
    (hE : ↑BksDraft.backend.rdPoolN ⊆ E) :
    BksDraft.backend.rdPool (GF := GF) γ P b ∗ threadTok ⊢
      |={E}=> ▷ rdTok γ P b ∗ BksDraft.backend.rdLoan γ P b := by
  iintro ⟨Hp, Ht⟩
  unfold BksDraft.backend.rdPool
  icases Hp with ⟨%γp, #Hp⟩
  imod threadPool.borrow BksDraft.backend.rdPoolN γp (rdTok (GF := GF) γ P b) E hE $$ [Hp Ht]
    with ⟨Hr, Hl⟩
  · iframe Ht; iframe #
  imodintro
  iframe Hr
  unfold BksDraft.backend.rdLoan
  iexists γp
  iframe Hl; iframe #

/-- **Give a borrowed reader slot back, for the thread token.** -/
theorem BksDraft.backend.rdTok_giveBack (γ : BNames) (P : BParams) (b : Loc) (E : CoPset)
    (hE : ↑BksDraft.backend.rdPoolN ⊆ E) :
    BksDraft.backend.rdLoan (GF := GF) γ P b ∗ rdTok γ P b ⊢ |={E}=> threadTok := by
  iintro ⟨Hl, Hr⟩
  unfold BksDraft.backend.rdLoan
  icases Hl with ⟨%γp, #Hp, Hl⟩
  iapply threadPool.giveBack BksDraft.backend.rdPoolN γp (rdTok (GF := GF) γ P b) E hE
  iframe Hl Hr; iframe #

end pool

section poolLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A reader with a thread token begins a read** (glue, decisions 1 and 2): it borrows a slot from
the backend's pool, `RLock`s with an open share it gets back at once, and holds the live read and
the loan, no open share. -/
theorem BksDraft.reader_RLock (hRL : BksDraft.backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt : Loc) (qo : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ BksDraft.backend.rdPool γ P b ∗
        threadTok ∗ £ 1 ∗ bOpen γ qo }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ∃ (rtx : Loc) (rv : RView), BksDraft.backend.rtHeld γ P b rtx rv ∗
        BksDraft.backend.rdLoan γ P b ∗ bOpen γ qo }} := by
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, #Hp, Ht, Hlc, Ho⟩ HΦ
  imod BksDraft.backend.rdTok_borrow γ P b ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hp $Ht]
    with ⟨Hr, Hl⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc Hr with Hr
  iapply (hRL γ P W Pk b rt qo) $$ %Φ [Hr Ho]
  · iframe Hr Ho; iframe #
  inext
  iintro ⟨%rtx, %rv, Hh, Ho⟩
  iapply HΦ
  iexists rtx, rv
  iframe Hh Hl Ho

/-- **The reader ends its read** (glue): `RUnlock` gives the slot back, the pool the thread token. -/
theorem BksDraft.reader_RUnlock
    (hRU : Perennial.EtcdGrove.backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt rtx : Loc) (rv : RView) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ BksDraft.backend.rtHeld γ P b rtx rv ∗
        BksDraft.backend.rdLoan γ P b }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, Hh, Hl⟩ HΦ
  ihave Hh := BksDraft.rtHeldF_old γ P b rtx rv _ $$ Hh
  rw [← Perennial.EtcdGrove.backend.rtHeld_eq]
  iapply wp_fupd
  iapply (hRU γ P W Pk b rt rtx rv) $$ %(fun v => iprop(|={⊤}=> Φ v)) [Hh]
  · iframe Hh; iframe #
  inext
  iintro Hr
  imod BksDraft.backend.rdTok_giveBack γ P b ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hl $Hr] with Ht
  imodintro
  iapply HΦ
  iexact Ht

/-- **A guard that carries an open share** (glue for the auth realization's release, decision 1):
a fractional token `G` whose share `q` holds the share `f q` of the backend open (the realization's
currency `Cu q` with `bOpen γ (q * authOpenQ)` inside). A reader `RLock`s with it and has it back
at once; a read in progress holds no part of it, so the whole `G 1`, hence the open share `f 1`,
comes back (for `Close`) while reads begun before still run. -/
theorem BksDraft.guarded_RLock (hRL : BksDraft.backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (γ : BNames) (G : Qp → IProp GF) (f : Qp → Qp)
    (hG1 : ∀ q, G q ⊣⊢ bOpen γ (f q) ∗ (bOpen γ (f q) -∗ G q))
    (P : BParams) (W Pk : IProp GF) (b rt : Loc) (q : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ rdTok γ P b ∗ G q }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ∃ (rtx : Loc) (rv : RView), BksDraft.backend.rtHeld γ P b rtx rv ∗ G q }} := by
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, Hr, Hg⟩ HΦ
  icases (hG1 q).1 $$ Hg with ⟨Ho, Hback⟩
  iapply (hRL γ P W Pk b rt (f q)) $$ %Φ [Hr Ho]
  · iframe Hr Ho; iframe #
  inext
  iintro ⟨%rtx, %rv, Hh, Ho⟩
  iapply HΦ
  iexists rtx, rv
  iframe Hh
  iapply Hback $$ Ho

end poolLC

/-! ### Where the pool is built: the candidate (Q2), `New`'s post -/

section newpost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The reader slots the candidate leaves counted (`actualMaxReaders - 2 ^ 29 = 2 ^ 29`), for the
clients that count slots until they move to pools (mvcc's readers, `bkRTx`; `notes/bounds-plan.md`,
B2's mvcc step): the pool takes the other `2 ^ 29`. -/
def BksDraft.backend.rdStockN : Nat := Int.toNat sync.rwmutex.actualMaxReaders - 2 ^ 29

/-- The counted reader slots (the candidate's remainder). -/
def BksDraft.backend.rdStock (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate BksDraft.backend.rdStockN (), rdTok γ P b)

end newpost

/-! ## 3. The tracked buckets by bucket set (decision 3) -/

section tracked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The client's part of the tracked buckets in `S`** (`P.RB`; D22's tracked-bucket token, split
by bucket set): the **writer's contents** hold `r` at the tracked buckets of `S` (each absent if `r`
has it absent), and only the holder writes them (`UnsafePut`, `UnsafeDelete`, `UnsafeCreateBucket`,
`UnsafeDeleteBucket` on a bucket of `S` take its part). A write of the holder's own session to `S`
may be pending: the readers may not see `r` yet (round A1's 30: a raw batch with a pending delete).
What `rbOwn` is today, for any `S`. Opaque in the draft; the representation (the Prove phase's):
`γ.rbk` a ghost map over the tracked buckets' names, the writer's halves, and a second over the
readers' contents, whose client half is with this part (`rbOwnIn`) or deposited in the batch lock by
the session's first write to the bucket, a receipt in its place, redeemed by `Unlock`. -/
opaque BksDraft.backend.rbPart (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    IProp GF := iprop(True)

/-- **The client's idle part of the tracked buckets in `S`**: `rbPart`, and no write to a bucket of
`S` pending, so **the readers see `r` there too** (`BksDraft.backend.rtHeldF_rbOwnIn`) until the
holder writes one. Go makes a part idle at `Unlock` (`batchTxBuffered.Unlock` writes the session's
puts back into the read buffer and commits when a delete is pending: etcd-io/etcd#17119) and at the
backend's creation; a session's write to `S` needs the holder's part, so no one else can make it
pending. Opaque in the draft (see `rbPart`). -/
opaque BksDraft.backend.rbOwnIn (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    IProp GF := iprop(True)

/-- **The client's half of the tracked buckets, redefined** (text and meaning kept: the writer's
contents, a write of the holder's pending or not): the part of every bucket. -/
def BksDraft.backend.rbOwn (γ : BNames) (r : GMap GoString BktData) : IProp GF :=
  BksDraft.backend.rbPart γ (fun _ => True) r

/-- **What a write to bucket `n` needs of the tracked buckets, redefined** (per bucket: the
client's part of `n` only, the writer's contents being `S`; nothing for an untracked bucket). -/
def BksDraft.backend.rbPut (γ : BNames) (P : BParams) (n : GoString) (S : Data) : IProp GF :=
  if P.RB n then BksDraft.backend.rbPart γ (fun m => m = n) (rbData P S) else iprop(True)

/-- Today's `rbPut` (the whole of the tracked buckets), over the redefined `rbOwn`: what today's
callers pass. -/
def BksDraft.backend.rbPutAll (γ : BNames) (P : BParams) (n : GoString) (S : Data) : IProp GF :=
  if P.RB n then BksDraft.backend.rbOwn γ (rbData P S) else iprop(True)

/-! ### The laws (the backend change's obligations; statements) -/

/-- **The parts of disjoint bucket sets are the part of their union.** -/
theorem BksDraft.backend.rbPart_split (γ : BNames) (S S' : GoString → Prop)
    (r : GMap GoString BktData) (hd : ∀ n, S n → S' n → False) :
    BksDraft.backend.rbPart (GF := GF) γ (fun n => S n ∨ S' n) r ⊣⊢
      BksDraft.backend.rbPart γ S r ∗ BksDraft.backend.rbPart γ S' r := by
  sorry

/-- **The idle parts of disjoint bucket sets are the idle part of their union.** -/
theorem BksDraft.backend.rbOwnIn_split (γ : BNames) (S S' : GoString → Prop)
    (r : GMap GoString BktData) (hd : ∀ n, S n → S' n → False) :
    BksDraft.backend.rbOwnIn (GF := GF) γ (fun n => S n ∨ S' n) r ⊣⊢
      BksDraft.backend.rbOwnIn γ S r ∗ BksDraft.backend.rbOwnIn γ S' r := by
  sorry

/-- **Restriction**: a part says nothing of the buckets outside its set. -/
theorem BksDraft.backend.rbPart_congr (γ : BNames) (S : GoString → Prop)
    (r r' : GMap GoString BktData) (h : ∀ n, S n → r.lookup n = r'.lookup n) :
    BksDraft.backend.rbPart (GF := GF) γ S r ⊣⊢ BksDraft.backend.rbPart γ S r' := by
  sorry

/-- **Restriction**, of the idle part. -/
theorem BksDraft.backend.rbOwnIn_congr (γ : BNames) (S : GoString → Prop)
    (r r' : GMap GoString BktData) (h : ∀ n, S n → r.lookup n = r'.lookup n) :
    BksDraft.backend.rbOwnIn (GF := GF) γ S r ⊣⊢ BksDraft.backend.rbOwnIn γ S r' := by
  sorry

/-- **The same set**, extensionally (a law, so that clients need not unfold). -/
theorem BksDraft.backend.rbOwnIn_set (γ : BNames) (S S' : GoString → Prop)
    (r : GMap GoString BktData) (h : ∀ n, S n ↔ S' n) :
    BksDraft.backend.rbOwnIn (GF := GF) γ S r ⊣⊢ BksDraft.backend.rbOwnIn γ S' r := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact .rfl

/-- **The same set**, extensionally, of the part. -/
theorem BksDraft.backend.rbPart_set (γ : BNames) (S S' : GoString → Prop)
    (r : GMap GoString BktData) (h : ∀ n, S n ↔ S' n) :
    BksDraft.backend.rbPart (GF := GF) γ S r ⊣⊢ BksDraft.backend.rbPart γ S' r := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact .rfl

/-- **The idle part is a part** (forgetting that nothing is pending). -/
theorem BksDraft.backend.rbOwnIn_part (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    BksDraft.backend.rbOwnIn (GF := GF) γ S r ⊢ BksDraft.backend.rbPart γ S r := by
  sorry

/-- The part of no bucket is nothing. -/
theorem BksDraft.backend.rbPart_none (γ : BNames) (r : GMap GoString BktData) :
    ⊢ BksDraft.backend.rbPart (GF := GF) γ (fun _ => False) r := by
  sorry

/-- The idle part of no bucket is nothing. -/
theorem BksDraft.backend.rbOwnIn_none (γ : BNames) (r : GMap GoString BktData) :
    ⊢ BksDraft.backend.rbOwnIn (GF := GF) γ (fun _ => False) r := by
  sorry

instance BksDraft.backend.rbPart_timeless (γ : BNames) (S : GoString → Prop)
    (r : GMap GoString BktData) : Timeless (BksDraft.backend.rbPart (GF := GF) γ S r) := by
  sorry

instance BksDraft.backend.rbOwnIn_timeless (γ : BNames) (S : GoString → Prop)
    (r : GMap GoString BktData) : Timeless (BksDraft.backend.rbOwnIn (GF := GF) γ S r) := by
  sorry

/-- **The writer's contents agree with the batch lock's** on the part's tracked buckets (today's
`rbOwn`'s agreement, per part). -/
theorem BksDraft.backend.batchLocked_rbPart (γ : BNames) (P : BParams) (b : Loc) (st : BSess)
    (S : GoString → Prop) (r : GMap GoString BktData) :
    batchLocked (GF := GF) γ P b st ∗ BksDraft.backend.rbPart γ S r ⊢
      batchLocked γ P b st ∗ BksDraft.backend.rbPart γ S r ∗
        ⌜∀ n, S n → P.RB n = true → (rbData P st.S).lookup n = r.lookup n⌝ := by
  sorry

/-- **The readers see the idle part's contents** (what `rbOwnIn` adds to `rbPart`): a held read's
state agrees with it on every key of the part's tracked buckets. While the read is held its state
stays (a write-back and a commit take `readTx.Lock()`). -/
theorem BksDraft.backend.rtHeldF_rbOwnIn (γ : BNames) (P : BParams) (b rtx : Loc) (rv : RView)
    (p : Qp) (S : GoString → Prop) (r : GMap GoString BktData) :
    BksDraft.backend.rtHeldF (GF := GF) γ P b rtx rv p ∗ BksDraft.backend.rbOwnIn γ S r ⊢
      BksDraft.backend.rtHeldF γ P b rtx rv p ∗ BksDraft.backend.rbOwnIn γ S r ∗
        ⌜∀ n k, S n → P.RB n = true → vOf P rv n k = ((r.lookup n).getD ∅).lookup k⌝ := by
  sorry

/-! ### The split the draft auth premise needs (`backend.rbOwn_split_in`, restated) -/

/-- **`rbOwn_split_in`, restated over the idle part** (the draft's statement split `rbOwn`, the
writer's pending contents, into idle parts: false while a write of the holder's is pending, round
A1's 30). The idle part of every bucket is the idle part of `S` and of the rest. -/
theorem BksDraft.backend.rbOwnIn_split_compl (γ : BNames) (S : GoString → Prop)
    (r : GMap GoString BktData) :
    BksDraft.backend.rbOwnIn (GF := GF) γ (fun _ => True) r ⊣⊢
      BksDraft.backend.rbOwnIn γ S r ∗ BksDraft.backend.rbOwnIn γ (fun n => ¬ S n) r := by
  refine (BksDraft.backend.rbOwnIn_set γ _ (fun n => S n ∨ ¬ S n) r ?_).trans ?_
  · intro n; exact ⟨fun _ => Classical.em _, fun _ => trivial⟩
  exact BksDraft.backend.rbOwnIn_split γ S (fun n => ¬ S n) r (fun _ h1 h2 => h2 h1)

/-- The same split of the part (`rbOwn`'s own, for clients that never need idleness). -/
theorem BksDraft.backend.rbOwn_split (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    BksDraft.backend.rbOwn (GF := GF) γ r ⊣⊢
      BksDraft.backend.rbPart γ S r ∗ BksDraft.backend.rbPart γ (fun n => ¬ S n) r := by
  unfold BksDraft.backend.rbOwn
  refine (BksDraft.backend.rbPart_set γ _ (fun n => S n ∨ ¬ S n) r ?_).trans ?_
  · intro n; exact ⟨fun _ => Classical.em _, fun _ => trivial⟩
  exact BksDraft.backend.rbPart_split γ S (fun n => ¬ S n) r (fun _ h1 h2 => h2 h1)

/-- The auth buckets (as the draft auth premise's `authBkts`). -/
def BksDraft.authBkts (n : GoString) : Prop :=
  n = go!"auth" ∨ n = go!"authUsers" ∨ n = go!"authRoles"

/-- The tracked buckets but the auth ones (as the draft's `restNonAuth`). -/
def BksDraft.restNonAuth (n : GoString) : Prop :=
  n ≠ go!"auth" ∧ n ≠ go!"authUsers" ∧ n ≠ go!"authRoles"

/-- **The premise's buckets** (glue for the draft auth premise, `authSchemaSnap`/`authSchemaSrv`,
and the mode-on `srvRestOwn`): a fresh backend's idle tracked buckets (`BksDraft.backend.newPostK`)
are the auth buckets' idle part, for the premise (what its readers see: `authBucketsAt st r`), and
the rest's, for the server (membership, the lessor, the alarms). -/
theorem BksDraft.premise_buckets (γ : BNames) (r : GMap GoString BktData) :
    BksDraft.backend.rbOwnIn (GF := GF) γ (fun _ => True) r ⊢
      BksDraft.backend.rbOwnIn γ BksDraft.authBkts r ∗
        BksDraft.backend.rbOwnIn γ BksDraft.restNonAuth r := by
  iintro H
  icases (BksDraft.backend.rbOwnIn_split_compl γ BksDraft.authBkts r).1 $$ H with ⟨Ha, Hr⟩
  iframe Ha
  iapply (BksDraft.backend.rbOwnIn_set γ _ _ r ?_).1 $$ Hr
  intro n
  unfold BksDraft.authBkts BksDraft.restNonAuth
  constructor
  · intro h; exact ⟨fun e => h (Or.inl e), fun e => h (Or.inr (Or.inl e)),
      fun e => h (Or.inr (Or.inr e))⟩
  · rintro ⟨h1, h2, h3⟩ (e | e | e)
    · exact h1 e
    · exact h2 e
    · exact h3 e

/-- **Today's whole-form write resource is a part of bucket `n` and the rest** (for the callers of
today's statements: `rbPut_of_all`'s two directions). -/
theorem BksDraft.backend.rbPutAll_split (γ : BNames) (P : BParams) (n : GoString) (S : Data) :
    BksDraft.backend.rbPutAll (GF := GF) γ P n S ⊢
      BksDraft.backend.rbPut γ P n S ∗
      (∀ S' : Data, ⌜∀ m, m ≠ n → S'.lookup m = S.lookup m⌝ -∗
        BksDraft.backend.rbPut γ P n S' -∗ BksDraft.backend.rbPutAll γ P n S') := by
  unfold BksDraft.backend.rbPutAll BksDraft.backend.rbPut
  cases hn : P.RB n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro -
    isplitr
    · itrivial
    iintro %S' -
    iintro -
    itrivial
  · simp only [↓reduceIte]
    iintro H
    icases (BksDraft.backend.rbOwn_split γ (fun m => m = n) (rbData P S)).1 $$ H with ⟨Hn, Hr⟩
    iframe Hn
    iintro %S' %hS' Hn'
    unfold BksDraft.backend.rbOwn
    have hset : ∀ m : GoString, True ↔ (m = n ∨ ¬ m = n) :=
      fun m => ⟨fun _ => Classical.em _, fun _ => trivial⟩
    have hcg : ∀ m : GoString, ¬ m = n → (rbData P S).lookup m = (rbData P S').lookup m := by
      intro m hm
      rw [rbData_lookup, rbData_lookup, hS' m hm]
    iapply (BksDraft.backend.rbPart_set γ _ (fun m => m = n ∨ ¬ m = n) _ hset).2
    iapply (BksDraft.backend.rbPart_split γ (fun m => m = n) (fun m => ¬ m = n) _
      (fun _ h1 h2 => h2 h1)).2
    iframe Hn'
    iapply (BksDraft.backend.rbPart_congr γ _ (rbData P S) (rbData P S') hcg).1 $$ Hr

/-! ### The batch transaction's statements, restated -/

/-- **`t.UnsafePut(bucket, key, value)`, restated** (decision 3): today's statement, its
tracked-bucket resource the part of the bucket put into only (`BksDraft.backend.rbPut`). -/
abbrev BksDraft.backend.batchTxBuffered.UnsafePut.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (key value : GoSlice) (kb vb : GoString),
  P.has bi → 0 < kb.length → kb.length ≤ maxKeySize →
  sint.Z st.pend + 1 < 2 ^ 58 →
  (P.SB bi.name = true → ∀ kc vc, (bktOf st.C bi.name).lookup kc = some vc → strLt kc kb) →
  (fkKey bi.name kb → P.FV vb) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*□ kb ∗ value ↦*□ vb ∗
      hkPut γ P bi.name kb st.S ∗ BksDraft.backend.rbPut γ P bi.name st.S ∗ fkPut γ bi.name kb }}
    (App (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafePut")) (Val #bk))
      (Val #key)) (Val #value))
  {{ RET #(); batchLocked γ P b (st.put bi kb vb false) ∗ hkPut γ P bi.name kb (st.put bi kb vb false).S ∗
      BksDraft.backend.rbPut γ P bi.name (st.put bi kb vb false).S ∗ fkPut γ bi.name kb }}

/-- The put changes only its bucket. -/
theorem BksDraft.put_other (st : BSess) (bi : BucketInfo) (kb vb : GoString) (seq : Bool) :
    ∀ m, m ≠ bi.name → (st.put bi kb vb seq).S.lookup m = st.S.lookup m := by
  intro m hm
  show (st.S.insert bi.name _).lookup m = _
  exact GMap.lookup_insert_ne _ _ (Ne.symm hm)

/-- **Today's `UnsafePut` (the whole tracked-bucket token) is a corollary** (spot-check 2: today's
callers, which pass the whole `rbOwn`, go through unchanged). -/
theorem BksDraft.batchTxBuffered.UnsafePut.spec_all
    (h : BksDraft.backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG)) :
    ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface)
      (bi : BucketInfo) (key value : GoSlice) (kb vb : GoString),
    P.has bi → 0 < kb.length → kb.length ≤ maxKeySize →
    sint.Z st.pend + 1 < 2 ^ 58 →
    (P.SB bi.name = true → ∀ kc vc, (bktOf st.C bi.name).lookup kc = some vc → strLt kc kb) →
    (fkKey bi.name kb → P.FV vb) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
        bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗ key ↦*□ kb ∗ value ↦*□ vb ∗
        hkPut γ P bi.name kb st.S ∗ BksDraft.backend.rbPutAll γ P bi.name st.S ∗ fkPut γ bi.name kb }}
      (App (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafePut")) (Val #bk))
        (Val #key)) (Val #value))
    {{ RET #(); batchLocked γ P b (st.put bi kb vb false) ∗
        hkPut γ P bi.name kb (st.put bi kb vb false).S ∗
        BksDraft.backend.rbPutAll γ P bi.name (st.put bi kb vb false).S ∗ fkPut γ bi.name kb }} := by
  intro γ P W Pk b t st bk bi key value kb vb h1 h2 h3 h4 h5 h6
  iintro %Φ ⟨#Hpkg, #Hb, #Ht, Hl, #Hbk, #Hk, #Hv, Hhk, Hrb, Hfk⟩ HΦ
  icases BksDraft.backend.rbPutAll_split γ P bi.name st.S $$ Hrb with ⟨Hrb, Hback⟩
  iapply (h γ P W Pk b t st bk bi key value kb vb h1 h2 h3 h4 h5 h6) $$ %Φ [Hl Hhk Hrb Hfk]
  · iframe Hl Hhk Hrb Hfk; iframe #
  inext
  iintro ⟨Hl, Hhk, Hrb, Hfk⟩
  iapply HΦ
  iframe Hl Hhk Hfk
  iapply Hback $$ %_ %(BksDraft.put_other st bi kb vb false) Hrb

/-- **`t.UnsafeDelete(bucket, key)`, restated** (decision 3): today's statement, its tracked-bucket
resource the part of its bucket only. -/
abbrev BksDraft.backend.batchTxBuffered.UnsafeDelete.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess)
    (bk : GoInterface) (bi : BucketInfo) (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool),
  P.has bi → sint.Z st.pend + 1 < 2 ^ 58 → P.hk bi.name kb = false → ¬ fkKey bi.name kb →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) ∗
      BksDraft.backend.rbPut γ P bi.name st.S }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeDelete")) (Val #bk))
      (Val #key))
  {{ RET #(); batchLocked γ P b (st.del bi kb) ∗
      (if own then key ↦*{dk} kb else txBytes st.tx key kb) ∗
      BksDraft.backend.rbPut γ P bi.name (st.del bi kb).S }}

/-- **`t.Unlock()`, restated** (decision 3): today's statement, and **a part handed in comes back
idle** (`rbPart γ S r` in, `rbOwnIn γ S r` out, for any bucket set `S`: the caller's choice, nothing
for `S` empty). Go: `Unlock` writes the session's puts back into the read buffer under
`readTx.Lock()` and, when a delete is pending, commits (etcd-io/etcd#17119; `pendingDeleteOperations`):
after it the readers see the writer's contents on every tracked bucket (the pre-commit hook writes
none: `hookStep`), and a later write to a bucket of `S` needs the holder's part. -/
abbrev BksDraft.backend.batchTxBuffered.Unlock.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF)
    (S : GoString → Prop) (r : GMap GoString BktData),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗ BksDraft.backend.rbPart γ S r ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q ∗ BksDraft.backend.rbOwnIn γ S r }}

/-- **Today's `Unlock` is a corollary** (the empty bucket set: spot-check 2's other half; every
caller of today's statement goes through unchanged). -/
theorem BksDraft.batchTxBuffered.Unlock.spec_old
    (h : BksDraft.backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG)) :
    Perennial.EtcdGrove.backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st Q h1 h2
  iintro %Φ ⟨#Hpkg, #Hb, #Ht, Hl, Hwb, Hbr⟩ HΦ
  ihave Hn : BksDraft.backend.rbPart (GF := GF) γ (fun _ => False) (∅ : GMap GoString BktData) $$ []
  · iapply BksDraft.backend.rbPart_none
  iapply (h γ P W Pk b t st Q (fun _ => False) ∅ h1 h2) $$ %Φ [Hl Hwb Hbr Hn]
  · iframe Hl Hwb Hbr Hn; iframe #
  inext
  iintro ⟨HQ, -⟩
  iapply HΦ
  iexact HQ

/-- **A session of the idle part's holder keeps it idle** (glue for the draft auth premise's write
contract): an idle part handed to the session (a part of it, `rbOwnIn_part`), written by the session's
puts (each its bucket's part, `rbPut`), comes back idle from `Unlock` at the writer's final
contents. Stated on the resources: the part at the session's end, handed to `Unlock`, gives the idle
part (the triple's frame); here, the part's agreement with the lock that fixes `r`. -/
theorem BksDraft.session_idle (γ : BNames) (P : BParams) (b : Loc) (st : BSess)
    (S : GoString → Prop) (r : GMap GoString BktData) :
    batchLocked (GF := GF) γ P b st ∗ BksDraft.backend.rbOwnIn γ S r ⊢
      batchLocked γ P b st ∗ BksDraft.backend.rbPart γ S r ∗
        ⌜∀ n, S n → P.RB n = true → (rbData P st.S).lookup n = r.lookup n⌝ := by
  iintro ⟨Hl, Hi⟩
  ihave Hp := BksDraft.backend.rbOwnIn_part γ S r $$ Hi
  iapply BksDraft.backend.batchLocked_rbPart γ P b st S r $$ [$Hl $Hp]

end tracked

/-! ### `New`'s post, restated (decisions 2 and 3) -/

section newpost2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **What the constructor gives, restated** (`newPostK`): today's, with the tracked buckets **idle**
(`rbOwnIn γ ⊤ (rbData P D)`: a fresh backend has no session, its readers see bbolt's data), and the
reader slots as **the backend's pool** (`rdPool`, decision 2; the candidate of Q2) and the counted
remainder (`rdStock`) in place of `actualMaxReaders` counted slots. -/
def BksDraft.backend.newPostK (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc)
    (D : Data) : IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ b ∗ K γ ∗
    bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗
    BksDraft.backend.rbOwnIn γ (fun _ => True) (rbData P D) ∗
    BksDraft.backend.rdPool γ P b ∗ BksDraft.backend.rdStock γ P b ∗
    dlInit γ ∗ fkCl γ P D ∗ srSlot b)

/-- **`New(bcfg)`, restated** (the candidate of Q2: the pool built by the constructor, which owns
`readTx.mu`; the thread bound its pool needs as an instance, B1's form). -/
abbrev BksDraft.backend.New.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] (cfg : BackendConfig) (P : BParams) (D : Data) (W Pk K : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      fileHolds cfg.Path' D ∗ ⌜P.Wf ∧ P.limit = cfg.BatchLimit'⌝ ∗
      hooksOk P W Pk cfg.Hooks' ∗
      (∀ γ : BNames, hkOwn γ (hkData P D) ∗ bFresh γ ={⊤}=∗ W γ ∗ Pk γ ∗ K γ) }}
    (App (Val (@! New)) (Val #cfg))
  {{ (r : val), RET r;
      (∃ (b : Loc) (γ : BNames),
        ⌜r = #(interface.mkOk (go.GoType.PointerType backend.ty) #b)⌝ ∗
        BksDraft.backend.newPostK γ P W Pk K b D) ∨
      ⌜∃ p : val, r = PanicV p⌝ }}

end newpost2

end EtcdGrove
end Perennial
