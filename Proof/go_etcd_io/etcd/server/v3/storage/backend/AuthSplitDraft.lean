/-
**The backend's specs for the auth split (Draft; `notes/backend-auth-split-plan.md`).** Imported by
nothing. Statements top-down; the laws of the new opaque predicates are statements (`sorry`), the
glue and the compatibility corollaries are proved over them.

The user's decisions of 2026-11-01 (`notes/snapshot-auth-on-plan.md` on `snap-auth-on-draft`, "The
user's decisions on the restated Draft's questions"), what this module drafts for each:

1. (**Applied**, 2026-11-01: section 1 below.) **A read in progress needs no open share; `Close`
   waits for the readers.** The held read (`rtHeldF`) records that its interval is live, so
   `readTx.UnsafeRange` takes no open share; the guard is at the acquisition (`RLock`).
2. **Readers backed by thread tokens.** The backend's pool of reader slots
   (`BksDraft.backend.rdPool`, a `threadPool` of `rdTok`), from which a thread token borrows a slot
   for one read (`rdTok_borrow`, `rdTok_giveBack`; the glue `BksDraft.reader_RLock`/`reader_RUnlock`),
   for the readers that hold no lock of their owner's; the constructor builds it
   (`BksDraft.backend.newPostK`, under J8a's `ThreadBoundLe GF (2 ^ 28)`) and leaves the rest of
   the slots counted (`rdStock`) for the owners that pool bundles nesting a slot (Q2).
3. (**Applied**, 2026-11-01, option (b): section 3 below.) **Per-bucket idleness**: the client's part
   of the tracked buckets of a set (`rbPart`), its idle part (`rbOwnIn`, a ghost idle token), the
   per-bucket write resource, `Unlock` making a part idle. Here only the draft auth premise's split
   (`BksDraft.premise_buckets`).

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

/-! ## 1. The readers and `Close` (decision 1): applied

Applied (2026-11-01, the Freeze of decision 1): `rtHeldF`/`rtHeld` with the interval live
(`InvBackend.lean`), `readTx.UnsafeRange` with no open share, the share-free laws
(`rtHeldF_lend'`, `rtHeldF_read'`, `ReadLemmas.lean`), `guarded_RLock` (`ClientLaws.lean`). -/

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
theorem BksDraft.reader_RLock (hRL : Perennial.EtcdGrove.backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt : Loc) (qo : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ BksDraft.backend.rdPool γ P b ∗
        threadTok ∗ £ 1 ∗ bOpen γ qo }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ∃ (rtx : Loc) (rv : RView), Perennial.EtcdGrove.backend.rtHeld γ P b rtx rv ∗
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
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ Perennial.EtcdGrove.backend.rtHeld γ P b rtx rv ∗
        BksDraft.backend.rdLoan γ P b }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, Hh, Hl⟩ HΦ
  iapply wp_fupd
  iapply (hRU γ P W Pk b rt rtx rv) $$ %(fun v => iprop(|={⊤}=> Φ v)) [Hh]
  · iframe Hh; iframe #
  inext
  iintro Hr
  imod BksDraft.backend.rdTok_giveBack γ P b ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hl $Hr] with Ht
  imodintro
  iapply HΦ
  iexact Ht

end poolLC

/-! ## 3. The tracked buckets by bucket set (decision 3): applied

Applied (2026-11-01, option (b) of the plan note: `rbOwnIn` a ghost idle token): `rbPart`,
`rbOwnIn`, `rbOwn = rbPart ⊤`, the per-bucket `rbPut` and the whole `rbPutAll`, the batch lock's side
`rbSide` (`InvBackend.lean`); their laws (`TrackedLemmas.lean`); `UnsafePut`, `UnsafeDelete`,
`UnsafeCreateBucket`, `UnsafeDeleteBucket` per bucket; `Unlock` making the part it is handed idle,
and `Unlock.bare` (`UnlockBare.lean`). `rbLock` is not needed: the batch lock's side has `rbOwn`'s
shape, so `backend.Snapshot`'s observation stays as it is. What stays here: the auth premise's split
(its consumer, the auth premise, is the trusted step's). -/

section tracked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The auth buckets (as the draft auth premise's `authBkts`). -/
def BksDraft.authBkts (n : GoString) : Prop :=
  n = go!"auth" ∨ n = go!"authUsers" ∨ n = go!"authRoles"

/-- The tracked buckets but the auth ones (as the draft's `restNonAuth`). -/
def BksDraft.restNonAuth (n : GoString) : Prop :=
  n ≠ go!"auth" ∧ n ≠ go!"authUsers" ∧ n ≠ go!"authRoles"

/-- **The premise's buckets** (glue for the draft auth premise, `authSchemaSnap`/`authSchemaSrv`,
and the mode-on `srvRestOwn`): idle tracked buckets are the auth buckets' idle part, for the premise,
and the rest's, for the server (membership, the lessor, the alarms). -/
theorem BksDraft.premise_buckets (γ : BNames) (r : GMap GoString BktData) :
    rbOwnIn (GF := GF) γ (fun _ => True) r ⊢
      rbOwnIn γ BksDraft.authBkts r ∗ rbOwnIn γ BksDraft.restNonAuth r := by
  iintro H
  icases (rbOwnIn_split_compl γ BksDraft.authBkts r).1 $$ H with ⟨Ha, Hr⟩
  iframe Ha
  iapply (rbOwnIn_set γ _ _ r ?_).1 $$ Hr
  intro n
  unfold BksDraft.authBkts BksDraft.restNonAuth
  constructor
  · intro h; exact ⟨fun e => h (Or.inl e), fun e => h (Or.inr (Or.inl e)),
      fun e => h (Or.inr (Or.inr e))⟩
  · rintro ⟨h1, h2, h3⟩ (e | e | e)
    · exact h1 e
    · exact h2 e
    · exact h3 e

end tracked

/-! ### `New`'s post, restated (decisions 2 and 3) -/

section newpost2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The reader slots the constructor leaves counted (`actualMaxReaders - 2 ^ 28`), for the readers
that nest a slot in a bundle of their owner's (auth's `beMu` over `readTx.mu`, mvcc's store under
`s.mu`: their pools' items, `notes/bounds-locks.md`'s B2), moved to the owner at its constructor. -/
def BksDraft.backend.rdStockN : Nat := Int.toNat sync.rwmutex.actualMaxReaders - 2 ^ 28

/-- The counted reader slots. -/
def BksDraft.backend.rdStock (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate BksDraft.backend.rdStockN (), rdTok γ P b)

/-- **What the constructor gives, restated** (`newPostK`): today's, with the tracked buckets **idle**
(`rbOwnIn γ ⊤ (rbData P D)`: a fresh backend has no session, its readers see bbolt's data), and the
reader slots as **the backend's pool** (`rdPool`, decision 2: for the readers that hold no lock of
their owner's across a read transaction, all on the apply thread: `MustReadMembersFromBackend`, the
alarm store's `GetAllAlarms`, `authStore.Recover`, `UserGet`/`UserList`/`RoleGet`/`Authenticate`:
rounds 3-4) and the counted remainder (`rdStock`) for the owners that pool bundles. Q2. -/
def BksDraft.backend.newPostK (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc)
    (D : Data) : IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ b ∗ K γ ∗
    bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗
    rbOwnIn γ (fun _ => True) (rbData P D) ∗
    BksDraft.backend.rdPool γ P b ∗ BksDraft.backend.rdStock γ P b ∗
    dlInit γ ∗ fkCl γ P D ∗ srSlot b)

/-- **`New(bcfg)`, restated** (the pool built by the constructor, which owns `readTx.mu`; the
thread bound it needs as an instance, B1's form, at J8a's `2 ^ 28`). -/
abbrev BksDraft.backend.New.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] (cfg : BackendConfig) (P : BParams) (D : Data) (W Pk K : BNames → IProp GF),
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
