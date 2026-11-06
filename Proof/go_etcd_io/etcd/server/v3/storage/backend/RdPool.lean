/-
**The backend's pool of reader slots** (the backend-auth-split stage, 2026-11-02; moved from the
stage's Draft, `AuthSplitDraft.lean`, decision 2: readers backed by thread tokens).

- `rdPool γ P b` (persistent): a `threadPool` of the backend's reader slots (`rdTok`), from which a
  thread token borrows one slot for one read (`rdTok_borrow`, `rdTok_giveBack`; the glue
  `reader_RLock`/`reader_RUnlock`), for the readers that hold no lock of their owner's.
- `bkRPool γ P b`: a pooled reader's resource, the pool and its `rdPoolN` slots' open shares
  (`rdOpen` each), not persistent.
- `rdAuth γ P b`: the auth store's share, `authRdN` slots (the auth-on snapshot plan's N4,
  2026-11-03: the store's reader resource a ticket, backed by these slots of each backend); their
  open shares travel with the pool's (`bkRPool`).
- `rdStock γ P b`: the `rdStockN` slots the constructor's post leaves counted past the pool and the
  auth share.
- `newPost_pool`/`newPostK_pool`: the constructor's post with its slots split into the pool and
  the stock (`newPostP`, `newPostKP`), for a thread bound within the pool.

What the partition counts (2026-11-06, `notes/axiom-review/authrdn-count.md`, attack 6): the
`actualMaxReaders` slots are the `readTx.mu` read locks taken with an `rdTok` (every one the verified
backend code takes, and those of the auth store's tickets), not every Go reader of `readTx.mu`.
`EtcdServer.monitorStorageVersion`'s goroutine read-locks it (`StorageVersion` →
`schema.DetectSchemaVersion`, `schema.go:85-88`) without one: its spec (`srvSVRes`) holds no
`rdTok`, so Go's `readTx.mu` can have one reader more than the slots count. Go's limit
(`2 ^ 30 - 1` readers) is still not reached: each reader is a live goroutine, at most the thread
bound (`≤ 2 ^ 28` in every closed theorem through `NewServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Perennial.Proof.ThreadPool
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- The size of the backend's reader pool: the thread bound the server fixes (`NewServer`'s
`threadBound GF ≤ 2 ^ 28`, J8a-6). -/
@[word_unfold] def rdPoolN : Nat := 2 ^ 28

/-- **The auth store's share of a backend's reader slots** (the auth-on snapshot plan's N4,
2026-11-03): the auth store's reader resource is a ticket, of which the server hands out at most
`authRdN` copies, each backed by one of these slots of the backend current when it is redeemed.
(revoke-open Q6 (a), 2026-11-06: `2 ^ 28` more, until then `2 ^ 7`, for the revocation's inner pool's
copies of the server's `E.RD`.) -/
@[word_unfold] def authRdN : Nat := 2 ^ 28 + 2 ^ 7

/-- The reader slots the constructor's post leaves counted, past the pool's `rdPoolN` and the auth
share's `authRdN`. (Irreducible, 2026-11-02: a unifier unfolding it would evaluate `Nat.sub` by
`2 ^ 28` steps; its value is `rdStockN_val`.) -/
@[irreducible] def rdStockN : Nat := Int.toNat sync.rwmutex.actualMaxReaders - rdPoolN - authRdN

/-- The pool, the auth share and the stock are the constructor's `actualMaxReaders` slots
(2026-11-02, the backend-auth-split stage; the auth share 2026-11-03): every `rdTok`, so every
`readTx.mu` reader that holds one; not `monitorStorageVersion`'s, which holds none (the file
header). -/
theorem rdPoolN_add_rdStockN :
    rdPoolN + authRdN + rdStockN = Int.toNat sync.rwmutex.actualMaxReaders := by
  unfold rdStockN rdPoolN authRdN
  rw [sync.rwmutex.actualMaxReaders_unseal]
  decide

/-- The stock's size (2026-11-02, the backend-auth-split stage; less the auth share 2026-11-03):
`2 ^ 30 - 1 - 2 ^ 28 - (2 ^ 28 + 2 ^ 7)` (revoke-open, 2026-11-06; until then `805306239`), for the
consumers' arithmetic. -/
theorem rdStockN_val : rdStockN = 536870783 := by
  unfold rdStockN rdPoolN authRdN
  rw [sync.rwmutex.actualMaxReaders_unseal]
  decide

/-- The stock is at most the constructor's slots. -/
theorem rdStockN_le : rdStockN ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
  have := rdPoolN_add_rdStockN; omega

/-- The namespace of a backend's pool of reader slots. -/
def rdPoolNs : Namespace := nroot .@ "backend_readers"

/-- `n + m` copies of `R` are `n` copies and `m` copies. -/
theorem bigSepL_replicate_add {GF : BundledGFunctors} (R : IProp GF) (n m : Nat) :
    ([∗list] _x ∈ List.replicate (n + m) (), R) ⊣⊢
      ([∗list] _x ∈ List.replicate n (), R) ∗ [∗list] _x ∈ List.replicate m (), R := by
  rw [← List.replicate_append_replicate]
  exact BigSepL.bigSepL_append

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The backend's pool of reader slots** (persistent; decision 2, the Bounds rule): a thread
token borrows one slot (`rdTok`: a slot of `readTx.mu`, of `txMu`, and a reader's budget token)
for one read and gives it back after (`rdTok_borrow`, `rdTok_giveBack`), so a reader holds its
thread token between reads and no pre-split share of the slots. -/
def rdPool (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ γp : GName, threadPool.isThreadPool rdPoolNs γp (rdTok (GF := GF) γ P b))

instance rdPool_persistent (γ : BNames) (P : BParams) (b : Loc) :
    Persistent (rdPool (GF := GF) γ P b) := by
  unfold rdPool; infer_instance

/-- A reader slot lent out by the backend's pool, for which the pool holds the borrower's thread
token. -/
def rdLoan (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(∃ γp : GName, threadPool.isThreadPool rdPoolNs γp (rdTok (GF := GF) γ P b) ∗
    threadPool.ownThreadLoan γp)

/-- The auth store's share of the reader slots (N4, 2026-11-03). -/
def rdAuth (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate authRdN (), rdTok γ P b)

/-- The counted reader slots. -/
def rdStock (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate rdStockN (), rdTok γ P b)

/-- **A pooled reader's resource** (the backend-auth-split stage, Q2 (a)): the backend's pool of
`rdPoolN` reader slots (`backend.rdPool`), from which the reader's thread token borrows one slot per
read (`rdTok_borrow`/`rdTok_giveBack`), and the pool's and the auth share's slots' shares of the
backend open (`rdOpen` each, taken from the constructor's replicated ones, so the shares reassemble
for `Close`; the auth share's slots, which the auth store keeps for good, carry none of their own:
2026-11-03, review R4's F3). Not
persistent (the open shares): the apply thread holds the one copy; on the snapshot path the old
backend's goes to the goroutine closing it (`server.go:1146`). -/
def bkRPool (γ : BNames) (P : BParams) (b : Loc) : IProp GF :=
  iprop(rdPool γ P b ∗ [∗list] _x ∈ List.replicate (rdPoolN + authRdN) (), bOpen γ rdOpen)

/-- **A pool from `n` reader slots**, enough for every thread but one (`threadBound GF ≤ n + 1`):
what the owner of the slots (the constructor's post, `newPost_pool`) builds. -/
theorem rdPool_init (γ : BNames) (P : BParams) (b : Loc) (E : CoPset) (n : Nat)
    (hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), rdTok (GF := GF) γ P b) ⊢ |={E}=> rdPool γ P b := by
  iintro Hs
  imod threadPool.init rdPoolNs (rdTok (GF := GF) γ P b) E n hn $$ Hs with ⟨%γp, #Hp⟩
  imodintro
  unfold rdPool
  iexists γp
  iexact Hp

/-- **Borrow a reader slot with a thread token.** -/
theorem rdTok_borrow (γ : BNames) (P : BParams) (b : Loc) (E : CoPset)
    (hE : ↑rdPoolNs ⊆ E) :
    rdPool (GF := GF) γ P b ∗ threadTok ⊢ |={E}=> ▷ rdTok γ P b ∗ rdLoan γ P b := by
  iintro ⟨Hp, Ht⟩
  unfold rdPool
  icases Hp with ⟨%γp, #Hp⟩
  imod threadPool.borrow rdPoolNs γp (rdTok (GF := GF) γ P b) E hE $$ [Hp Ht] with ⟨Hr, Hl⟩
  · iframe Ht; iframe #
  imodintro
  iframe Hr
  unfold rdLoan
  iexists γp
  iframe Hl; iframe #

/-- **Give a borrowed reader slot back, for the thread token.** -/
theorem rdTok_giveBack (γ : BNames) (P : BParams) (b : Loc) (E : CoPset)
    (hE : ↑rdPoolNs ⊆ E) :
    rdLoan (GF := GF) γ P b ∗ rdTok γ P b ⊢ |={E}=> threadTok := by
  iintro ⟨Hl, Hr⟩
  unfold rdLoan
  icases Hl with ⟨%γp, #Hp, Hl⟩
  iapply threadPool.giveBack rdPoolNs γp (rdTok (GF := GF) γ P b) E hE
  iframe Hl Hr; iframe #

/-- **The whole open token is the constructors' half, the pool's shares and the stock's**
(2026-11-02, the backend-auth-split stage): `bOpen_one_shares` with the readers' shares split at
`rdPoolN + authRdN` (the pool's with the auth share's, 2026-11-03). -/
theorem bOpen_one_pool (γ : BNames) :
    bOpen (GF := GF) γ 1 ⊣⊢ bOpen γ (1 : Qp).half ∗
      ([∗list] _x ∈ List.replicate (rdPoolN + authRdN) (), bOpen γ rdOpen) ∗
      [∗list] _x ∈ List.replicate rdStockN (), bOpen γ rdOpen := by
  refine (bOpen_one_shares (GF := GF) (hG := hG) γ).trans ?_
  rewrite [← rdPoolN_add_rdStockN]
  exact sep_congr .rfl (bigSepL_replicate_add _ (rdPoolN + authRdN) rdStockN)

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
theorem reader_RLock (hRL : Perennial.EtcdGrove.backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt : Loc) (qo : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ rdPool γ P b ∗
        threadTok ∗ £ 1 ∗ bOpen γ qo }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ∃ (rtx : Loc) (rv : RView), rtHeld γ P b rtx rv ∗ rdLoan γ P b ∗ bOpen γ qo }} := by
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, #Hp, Ht, Hlc, Ho⟩ HΦ
  imod rdTok_borrow γ P b ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hp $Ht] with ⟨Hr, Hl⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc Hr with Hr
  iapply (hRL γ P W Pk b rt qo) $$ %Φ [Hr Ho]
  · iframe Hr Ho; iframe #
  inext
  iintro ⟨%rtx, %rv, Hh, Ho⟩
  iapply HΦ
  iexists rtx, rv
  iframe Hh Hl Ho

/-- **The reader ends its read** (glue): `RUnlock` gives the slot back, the pool the thread token. -/
theorem reader_RUnlock
    (hRU : Perennial.EtcdGrove.backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt rtx : Loc) (rv : RView) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ rtHeld γ P b rtx rv ∗ rdLoan γ P b }}
      (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hpkg, #Hb, #Hrt, Hh, Hl⟩ HΦ
  iapply wp_fupd
  iapply (hRU γ P W Pk b rt rtx rv) $$ %(fun v => iprop(|={⊤}=> Φ v)) [Hh]
  · iframe Hh; iframe #
  inext
  iintro Hr
  imod rdTok_giveBack γ P b ⊤ (fun _ _ => CoPset.mem_full) $$ [$Hl $Hr] with Ht
  imodintro
  iapply HΦ
  iexact Ht

/-- **The constructor's post with its reader slots pooled** (2026-11-02, the backend-auth-split
stage): `newPost` with the `actualMaxReaders` slots as the pool (`bkRPool`, with its slots' open
shares) and the counted stock (`rdStock`), and the whole open token `bOpen γ 1` less the pool's
shares: the constructors' half and the stock's shares. -/
def newPostP (γ : BNames) (P : BParams) (W Pk : BNames → IProp GF) (b : Loc) (D : Data) :
    IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ P (W γ) (Pk γ) b ∗ bOpen γ (1 : Qp).half ∗
    ([∗list] _x ∈ List.replicate rdStockN (), bOpen γ rdOpen) ∗
    bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗ ownToks γ.wb wbInit ∗
    rbOwn γ (rbData P D) ∗ bkRPool γ P b ∗ rdAuth γ P b ∗ rdStock γ P b ∗
    dlInit γ ∗ fkCl γ P D ∗ srSlot b)

/-- **`newPostK` with its reader slots pooled** (2026-11-02, the backend-auth-split stage): the
slots as the pool (`rdPool`) and the counted stock (`rdStock`). The pool's open shares are not
here: `newPostK` holds no open token (its `K γ` took `bFresh γ`); whoever gets `bOpen γ 1` back
splits them off (`bOpen_one_pool`) and builds `bkRPool` (`bkRPool_intro`). -/
def newPostKP (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc) (D : Data) :
    IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ P (W γ) (Pk γ) b ∗ K γ ∗
    bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗
    rbOwn γ (rbData P D) ∗ rdPool γ P b ∗ rdAuth γ P b ∗ rdStock γ P b ∗
    dlInit γ ∗ fkCl γ P D ∗ srSlot b)

/-- **`newPostKP`, by name** (2026-11-02, the backend-auth-split stage; as `newPostK_named`):
`HnPool` the pool, `HnRT` the counted stock's slots, the others `newPostK_named`'s. -/
theorem newPostKP_named (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc)
    (D : Data) :
    newPostKP γ P W Pk K b D ⊢
      iprop("#HnB" ∷ isBackend γ P (W γ) (Pk γ) b ∗ "#HnSC" ∷ isStopChans γ P (W γ) (Pk γ) b ∗ "HnK" ∷ K γ ∗
        "HnV" ∷ bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ "HnH" ∷ plHook γ func.nil ∗
        "HnRB" ∷ rbOwn γ (rbData P D) ∗ "#HnPool" ∷ rdPool γ P b ∗ "HnRA" ∷ rdAuth γ P b ∗
        "HnRT" ∷ ([∗list] _x ∈ List.replicate rdStockN (), rdTok γ P b) ∗
        "HnDl" ∷ dlInit γ ∗ "HnFk" ∷ fkCl γ P D ∗ "HnSr" ∷ srSlot b) := by
  unfold newPostKP rdStock; exact .rfl

/-- A pooled reader's resource from the pool and its slots' open shares. -/
theorem bkRPool_intro (γ : BNames) (P : BParams) (b : Loc) :
    rdPool (GF := GF) γ P b ∗ ([∗list] _x ∈ List.replicate (rdPoolN + authRdN) (), bOpen γ rdOpen) ⊢
      bkRPool γ P b := by
  iintro ⟨Hp, Hs⟩
  unfold bkRPool
  iframe

/-- The constructor's slots into the pool, the auth share and the stock. -/
theorem rdToks_pool (hT : threadBound GF ≤ rdPoolN) (E : CoPset) (γ : BNames) (P : BParams)
    (b : Loc) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), rdTok (GF := GF) γ P b)
      ⊢ |={E}=> rdPool γ P b ∗ rdAuth γ P b ∗ rdStock γ P b := by
  rewrite [← rdPoolN_add_rdStockN]
  iintro Hs
  icases (bigSepL_replicate_add _ (rdPoolN + authRdN) rdStockN).1 $$ Hs with ⟨Hp, Hs⟩
  icases (bigSepL_replicate_add _ rdPoolN authRdN).1 $$ Hp with ⟨Hp, Ha⟩
  imod rdPool_init γ P b E rdPoolN (by omega) $$ Hp with Hp
  imodintro
  unfold rdAuth rdStock
  iframe

/-- **The constructor's post, its reader slots split into the backend's pool and a counted stock**
(Q2 (a)): `rdPoolN` of the `actualMaxReaders` replicated slots (`rdTok`) and as many of their open
shares (`rdOpen`, split off the post's `bOpen γ 1`) become the pool (`bkRPool`), the other
`rdStockN` slots stay as today's consumers take them, for a thread bound within the pool. -/
theorem newPost_pool (hT : threadBound GF ≤ rdPoolN) (E : CoPset)
    (γ : BNames) (P : BParams) (W Pk : BNames → IProp GF) (b : Loc) (D : Data) :
    newPost γ P W Pk b D ⊢ |={E}=> newPostP γ P W Pk b D := by
  unfold newPost newPostP
  iintro ⟨Hb, Hs, Ho, Hv, Hh, Ht, Hr, Hrd, Hdl, Hfk, Hsr⟩
  icases (bOpen_one_pool γ).1 $$ Ho with ⟨Hoh, Hop, Hos⟩
  imod rdToks_pool hT E γ P b $$ Hrd with ⟨Hp, Ha, Hst⟩
  ihave Hk := bkRPool_intro γ P b $$ [$Hp $Hop]
  imodintro
  iframe

/-- **`newPostK`, its reader slots split into the backend's pool and a counted stock** (as
`newPost_pool`; the pool's open shares come with the open token, `newPostKP`). -/
theorem newPostK_pool (hT : threadBound GF ≤ rdPoolN) (E : CoPset)
    (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc) (D : Data) :
    newPostK γ P W Pk K b D ⊢ |={E}=> newPostKP γ P W Pk K b D := by
  unfold newPostK newPostKP
  iintro ⟨Hb, Hs, Hk, Hv, Hh, Hr, Hrd, Hdl, Hfk, Hsr⟩
  imod rdToks_pool hT E γ P b $$ Hrd with ⟨Hp, Ha, Hst⟩
  imodintro
  iframe

end poolLC

end backend
end EtcdGrove
end Perennial
