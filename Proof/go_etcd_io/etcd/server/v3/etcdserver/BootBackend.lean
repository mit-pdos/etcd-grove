/-
**The backend `bootstrap` returns, from the backend's constructor** (the integration of the
server construction with branch `construct`'s item 6, 2026-10-17). Lean-first (no Rocq
counterpart).

`bootOk`'s backend part (`InvBoot.lean`) is `backend.New`'s postcondition `backend.newPostK`
(item 6) at the server's batch-lock resources (`W` the store's late registration, `Pk` the apply
protocol's batch lock), plus what `bootstrap` adds: bbolt's data `D` with an empty key bucket
(a new cluster's data directory), the store's registration right, `keySized`, the fresh buckets'
tokens, and (2026-11-03, the whole-`bootOk` review, A) the payment rights `bootstrap`'s own
sessions leave (`bootLeft N`: `N + 7` write-back tokens and the open token, past the `bootWB`
`bootstrap` spends). `bootBackend_of_bootLeft` turns `newPostK … (bootLeft N)` into the resources
`NewServer` uses: the backend, the post-lock hook nil, an open share, the key view, the budget's
`N + 7` write-backs and a read token with an open share per reader slot (`mvcc.bkRTx`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An open share splits in halves. -/
theorem bOpen_halves (γ : backend.BNames) (q : Qp) :
    backend.bOpen (GF := GF) γ q ⊢ backend.bOpen γ q.half ∗ backend.bOpen γ q.half := by
  unfold backend.bOpen
  iintro ⟨Ho, Hc⟩
  have h1 : (DFrac.own q.half : DFrac) = DFrac.own q.half.half • DFrac.own q.half.half := by
    show DFrac.own q.half = DFrac.own (q.half.half + q.half.half)
    rw [Qp.half_add_half]
  have h2 : ghostVar (GF := GF) γ.cls q () = ghostVar γ.cls (q.half + q.half) () := by
    rw [Qp.half_add_half]
  rw [h1, h2]
  icases dghostVar_split (GF := GF) γ.opn false _ _ $$ Ho with ⟨Ho1, Ho2⟩
  icases ghostVar_split (GF := GF) γ.cls () q.half q.half $$ Hc with ⟨Hc1, Hc2⟩
  iframe Ho1 Ho2 Hc1 Hc2

/-- Each reader slot's token with the reader's share of the open token (`mvcc.bkRTx`; D22 receiver
epochs, S8d, W7, 2026-10-25: a fixed share, `backend.rdOpen`). -/
theorem bkRTx_of_rdToks (γ : backend.BNames) (P : backend.BParams) (b : Loc) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), backend.rdTok (GF := GF) γ P b) ∗
      ([∗list] _x ∈ List.replicate n (), backend.bOpen γ backend.rdOpen) ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.bkRTx γ P b
  | 0 => by
    simp only [List.replicate]
    iintro -
    iapply BigSepL.bigSepL_nil.2; itrivial
  | n + 1 => by
    simp only [List.replicate]
    iintro ⟨Hr, Ho⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Ho with ⟨Ho1, Ho⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr1 Ho1]
    · unfold mvcc.bkRTx; iframe Hr1 Ho1
    iapply bkRTx_of_rdToks γ P b n
    iframe Hr Ho

/-- **The write-back tokens `bootstrap` spends before it returns** (2026-11-03, the whole-`bootOk`
review, finding A): one per batch-lock session with pending changes that it runs on the backend it
opened. Each session's `Unlock` writes back once (`batchTxBuffered.Unlock`, `txReadBuffer.writeback`:
`bufVersion` +1), paid by one token. The `run` goroutine's commits are unpaid: they take no token,
leave `bufVersion` alone, and happen only when something is pending (`safePending() != 0`,
`backend.go:474`); whether one runs before `bootstrap` returns is timing (`isMemberBootstrapped`,
`bootstrap.go:384`, waits on peers between the sessions). `bootstrap` runs two sessions:
`CreateMetaBucket`'s (`bootstrap.go:266`, `schema/cindex.go:30-34`) and `Finalize`'s
`MustCreateBackendBuckets` (`:512`, `schema/membership.go:171-178`). `Defrag` (a third,
`bootstrap.go:267-272`) is excluded by `bootCfgOk`. Two are needed; four keep a margin for a session
added upstream. Measured (`etc/spec-test/bootstrap/`): `bufVersion = 2` at return. -/
@[word_unfold] def bootWB : Nat := 4

/-- **What `NewServer` keeps of the backend's payment rights after `bootstrap`'s sessions**
(2026-11-03, the whole-`bootOk` review, A): `N + 7` write-back tokens (`N` for the applied entries,
seven for `NewServer`'s construction) and the clients' whole open token. Not `backend.bFresh`
(every token): the batch lock's bound `bgOk` (`ver + n + k < 2 ^ 40`, `ver` the read buffer's
`bufVersion`) makes holding every token false once a session has written back. -/
def bootLeft (N : Nat) (γ : backend.BNames) : IProp GF :=
  iprop(ownToks γ.wb (N + 7) ∗ backend.bOpen γ 1)

/-- **The backend `NewServer` uses, from what `backend.New` gave as `bootstrap` leaves it** (see the
file header; 2026-11-03, the whole-`bootOk` review, A: from `newPostK … (bootLeft N)`, `N + 7`
write-back tokens and the open token, until then from `newPost`'s every token, false after
`bootstrap`'s own write-backs): bbolt's data with an empty key bucket gives the store's key view
`∅`; (D22, 2026-10-23) the client's half of the tracked buckets, at `D`'s; (the backend-compaction
stage, 2026-10-29) over data with no compaction recorded, the backend's no-compaction token
(`mvcc.bkNoCmp_of_fkCl`); (question 5's core stage, part (1)) the safe-range slot (`srSlot`, kept
for a compacting store: M2's); (M2, the storage side, 2026-10-30; the backend-cmp Probe's S3) the
compaction keys' values tracked (`backend.fkV γ true`, persistent: `mvcc.bkNoCmp_fkV_of_fkCl`), what a
compacting store's `NewStore` takes. (2026-11-02, the backend-auth-split stage) Its reader slots
pooled (as `backend.newPost_pool`, for a thread bound within the pool): the backend's pool of readers
(`bkRPool`, the apply thread's) and a read token per slot of the counted stock (`rdStockN`). -/
theorem bootBackend_of_bootLeft
    [go_etcd_io.etcd.server.v3.storage.backend.Assumptions] (hT : threadBound GF ≤ backend.rdPoolN) (E : CoPset)
    (γ : backend.BNames) (P : backend.BParams)
    (W Pk : backend.BNames → IProp GF) (b : Loc) (D : backend.Data) (N : Nat)
    (hD : mvcc.keyView (backend.vData P (D, ⟨∅, W64 0⟩)) ∅) (hnc : mvcc.noCmpData D) :
    backend.newPostK γ P W Pk (bootLeft N) b D ⊢ |={E}=>
      backend.isBackend γ P (W γ) (Pk γ) b ∗ backend.isStopChans γ b ∗ backend.plHook γ func.nil ∗
      backend.bOpen γ (1 : Qp).half ∗ mvcc.bkView γ 1 (∅ : mvcc.Bucket) ∗
      ownToks γ.wb (N + 7) ∗ backend.rbOwn γ (backend.rbData P D) ∗
      ([∗list] _x ∈ List.replicate backend.rdStockN (),
        mvcc.bkRTx γ P b) ∗
      -- (the backend-compaction stage) the creator's deletable-keys registration, unfixed
      backend.dlInit γ ∗ mvcc.bkNoCmp γ ∗
      -- (M2, the storage side) the compaction keys' values tracked, for a compacting store
      backend.fkV γ true ∗
      -- (question 5's core stage, part (1)) the safe-range slot, for a compacting store (M2's)
      backend.srSlot b ∗
      -- (the backend-auth-split stage) the backend's pool of readers
      backend.bkRPool γ P b := by
  unfold backend.newPostK bootLeft
  iintro ⟨#HnB, #HnSC, ⟨HnWb, Ho⟩, HnV, HnH, HnRB, HnRd, HnDl, HnFk, HnSr⟩
  icases (backend.bOpen_one_pool γ).1 $$ Ho with ⟨Ho, Hop, Hos⟩
  imod backend.rdToks_pool hT E γ P b $$ HnRd with ⟨HnPool, HnRT⟩
  ihave HbkP := backend.bkRPool_intro γ P b $$ [$HnPool $Hop]
  imodintro
  iframe HnB HnSC HnH HnRB HnDl HnSr HbkP HnWb
  ihave ⟨Hnc, Hfv⟩ := mvcc.bkNoCmp_fkV_of_fkCl γ _ hnc $$ HnFk
  iframe Hnc Hfv
  iunfold backend.rdStock at HnRT
  ihave Hrts := bkRTx_of_rdToks γ P b _ $$ [$HnRT $Hos]
  iframe Hrts Ho
  unfold mvcc.bkView
  iexists _
  isplitl [HnV]
  · unfold backend.bView; iexists true; iexact HnV
  ipureintro; exact hD

end boot

end EtcdGrove
end Perennial
