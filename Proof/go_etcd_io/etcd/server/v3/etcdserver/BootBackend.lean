/-
**The backend `bootstrap` returns, from the backend's constructor** (the integration of the
server construction with branch `construct`'s item 6, 2026-10-17). Lean-first (no Rocq
counterpart).

`bootOk`'s backend part (`InvBoot.lean`) is `backend.New`'s postcondition `backend.newPost`
(item 6) at the server's batch-lock resources (`W` the store's late registration, `Pk` the apply
protocol's batch lock), plus what `bootstrap` adds: bbolt's data `D` with an empty key bucket
(a new cluster's data directory), the store's registration right, `keySized`, the fresh buckets'
tokens, and the budget `N + 7 ≤ wbInit`. `bootBackend_of_newPost` turns `newPost` into the
resources `NewServer` uses: the backend, the post-lock hook nil, an open share, the key view, the
budget's `N + 7` write-backs and a read token with an open share per reader slot (`mvcc.bkRTx`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
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

/-- **The backend `NewServer` uses, from `backend.New`'s postcondition** (see the file header):
bbolt's data with an empty key bucket gives the store's key view `∅`, and `N + 7` of the
`wbInit` write-backs; (D22, 2026-10-23) the client's half of the tracked buckets, at `D`'s;
(the backend-compaction stage, 2026-10-29) over data with no compaction recorded, the backend's
no-compaction token (`mvcc.bkNoCmp_of_fkCl`: until then a separate premise of `bootOk`); (question 5's
core stage, part (1)) the safe-range slot (`srSlot`, kept for a compacting store: M2's). -/
theorem bootBackend_of_newPost (γ : backend.BNames) (P : backend.BParams)
    (W Pk : backend.BNames → IProp GF) (b : Loc) (D : backend.Data) (N : Nat)
    (hD : mvcc.keyView (backend.vData P (D, ⟨∅, W64 0⟩)) ∅) (hN : N + 7 ≤ backend.wbInit)
    (hnc : mvcc.noCmpData D) :
    backend.newPost γ P W Pk b D ⊢
      backend.isBackend γ P (W γ) (Pk γ) b ∗ backend.isStopChans γ b ∗ backend.plHook γ func.nil ∗
      backend.bOpen γ (1 : Qp).half ∗ mvcc.bkView γ 1 (∅ : mvcc.Bucket) ∗
      ownToks γ.wb (N + 7) ∗ backend.rbOwn γ (backend.rbData P D) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.bkRTx γ P b) ∗
      -- (the backend-compaction stage) the creator's deletable-keys registration, unfixed
      backend.dlInit γ ∗ mvcc.bkNoCmp γ ∗
      -- (question 5's core stage, part (1)) the safe-range slot, for a compacting store (M2's)
      backend.srSlot b := by
  iintro Hnew
  ihave Hnew := backend.newPost_named γ P W Pk b D $$ Hnew
  iNamed Hnew
  iframe HnB HnSC HnH HnRB HnDl HnSr
  ihave Hnc := mvcc.bkNoCmp_of_fkCl γ _ hnc $$ HnFk
  iframe Hnc
  icases (backend.bOpen_one_shares γ).1 $$ HnOpen with ⟨Ho, Hos⟩
  ihave Hrts := bkRTx_of_rdToks γ P b _ $$ [$HnRT $Hos]
  iframe Hrts Ho
  isplitl [HnV]
  · unfold mvcc.bkView
    iexists _
    isplitl [HnV]
    · unfold backend.bView; iexists true; iexact HnV
    ipureintro; exact hD
  obtain ⟨k, hk⟩ : ∃ k, backend.wbInit = k + (N + 7) :=
    ⟨backend.wbInit - (N + 7), (Nat.sub_add_cancel hN).symm⟩
  rw [hk]
  icases (ownToks_add (N + 7) k γ.wb).1 $$ HnWb with ⟨-, Hw⟩
  iexact Hw

end boot

end EtcdGrove
end Perennial
