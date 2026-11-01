/-
What the backend's constructor (`New`, `newBackend`) takes and gives. Lean-first (no Rocq
counterpart); 2026-10-17, branch `construct`.

- `hooksOk P W Pk h`: the hooks' contract of the configuration's hooks `h`, for every backend
  made with the parameters `P` and the batch lock's resources `W γ`, `Pk γ` (functions of the
  backend's ghost names: the server's hooks' resource names the backend's `hkOwn`), given the
  backend later (`▷ isBackend`, as `isBackend_of_hooks` takes it). A nil `h` meets it
  (`hooksOk_nil`).
- `newPost γ P W Pk b D`: what the constructor gives: the backend (`isBackend`), its stop
  channels (`isStopChans`, for `Close`), the clients' whole open token, the clients' half of the
  readers' view (of bbolt's data `D`, no buffered writes), the post-lock hook's clients' half
  (nil), the write-back tokens (`wbInit`: all the model provides), (D22, 2026-10-23) the client's
  half of the tracked buckets (`rbOwn`, at `D`'s) and a reader's token for each of `readTx.mu`'s
  reader slots.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- The write-back tokens a new backend provides: the batch lock's budget bounds the read
buffer's version plus the tokens out below `2 ^ 40` (`bgOk`; the version starts at 0). -/
def wbInit : Nat := 2 ^ 40 - 1

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The hooks' contract of `h` for every backend made with `P`, `W`, `Pk`, given the backend
later (persistent). -/
def hooksOk (P : BParams) (W Pk : BNames → IProp GF) (h : GoInterface) : IProp GF :=
  iprop(□ ∀ (γ : BNames) (b t : Loc), ▷ isBackend γ P (W γ) (Pk γ) b -∗
    bF go!"batchTx" b ↦□ t -∗ hooksSpec γ P (Pk γ) b t h)

instance hooksOk_persistent (P : BParams) (W Pk : BNames → IProp GF) (h : GoInterface) :
    Persistent (hooksOk P W Pk h) := by
  unfold hooksOk; infer_instance

/-- **What the constructor gives** for the backend `b` over bbolt's data `D`, its ghost names
`γ` (the clients' whole view with the read buffer known clean, `bViewC … true`: the restore
plan's R5a). -/
def newPost (γ : BNames) (P : BParams) (W Pk : BNames → IProp GF) (b : Loc) (D : Data) :
    IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ b ∗ bOpen γ 1 ∗
    bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗ ownToks γ.wb wbInit ∗
    rbOwn γ (rbData P D) ∗ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), rdTok γ P b) ∗
    -- (the backend-compaction stage, Draft round 2) the creator's part of the deletable keys
    dlInit γ ∗
    -- (the compaction keys' tracked absence, 2026-10-29; question 4) the client's half of their
    -- flag and the bit of their values
    fkCl γ P D ∗
    -- (question 5's wiring, Q5-2, 2026-10-29) the safe-range slot (one reader's slot of
    -- `safeRangeDeleteMu`, from its zero value): what the compaction job's
    -- `LockForSafeRangeDelete` takes
    srSlot b)

end preds

section fresh
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A fresh backend's payment rights** (D22 receiver epochs, S8a, 2026-10-24): every write-back
token and the clients' whole open token, which the constructor gives (`newPost`). Whoever holds
them knows no commit can run the backend's hooks (`hook_fresh_false`): every commit is paid by one
of them (`payIn`). -/
def bFresh (γ : BNames) : IProp GF := iprop(ownToks γ.wb wbInit ∗ bOpen γ 1)

/-- **No hook runs on a fresh backend** (D22 receiver epochs, S8a, 2026-10-24): a commit's payment
(`payIn`) under the batch lock refutes the fresh backend's payment rights. A write-back token is
one too many (`bgOk`: the read buffer's version, the tokens out and the paid commits stay below
`2 ^ 40 = wbInit + 1`); a write-back since the backend was made (the `run` goroutine's commit,
`Unlock`'s) raised the version past 0 (`w ≤ ver`); a stop holds the clients' half of the open
token. -/
theorem hook_fresh_false (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (stop : Bool)
    (m u : Nat) :
    batchLocked (GF := GF) γ P b st ∗ payIn γ st stop m u ∗ ownToks γ.wb wbInit ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half) false ⊢ False := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨Hl, Hpay, Htoks, Hop⟩
  icases Hl with ⟨%t, %db, -, -, -, ⟨-, %n, %w, %u0, -, Ha, Hmo, -, -, -, -, %Hbg⟩, -⟩
  icombine Ha Htoks gives %Hle
  have h1 := Hbg.1
  have hwv := Hbg.2.2.2.2.2.2.2.2.2
  have hv0 : 0 ≤ uint.Z st.R.ver := by word
  have hwi : wbInit = 2 ^ 40 - 1 := rfl
  iunfold payIn at Hpay
  cases stop
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hm0 : m = 0
    · rw [if_pos hm0]
      iunfold wbTok at Hpay
      icombine Htoks Hpay as Ht
      icombine Ha Ht gives %Hle2
      exfalso
      omega
    by_cases hm1 : m = 1
    · rw [if_neg hm0, if_pos hm1]
      icases Hpay with ⟨-, #Hlb⟩
      ihave %Hlw := monoNatLbOwn_valid γ.wbc 1 w (u + 1) $$ Hmo Hlb
      exfalso
      omega
    · rw [if_neg hm0, if_neg hm1]
      icases Hpay with ⟨-, #Hlb⟩
      ihave %Hlw := monoNatLbOwn_valid γ.wbc 1 w 1 $$ Hmo Hlb
      exfalso
      omega
  · simp only [↓reduceIte]
    icases Hpay with ⟨Hp1, Hp2⟩
    icombine Hp1 Hop as Hf
    icombine Hf Hp2 gives %Hv2
    exfalso
    have := DFrac.valid_own_op Hv2.1
    exact absurd this (by simp)

/-- `hook_fresh_false` with the payment rights of any backend with the same write-back and open
names. -/
theorem hook_bFresh_false (γ γ' : BNames) (P : BParams) (b : Loc) (st : BSess) (stop : Bool)
    (m u : Nat) (hwb : γ'.wb = γ.wb) (hopn : γ'.opn = γ.opn) :
    batchLocked (GF := GF) γ P b st ∗ payIn γ st stop m u ∗ bFresh γ' ⊢ False := by
  unfold bFresh bOpen
  iintro ⟨Hl, Hpay, Htoks, Hop, -⟩
  ihave Htoks : ownToks γ.wb wbInit $$ [Htoks]
  · rw [← hwb]; iexact Htoks
  ihave Hop : dghostVar γ.opn (DFrac.own (1 : Qp).half) false $$ [Hop]
  · rw [← hopn]; iexact Hop
  iapply hook_fresh_false γ P b st stop m u $$ [$Hl $Hpay $Htoks $Hop]

end fresh

section preds2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **What the constructor gives, the fresh backend's payment rights traded** (D22 receiver epochs,
S8a, 2026-10-24): `newPost` with the creator's batch-lock step having taken `bFresh γ` (every
write-back token and the clients' whole open token) and given `K γ` in its place. A creator that
keeps them takes `K := bFresh` (`newPost_of_K`); `applySnapshot` deposits them with the apply
protocol until the new backend becomes current, so that no hook can run on it before
(`hook_fresh_false`). -/
def newPostK (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc) (D : Data) :
    IProp GF :=
  iprop(isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ b ∗ K γ ∗
    bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗
    rbOwn γ (rbData P D) ∗ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), rdTok γ P b) ∗
    dlInit γ ∗ fkCl γ P D ∗ srSlot b)

/-- The constructor's post with the payment rights kept is `newPost`. -/
theorem newPost_of_K (γ : BNames) (P : BParams) (W Pk : BNames → IProp GF) (b : Loc) (D : Data) :
    newPostK (GF := GF) γ P W Pk bFresh b D ⊢ newPost γ P W Pk b D := by
  unfold newPostK bFresh
  iintro ⟨Hb, Hs, ⟨Ht, Ho⟩, Hv, Hh, Hr, Hrd, Hdl, Hfk, Hsr⟩
  unfold newPost
  iframe Hb Hs Ho Hv Hh Ht Hr Hrd Hdl Hfk Hsr

end preds2

end backend
end EtcdGrove
end Perennial
