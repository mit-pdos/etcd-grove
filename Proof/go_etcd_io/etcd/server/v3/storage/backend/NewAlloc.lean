/-
The backend's invariants allocated by its constructor (`backend_init`), once `newBatchTxBuffered`
has begun bbolt's two transactions: the ghost names, the batch lock's resource in its first
state (`st0`: committed and written data `D`, empty buffers), `readTx.mu`'s resource in its first
state (`rv0`, the first interval's read transaction, its `WaitGroup`), `txMu`, the cache, the
stop protocol, and the clients' and the `run` goroutine's shares. Lean-first (no Rocq
counterpart); 2026-10-17, branch `construct`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.NewLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.HooksLoeb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-! ## The first states -/

/-- The read buffer of a new backend. -/
def rb0 : RBuf := ⟨∅, W64 0⟩

/-- The readers' first state: bbolt's data `D`, an empty read buffer. -/
def rv0 (D : Data) : RView := (D, rb0)

/-- The batch transaction's first state: bbolt's data `D` committed and in the write transaction
`tx`, empty buffers, nothing pending. -/
def st0 (D : Data) (tx : Loc) : BSess :=
  { C := D, S := D, R := rb0, W := ⟨∅, ∅⟩, pend := W64 0, ndel := W64 0, tx := tx,
    cnt := ⟨0, 0, 0, 0, false⟩ }

theorem bkOf_empty (i : w64) : bkOf (∅ : GMap w64 (List Ent)) i = [] := rfl

theorem rv0_safe (P : BParams) (D : Data) : safeRv P (rv0 D) := by
  intro n i _ _ kc vc e _ he
  simp [rv0, rb0, bkOf_empty] at he

theorem st0_freeOk (P : BParams) (D : Data) (tx : Loc) (hP : P.Wf) : freeOk P (st0 D tx) := by
  have hview : viewOf P (st0 D tx) = dget D := ovB_empty _ _ _ (fun i => bkOf_empty i)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, ?_, rfl⟩
  · intro id es h; simp [st0] at h
  · intro id es h; simp [st0, rb0] at h
  · intro i es h; simp [st0] at h
  · intro i es h; simp [st0, rb0] at h
  · simp [st0]
  · simp [st0]
  · simp [st0]
  · simp [st0]
  · intro _ i; rfl
  · intro _ n _ k
    show dget D n k = ovB P.BT ∅ (viewOf P (st0 D tx)) n k
    rw [ovB_empty _ _ _ (fun i => bkOf_empty i), hview]
  · refine ⟨rv0_safe P D, ?_⟩
    intro n i _ _
    intro kc vc e _ he; simp [st0, bkOf_empty] at he
  · simp only [st0]; exact hP.2.1
  · intro n i _ _; rfl

theorem st0_bgOk (P : BParams) (D : Data) (tx : Loc) : bgOk P (st0 D tx) true wbInit 0 0 := by
  refine ⟨?_, Nat.le_refl 0, ?_, ?_, ⟨Or.inl rfl, Or.inl rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [st0, rb0, wbInit]; word
  · simp [st0]
  · simp [st0]
  · simp [st0]
  · intro i; simp [st0, rb0, bkOf_empty]
  · intro nm i _ _; simp [st0, bkOf_empty]
  · intro _; simp only [st0]; refine ⟨by word, fun h => absurd rfl h⟩
  · simp only [st0, rb0]; word

/-! ## The invariants -/

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

instance tmTok_fractional (γ : BNames) : Fractional (fun q => tmTok (GF := GF) γ q) where
  fractional q1 q2 := by
    unfold tmTok
    constructor
    · iintro ⟨Ha, Hb⟩
      icases ghostVar_split γ.txa () q1 q2 $$ Ha with ⟨Ha1, Ha2⟩
      icases ghostVar_split γ.txb () q1 q2 $$ Hb with ⟨Hb1, Hb2⟩
      iframe
    · iintro ⟨⟨Ha1, Hb1⟩, ⟨Ha2, Hb2⟩⟩
      icombine Ha1 Ha2 as Ha
      icombine Hb1 Hb2 as Hb
      iframe

instance ptOwn_fractional {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    Fractional (fun q => typedPointsto (GF := GF) l v (DFrac.own q)) where
  fractional q1 q2 := typedPointsto_frac_add l v q1 q2

/-- A broadcast channel's owner also has its persistent `Unknown` view. -/
theorem bchan_dup_unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (st : Broadcast) :
    ownBroadcastChan (GF := GF) ch γ Q st ⊢
      ownBroadcastChan ch γ Q st ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hi, Ht⟩
  isplitl [Ht]
  · iapply ownBroadcastChan_close _ _ _ st γch
    iframe Hi Ht
  · iapply ownBroadcastChan_close _ _ _ .Unknown γch
    iframe Hi

/-- Zipping three lists of reader resources into reader tokens. -/
theorem rep_zip (n : Nat) (A B : IProp GF) (γ : GName) :
    ([∗list] _x ∈ List.replicate n (), A) ∗ ([∗list] _x ∈ List.replicate n (), B) ∗
      ownToks γ n ⊢ [∗list] _x ∈ List.replicate n (), iprop(A ∗ B ∗ ownToks γ 1) := by
  induction n with
  | zero =>
    simp only [List.replicate]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    simp only [List.replicate]
    iintro ⟨Ha, Hb, Ht⟩
    icases BigSepL.bigSepL_cons.1 $$ Ha with ⟨Ha1, Ha⟩
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨Hb1, Hb⟩
    icases (ownToks_add 1 n γ).1 $$ Ht with ⟨Ht, Ht1⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha1 Hb1 Ht1]
    · iframe
    · iapply ih $$ [$Ha $Hb $Ht]

theorem gv_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ 1 a ⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  iintro H
  iapply ghostVar_split γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half]
  iexact H

theorem gv_quarters {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    ghostVar (GF := GF) γ (1 : Qp).half a ⊢
      ghostVar γ (1 : Qp).half.half a ∗ ghostVar γ (1 : Qp).half.half a := by
  iintro H
  iapply ghostVar_split γ a (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half]
  iexact H

theorem dgv_halves {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    dghostVar (GF := GF) γ (DFrac.own 1) a ⊢
      dghostVar γ (DFrac.own (1 : Qp).half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half) a := by
  iintro H
  iapply dghostVar_split γ a (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half]
  iexact H

theorem dgv_quarters {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    dghostVar (GF := GF) γ (DFrac.own (1 : Qp).half) a ⊢
      dghostVar γ (DFrac.own (1 : Qp).half.half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half.half) a := by
  iintro H
  iapply dghostVar_split γ a (DFrac.own (1 : Qp).half.half) (DFrac.own (1 : Qp).half.half)
  rw [DFrac.op_own, Qp.half_add_half]
  iexact H

theorem rdMax_split : rdMax = (rdMax - Int.toNat sync.rwmutex.actualMaxReaders) +
    Int.toNat sync.rwmutex.actualMaxReaders := by
  rw [sync.rwmutex.actualMaxReaders_unseal]; decide

theorem cacheInv_alloc (γ : BNames) :
    ghostMapAuth (GF := GF) γ.cached 1 (∅ : GMap (w64 × Nat) Bool) ∗
      ghostVar γ.cur (1 : Qp).half (((W64 0, 0) : w64 × Nat), false) ∗
      ghostVar γ.cvw (1 : Qp).half () ⊢ |={⊤}=> cacheInv γ := by
  iintro ⟨Hc, Hcur, Hcvw⟩
  unfold cacheInv
  iapply inv_alloc
  inext
  iexists ∅, ((W64 0, 0) : w64 × Nat), false
  iframe
  isplitr
  · imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  isplitr
  · ipureintro
    refine ⟨fun k' b h => by simp at h, fun _ h => by simp at h⟩
  ileft
  ipureintro; rfl

theorem intvInv_alloc (γ : BNames) (P : BParams) (rtx : Loc) (cm : GoMap) (D : Data) :
    ownMap (GF := GF) cm (DFrac.own 1) (∅ : GMap w64 Loc) ∗ rtxStats rtx ⊢
      |={⊤}=> intvInv γ P rtx cm D := by
  iintro ⟨Hcm, Hst⟩
  unfold intvInv
  imod inv_alloc (bN.@"intv") ⊤ iprop(∃ (M : GMap w64 Loc) (qm : Rat), □ cmFacts P rtx D M ∗
      ⌜0 ≤ qm ∧ qm ≤ 1⌝ ∗ mapPart cm qm M ∗ tokPart γ (1 - qm)) $$ [Hcm] with #H1
  · inext
    iexists ∅, 1
    isplitr
    · imodintro
      unfold cmFacts
      iapply BigSepM.bigSepM_empty.2
      itrivial
    isplitr
    · ipureintro; exact ⟨by decide, by decide⟩
    unfold mapPart tokPart
    rw [dif_pos (by decide), dif_neg (by grind)]
    iframe
  imod inv_alloc (bN.@"stats") ⊤ iprop(rtxStats rtx ∨ ghostVar γ.txb 1 ()) $$ [Hst] with #H2
  · inext
    ileft
    iexact Hst
  imodintro
  iframe #

theorem wgInv_alloc (γ : BNames) (rtx wg : Loc) (γw γo γt : GName) :
    ownTokAuthDfrac (GF := GF) γ.rdt DFrac.discard rdMax ∗ wg ↦ (zero_val sync.WaitGroup) ∗
      ghostMapAuth γo 1 (∅ : GMap Nat Qp) ∗ txLive rtx (1 : Qp).half ∗ ownToks γ.rdt 0 ⊢
      |={⊤}=> wgInv γ rtx wg γw γo γt := by
  iintro ⟨#Ha, Hwg, Ho, Hl, Ht⟩
  imod sync.init_WaitGroup (bN.@"wg") wg $$ Hwg with ⟨%γwg, #Hiwg, Hc, Hws⟩
  imod inv_alloc (bN.@"wgi") ⊤ (wgBody γ rtx γwg γw γo γt) $$ [Hc Hws Ho Hl Ht] with #Hinv
  · inext
    unfold wgBody
    ileft
    iexists (W32 0), ∅, (1 : Qp).half
    rw [show sint.nat (W32 0) = 0 from rfl]
    iframe Hc Ho Hl Ht
    isplitr
    · ipureintro
      simp only [qsum, GMap.map_size_empty]
      refine ⟨by simp, ?_⟩
      simp
      first | rfl | exact Rat.add_zero _ | decide
    ileft
    iexact Hws
  imodintro
  unfold wgInv
  iexists γwg
  iframe #

/-- The history of a new backend: its first state. -/
def H0 (D : Data) : GMap (w64 × Nat) RView := (∅ : GMap (w64 × Nat) RView).insert (W64 0, 0) (rv0 D)

theorem H0_facts (D : Data) : (H0 D).lookup (W64 0, 0) = some (rv0 D) ∧
    ∀ k rv', (H0 D).lookup k = some rv' → keyLe k (W64 0, 0) := by
  refine ⟨by simp [H0], ?_⟩
  intro k rv' hk
  unfold H0 at hk
  by_cases he : k = (W64 0, 0)
  · subst he; right; exact ⟨rfl, Nat.le_refl 0⟩
  · simp at hk; exact absurd hk.1.symm he

/-- `readTx.mu`'s resource in a new backend: the first interval, its read transaction `rtx`. -/
theorem rtRes_init (γ : BNames) (P : BParams) (rt rtx wg : Loc) (m cm : GoMap) (D : Data)
    (γw γo γt : GName) :
    structFieldRef txReadBuffer go!"txBuffer" (rbufOf (baseOf rt)) ↦
      ({ buckets' := m } : txBuffer) ∗
    structFieldRef txReadBuffer go!"bufVersion" (rbufOf (baseOf rt)) ↦ (W64 0) ∗
    ownMap m (DFrac.own 1) (∅ : GMap w64 Loc) ∗ rbktOf (baseOf rt) ↦ cm ∗
    ghostVar γ.view (1 : Qp).half.half (vData P (rv0 D)) ∗
    ghostVar γ.rd 1 (⟨rtx, wg, γw, γo, γt, 0, false, true, true⟩ : RdSt) ∗
    ghostVar γ.rvs (1 : Qp).half (rv0 D, false) ∗ ghostVar γ.cln (1 : Qp).half true ∗
    ghostVar γ.cur (1 : Qp).half ((((W64 0), 0) : w64 × Nat), false) ∗
    ghostMapAuth γ.hist 1 (H0 D) ∗ histAt γ (W64 0) 0 (rv0 D) ∗
    rtxOf (baseOf rt) ↦ rtx ∗ rwgOf (baseOf rt) ↦ wg ∗
    ownTokAuthDfrac γ.rdt DFrac.discard rdMax ∗ txLive rtx (1 : Qp).half ∗ rtxSnap rtx D ∗
    intvInv γ P rtx cm D ∗ wgInv γ rtx wg γw γo γt ∗ ghostVar γw 1 () ∗ ghostVar γt 1 () ∗
    fkRd γ P (rv0 D) ⊢
    rtRes (GF := GF) γ P rt 1 := by
  iintro ⟨Hrb1, Hrb2, Hm, Hcm, Hv, Hrd, Hrvs, Hcln, Hcur, Hh, #Hh0, Hrtx, Hwg, #Hrdt, Hl, #Hs, #Hi,
    #Hw, Hgw, Hgt, #Hfk⟩
  -- a new backend's view is exact
  ihave Hv := viewQ_exact γ _ _ $$ Hv
  unfold rtRes rtResAt rtRest rtCore rtIntv rbAt bksAt wgOpen clnPart
  iexists ⟨rtx, wg, γw, γo, γt, 0, false, true, true⟩, rv0 D, H0 D, vData P (rv0 D), m, ∅, cm
  simp only [↓reduceIte, Bool.false_eq_true, rv0, rb0]
  rw [GMap.fmap_empty]
  iframe
  iframe #
  isplitr
  · iapply bbs_empty
  isplitr
  · ipureintro; intro id x es h; simp at h
  isplitr
  · ipureintro; intro _ n i _ _; rfl
  isplitr
  · ipureintro
    exact ⟨fun id es h => by simp at h, fun i es h => by simp at h,
      (H0_facts D).1, (H0_facts D).2, fun h => absurd h (by decide), rv0_safe P D⟩
  unfold cacheValid histAt
  iintro !> %i %rv' %hi #Hh' -
  have hi0 : i = 0 := by omega
  subst hi0
  ihave %he := ghostMapElem_agree _ _ _ _ _ _ $$ Hh0 Hh'
  subst he
  iapply thinV_refl

/-- The batch lock's resource in a new backend: free, in its first state. -/
theorem batchFree_init (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t db wtx : Loc) (D : Data)
    (hP : P.Wf) :
    txFOf t ↦ wtx ∗ pendOf t ↦ (W64 0) ∗ delOf t ↦ (W64 0) ∗ ownWB (wbOf t) ⟨∅, ∅⟩ ∗
    bF go!"txPostLockInsideApplyHook" b ↦ func.nil ∗
    dghostVar γ.hook (DFrac.own (1 : Qp).half) func.nil ∗
    ownDB db γ.db D ∗ ownWTx wtx γ.db D D ∗ txDB wtx db ∗
    sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    ghostVar γ.view (1 : Qp).half.half (vData P (rv0 D)) ∗
    ghostVar γ.rvs (1 : Qp).half (rv0 D, false) ∗ ownTokAuth γ.wb wbInit ∗
    monoNatAuthOwn γ.wbc 1 0 ∗ ghostVar γ.used (1 : Qp).half 0 ∗
    dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
    trkHalf γ P D ∗ fkHalf γ P (st0 D wtx) ∗ W ∗ Pk ⊢ batchFree (GF := GF) γ P W Pk b t := by
  iintro ⟨Htxf, Hpend, Hdel, Hwb, Hphk, Hhook, Hown, Hwtx, #Hwdb, Hmus, Hv, Hrvs, Hwba, Hwbc, Hused,
    Hopn, Hhkd, Hfkh, HW, HPk⟩
  unfold batchFree
  ileft
  iexists st0 D wtx, db
  unfold batchPhys batchGhostAt
  isplitl [Htxf Hpend Hdel Hwb Hphk Hhook Hown Hwtx Hmus]
  · iexists func.nil
    simp only [st0]
    iframe
    iframe #
  isplitl [Hv Hrvs Hwba Hwbc Hused Hopn Hhkd Hfkh]
  · ihave Hv := batchViewQ_of_exact γ P (st0 D wtx) $$ [Hv]
    · simp only [st0, rv0, rb0] at *; iexact Hv
    iframe Hv
    simp only [st0, rv0]
    iexists wbInit, 0, 0
    iframe
    ipureintro
    exact st0_bgOk P D wtx
  iframe
  ipureintro
  exact st0_freeOk P D wtx hP

/-- The stop protocol of a new backend. -/
theorem stop_init (γ : BNames) (sc dc : GoChan) (γsc γdc : ChanNames) (b : Loc) :
    bF go!"stopc" b ↦□ sc ∗ bF go!"donec" b ↦□ dc ∗
    isChan sc γsc Unit ∗ ownChan γsc Unit .Idle ∗ isChan dc γdc Unit ∗ ownChan γdc Unit .Idle ∗
    dghostVar γ.sdn (DFrac.own 1) false ⊢
    |={⊤}=> isStopChansAt (GF := GF) γ b sc dc γsc γdc ∗
      ownBroadcastChan dc γdc iprop(True) .Pending := by
  iintro ⟨#Hsc, #Hdc, #Hscc, Hsco, #Hdcc, Hdco, Hsdn⟩
  imod alloc_broadcast_chan (E := ⊤) (stopQ γ) γsc sc $$ Hscc Hsco with Hsb
  icases bchan_dup_unknown _ _ _ _ $$ Hsb with ⟨Hsb, #Hsbu⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γdc dc $$ Hdcc Hdco with Hdb
  icases bchan_dup_unknown _ _ _ _ $$ Hdb with ⟨Hdb, #Hdbu⟩
  imod inv_alloc (bN.@"stop") ⊤
    iprop((ownBroadcastChan sc γsc (stopQ γ) .Pending ∗ dghostVar γ.sdn (DFrac.own 1) false) ∨
     (ghostVar γ.cls 1 () ∗ (dghostVar γ.opn (DFrac.own (1 : Qp).half) false ∨ runTok γ)))
    $$ [Hsb Hsdn] with #Hinv
  · inext; ileft; iframe
  imodintro
  iframe Hdb
  unfold isStopChansAt stopInv
  iframe #

/-- A guard from a list of reader slots. -/
theorem rep_guard (n : Nat) (hn : 0 < n) (rw : Loc) (Q : Qp → IProp GF) :
    ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex rw Q) ⊢
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex rw Q) ∗ sync.isRWMutexGuard rw Q := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [List.replicate]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases sync.ownRWMutex_guard rw Q $$ H1 with ⟨H1, #Hg⟩
  iframe Hg
  iapply BigSepL.bigSepL_cons.2
  iframe

/-- One element of a nonempty list of copies. -/
theorem rep_one (n : Nat) (hn : 0 < n) (A : IProp GF) :
    ([∗list] _x ∈ List.replicate n (), A) ⊢ A := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [List.replicate]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, -⟩
  iexact H1

theorem actualMaxReaders_pos' : 0 < Int.toNat sync.rwmutex.actualMaxReaders := by
  rw [sync.rwmutex.actualMaxReaders_unseal]; omega

/-- Reader tokens from the slots and the readers' budget tokens. -/
theorem rep_rdTok (n : Nat) (γ : BNames) (P : BParams) (b rt tm : Loc) :
    bF go!"readTx" b ↦□ rt ∗ rtmuOf (baseOf rt) ↦□ tm ∗
      ([∗list] _x ∈ List.replicate n (),
        iprop(sync.ownRWMutex (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
          sync.ownRWMutex tm (fun q => tmTok γ q) ∗ ownToks γ.rdt 1)) ⊢
      [∗list] _x ∈ List.replicate n (), rdTok (GF := GF) γ P b := by
  induction n with
  | zero =>
    simp only [List.replicate]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    simp only [List.replicate]
    iintro ⟨#Hrt, #Htm, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨Hr, Ht, Hk⟩, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr Ht Hk]
    · unfold rdTok crTok
      iexists rt
      iframe Hrt Hr
      iexists tm
      iframe
      iframe #
    · iapply ih $$ [$Hrt $Htm $H]

end alloc
section alloc2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The backend's invariants and tokens**, allocated by `newBackend` once `newBatchTxBuffered`
has begun bbolt's transactions (`wtx` writing, `rtx` reading, both over `D`) and the backend's
fields are set: the backend (`isBackend`, its hooks' contract from `hooksOk`), its stop channels,
the clients' shares (`newPost`) and the `run` goroutine's (its spec's premises). The batch lock's
resources are the creator's, made from the client's half of the hook's own keys (`Hmk`) and (D22
receiver epochs, S8a, 2026-10-24) the fresh backend's payment rights (`bFresh`), traded for `K γ`. -/
theorem backend_init (P : BParams) (W Pk K : BNames → IProp GF) (h : GoInterface)
    (b t rt tm wg db lg wtx rtx : Loc) (m cm : GoMap) (γd : DBNames)
    (γrw : sync.rwmutex.RWMutexNames) (D : Data) (sc dc : GoChan) (γsc γdc : ChanNames)
    (hP : P.Wf) (hlg : lg ≠ Loc.null) :
    hooksOk P W Pk h ∗ (∀ γ : BNames, hkOwn γ (hkData P D) ∗ bFresh γ ={⊤}=∗ W γ ∗ Pk γ ∗ K γ) ∗
    bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗ bF go!"batchLimit" b ↦□ P.limit ∗
    bF go!"lg" b ↦□ lg ∗ bF go!"hooks" b ↦□ h ∗ beOf t ↦□ b ∗ rtmuOf (baseOf rt) ↦□ tm ∗
    bF go!"stopc" b ↦□ sc ∗ bF go!"donec" b ↦□ dc ∗ metricsInv b ∗
    sync.isRWMutexGuard (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
    sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗ isDB db ∗
    muOf t ↦ (false : Bool) ∗ txFOf t ↦ wtx ∗ pendOf t ↦ (W64 0) ∗ delOf t ↦ (W64 0) ∗
    ownWB (wbOf t) ⟨∅, ∅⟩ ∗ bF go!"txPostLockInsideApplyHook" b ↦ func.nil ∗
    ownDB db γd D ∗ ownWTx wtx γd D D ∗ txDB wtx db ∗
    sync.rwmutex.isRWMutex (rmuOf (baseOf rt)) γrw (nroot.@"rw") ∗
    sync.rwmutex.ownRWMutex γrw (rwmutex.RLocked 0) ∗
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      sync.rwmutex.ownRLockToken γrw) ∗
    rtxOf (baseOf rt) ↦ rtx ∗ txLive rtx 1 ∗ rtxSnap rtx D ∗ rtxStats rtx ∗
    rwgOf (baseOf rt) ↦ wg ∗ wg ↦ (zero_val sync.WaitGroup) ∗
    structFieldRef txReadBuffer go!"txBuffer" (rbufOf (baseOf rt)) ↦
      ({ buckets' := m } : txBuffer) ∗
    structFieldRef txReadBuffer go!"bufVersion" (rbufOf (baseOf rt)) ↦ (W64 0) ∗
    ownMap m (DFrac.own 1) (∅ : GMap w64 Loc) ∗
    rbktOf (baseOf rt) ↦ cm ∗ ownMap cm (DFrac.own 1) (∅ : GMap w64 Loc) ∗
    tm ↦ (zero_val sync.RWMutex) ∗
    cmuOf b ↦ (false : Bool) ∗ cbufOf b ↦ Loc.null ∗ cverOf b ↦ (W64 0) ∗
    isChan sc γsc Unit ∗ ownChan γsc Unit .Idle ∗ isChan dc γdc Unit ∗ ownChan γdc Unit .Idle ∗
    srSlot b ⊢
    |={⊤}=> ∃ γ : BNames, ⌜γ.db = γd⌝ ∗ newPostK γ P W Pk K b D ∗ isStopChansAt γ b sc dc γsc γdc ∗
      ownBroadcastChan dc γdc iprop(True) .Pending ∗ runTok γ ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ ghostVar γ.used (1 : Qp).half 0 := by
  iintro ⟨#Hhk, Hmk, #Ht, #Hrt, #Hlim, #Hlg, #Hh, #Hbe, #Htm, #Hsc, #Hdc, #Hmi, #Hmug, Hmus,
    #Hdb, Hmx, Htxf, Hpend, Hdel, Hwb, Hphk, Hown, Hwtx, #Hwdb, #Hrw, Hst, Hrtoks, Hrtx, Hlive,
    #Hsnap, Hstats, Hrwg, Hwg, Hrb1, Hrb2, Hm, Hcm, Hcmm, Htmz, Hcmu, Hcbuf, Hcver, #Hscc, Hsco,
    #Hdcc, Hdco, Hsr⟩
  -- the ghost names
  imod ghostVar_alloc () with ⟨%gw, Hgw⟩
  imod ghost_map_alloc_empty (K := Nat) (V := Qp) with ⟨%go, Hgo⟩
  imod ghostVar_alloc () with ⟨%gt, Hgt⟩
  imod ghostVar_alloc (vData P (rv0 D)) with ⟨%gview, Hview⟩
  imod ghostVar_alloc (⟨rtx, wg, gw, go, gt, 0, false, true, true⟩ : RdSt) with ⟨%grd, Hrd⟩
  imod ghost_map_alloc_empty (K := w64 × Nat) (V := RView) with ⟨%ghist, Hhist⟩
  imod ghost_map_insert_persist ((W64 0, 0) : w64 × Nat) (rv0 D) (by rfl) $$ Hhist
    with ⟨Hhist, #Hh0⟩
  imod ghost_map_alloc_empty (K := w64 × Nat) (V := Bool) with ⟨%gcached, Hcached⟩
  imod ghostVar_alloc ((((W64 0), 0), false) : (w64 × Nat) × Bool) with ⟨%gcur, Hcur⟩
  imod dghostVar_alloc (func.nil : GoFunc) with ⟨%ghook, Hhook⟩
  imod dghostVar_alloc false with ⟨%gopn, Hopn⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%gwb, Hwba⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%grdt, Hrdta⟩
  imod ghostVar_alloc () with ⟨%gtxa, Htxa⟩
  imod ghostVar_alloc () with ⟨%gtxb, Htxb⟩
  imod ghostVar_alloc ((rv0 D, false) : RView × Bool) with ⟨%grvs, Hrvs⟩
  imod ghostVar_alloc () with ⟨%gcvw, Hcvw⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%gwbc, Hwbc, -⟩
  imod ghostVar_alloc (0 : Nat) with ⟨%gused, Hused⟩
  imod ghostVar_alloc () with ⟨%gcls, Hcls⟩
  imod dghostVar_alloc false with ⟨%gsdn, Hsdn⟩
  imod ghostVar_alloc () with ⟨%gstk, Hstk⟩
  imod ghostVar_alloc (hkData P D) with ⟨%ghkd, Hhkd⟩
  imod ghostVar_alloc (rbData P D) with ⟨%grbk, Hrbk⟩
  imod ghostVar_alloc true with ⟨%gcln, Hcln⟩
  -- (the backend-compaction stage, O1) the deletable keys' registration, nothing yet
  imod saved_pred_alloc (A := GoString × GoString) (fun _ => iprop(False)) (DFrac.own 1)
    DFrac.valid_own_one with ⟨%gdlg, Hdlg⟩
  -- (O1's fallback) the flag: no key deletable yet
  imod dghostVar_alloc false with ⟨%gdlb, Hdlb⟩
  -- (the compaction keys' tracked absence) their flag, `0` if `D` has none; (question 4) the bit,
  -- `true` if `D`'s are well formed, discarded at once
  imod mono_nat_own_alloc (GF := GF) (fkInit D) with ⟨%gfk, Hfk, #Hfklb⟩
  imod dghostVar_alloc (fkWInit P D) with ⟨%gfkv, Hfkv⟩
  imod dghostVar_persist gfkv 1 (fkWInit P D) $$ Hfkv with #Hfkv
  let γ : BNames := ⟨γd, gview, grd, ghist, gcached, gcur, ghook, gopn, gwb, grdt, gtxa, gtxb,
    grvs, gcvw, gwbc, gused, gcls, gsdn, gstk, ghkd, grbk, gcln, gdlg, gdlb, gfk, gfkv⟩
  icases (fk_halves γ (fkInit D)).1 $$ Hfk with ⟨Hfkb, Hfkc⟩
  have Hok0 : fkOk P (fkInit D) (fkWInit P D) (st0 D wtx) := fkOk_init rfl rfl rfl rfl
  ihave #Hfkr : fkRd γ P (rv0 D) $$ []
  · unfold fkRd fkV
    iexists fkInit D, fkWInit P D
    iframe Hfklb Hfkv
    ipureintro
    exact fkOkRv_of Hok0
  ihave Hfkb : fkHalf γ P (st0 D wtx) $$ [Hfkb]
  · unfold fkHalf fkV
    iexists fkInit D, fkWInit P D
    iframe Hfkb Hfkv
    ipureintro
    exact Hok0
  let rd0 : RdSt := ⟨rtx, wg, gw, go, gt, 0, false, true, true⟩
  -- the shares
  icases gv_halves gview _ $$ Hview with ⟨Hviewc, Hview⟩
  icases gv_quarters gview _ $$ Hview with ⟨Hviewb, Hviewr⟩
  icases gv_halves gcur _ $$ Hcur with ⟨Hcurc, Hcurr⟩
  icases dgv_halves ghook _ $$ Hhook with ⟨Hhookc, Hhookb⟩
  icases dgv_halves gopn _ $$ Hopn with ⟨Hopnc, Hopn⟩
  icases dgv_quarters gopn _ $$ Hopn with ⟨Hopnr, Hopnb⟩
  icases gv_halves grvs _ $$ Hrvs with ⟨Hrvsb, Hrvsr⟩
  icases gv_halves gcvw _ $$ Hcvw with ⟨Hcvwc, Hcvwi⟩
  icases gv_halves gused _ $$ Hused with ⟨Husedb, Husedr⟩
  icases gv_halves ghkd _ $$ Hhkd with ⟨Hhkdb, Hhkdc⟩
  icases gv_halves grbk _ $$ Hrbk with ⟨Hrbkb, Hrbkc⟩
  icases gv_halves gcln _ $$ Hcln with ⟨Hclnc, Hclnr⟩
  -- the tokens
  imod ownTokAuth_add wbInit gwb 0 $$ Hwba with ⟨Hwba, Hwbt⟩
  imod ownTokAuth_add rdMax grdt 0 $$ Hrdta with ⟨Hrdta, Hrdtt⟩
  simp only [Nat.zero_add]
  imod (update_into_persistently (P := ownTokAuthDfrac (GF := GF) grdt (DFrac.own 1) rdMax))
    $$ Hrdta with #Hrdta
  rw [rdMax_split]
  icases (ownToks_add _ _ grdt).1 $$ Hrdtt with ⟨-, Hrdtt⟩
  rw [← rdMax_split]
  imod ownToks_0 (GF := GF) grdt with Hrdt0
  -- the cache's invariant
  imod cacheInv_alloc γ $$ [Hcached Hcurc Hcvwi] with #Hcinv
  · iframe
  -- the first interval and `readTx.mu`
  icases ((txLive_fractional rtx).fractional (1 : Qp).half (1 : Qp).half).1 $$ [Hlive]
    with ⟨Hlive1, Hlive2⟩
  · rw [Qp.half_add_half]; iexact Hlive
  imod intvInv_alloc γ P rtx cm D $$ [Hcmm Hstats] with #Hintv
  · iframe
  imod wgInv_alloc γ rtx wg gw go gt $$ [Hwg Hgo Hlive2 Hrdt0] with #Hwgi
  · iframe
    iframe #
  ihave Hrt1 := rtRes_init γ P rt rtx wg m cm D gw go gt $$
    [Hrb1 Hrb2 Hm Hcm Hviewr Hrd Hrvsr Hclnr Hcurr Hhist Hrtx Hrwg Hlive1 Hgw Hgt]
  · unfold histAt
    iframe
    iframe #
  imod init_RWMutex_guard (rtRes γ P rt) (E := ⊤) (rmuOf (baseOf rt)) γrw $$
    [Hst Hrtoks Hrt1] with Hrmus
  · iframe
    iframe #
    iapply rtRes_frac
  -- `txMu`
  imod sync.init_RWMutex (fun q => tmTok γ q) (E := ⊤) tm (HPfrac := tmTok_fractional γ) $$
    [Htxa Htxb] Htmz with Htms
  · inext; unfold tmTok; iframe
  -- the cache's mutex
  imod sync.init_Mutex (cacheRes γ P b) ⊤ (cmuOf b) $$ [Hcmu] [Hcbuf Hcver] with #Hcmx
  · iexact Hcmu
  · inext; unfold cacheRes; iexists Loc.null, W64 0; iframe; ileft; ipureintro; rfl
  -- the batch lock
  ihave Hko : hkOwn γ (hkData P D) $$ [Hhkdc]
  · unfold hkOwn; iexact Hhkdc
  ihave Hfr : bFresh γ $$ [Hwbt Hopnc Hcls]
  · unfold bFresh bOpen; iframe Hwbt Hopnc Hcls
  ispecialize Hmk $$ %γ [$Hko $Hfr]
  imod Hmk with ⟨HW, HPk, HK⟩
  imod sync.init_Mutex (batchFree γ P (W γ) (Pk γ) b t) ⊤ (muOf t) $$ [Hmx]
    [Htxf Hpend Hdel Hwb Hphk Hhookb Hown Hwtx Hmus Hviewb Hrvsb Hwba Hwbc Husedb Hopnb Hhkdb Hrbkb
      Hfkb HW HPk]
    with #Hbl
  · iexact Hmx
  · inext
    iapply batchFree_init γ P (W γ) (Pk γ) b t db wtx D hP
    unfold trkHalf
    iframe
    iframe #
  -- the guards of `readTx.mu` and `txMu`
  have hn : 0 < Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; omega
  icases rep_guard _ hn (rmuOf (baseOf rt)) (rtRes γ P rt) $$ Hrmus with ⟨Hrmus, #Hrg⟩
  icases rep_guard _ hn tm (fun q => tmTok γ q) $$ Htms with ⟨Htms, #Htg⟩
  -- the backend
  ihave #Hnh : isBackendNH γ P (W γ) (Pk γ) b h $$ []
  · unfold isBackendNH
    iintro !>
    iexists t, rt, tm, db, lg
    iframe #
    ipureintro; exact ⟨hlg, hP⟩
  ihave #Hb : isBackend γ P (W γ) (Pk γ) b $$ []
  · iapply isBackend_of_hooks γ P (W γ) (Pk γ) b h
    iframe #
    iintro !> Hb' %t' #Ht'
    iunfold hooksOk at Hhk
    iapply Hhk $$ Hb' Ht'
  -- the stop protocol
  imod stop_init γ sc dc γsc γdc b $$ [Hsco Hdco Hsdn] with ⟨#Hstop, Hdcp⟩
  · iframe
    iframe #
  -- the readers' tokens
  ihave Hrds := rep_zip (Int.toNat sync.rwmutex.actualMaxReaders)
    (sync.ownRWMutex (rmuOf (baseOf rt)) (rtRes γ P rt)) (sync.ownRWMutex tm (fun q => tmTok γ q))
    γ.rdt $$ [Hrmus Htms Hrdtt]
  · iframe Hrmus Htms
    iexact Hrdtt
  ihave Hrds := rep_rdTok (Int.toNat sync.rwmutex.actualMaxReaders) γ P b rt tm $$ [Hrds]
  · iframe #
    iexact Hrds
  imodintro
  iexists γ
  isplitr
  · ipureintro; rfl
  isplitl [HK Hviewc Hcvwc Hclnc Hhookc Hrbkc Hrds Hdlg Hdlb Hfkc Hsr]
  · unfold newPostK
    isplitr
    · iexact Hb
    isplitr
    · unfold isStopChans
      iexists sc, dc, γsc, γdc
      iexact Hstop
    isplitl [HK]
    · iexact HK
    isplitl [Hviewc Hcvwc Hclnc]
    · unfold bViewC
      simp only [rv0, rb0]
      iframe Hviewc Hcvwc Hclnc
    isplitl [Hhookc]
    · unfold plHook plHookAt
      iexact Hhookc
    isplitl [Hrbkc]
    · unfold rbOwn; iexact Hrbkc
    isplitl [Hrds]
    · iexact Hrds
    isplitl [Hdlg Hdlb]
    · unfold dlInit
      iframe Hdlg Hdlb
    isplitl [Hfkc]
    · unfold fkCl fkOwn fkV
      iframe Hfkc Hfkv
    iexact Hsr
  unfold runTok
  iframe Hstop Hdcp Hstk Hopnr Husedr

end alloc2

end backend
end EtcdGrove
end Perennial
