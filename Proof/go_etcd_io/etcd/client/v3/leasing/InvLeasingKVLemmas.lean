/-
Lemmas about the leasing KV's vocabulary (`InvLeasingKV.lean`): the KV's part of the cache's lock
(`leasingX`: what a reader learns, the steps of the log), and the wait group (`get`'s `Add(1)`
and its goroutine's `Done()`, after `InvCache.lean`'s). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV
public import Proof.go_etcd_io.etcd.client.v3.leasing.PoolLoans

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-! ## The KV's part of the cache's lock -/

/-- **A reader learns that the state it read is in the log** (`lcPeek`, for the cache's readers). -/
theorem leasingX_peek (lkv : Loc) (γ : LeasingNames) :
    ⊢ lcPeek (GF := GF) (leasingX lkv γ) (leasingSeen γ) := by
  unfold lcPeek
  iintro !>
  iintro %st %q HX
  unfold leasingX leasingXBody
  icases HX with ⟨%x, Hs, Hsc, Hl, %Hlast, Hn, #Hso, #Hsco⟩
  ihave #Hlb := monoListLbOwn_get γ.log q x.2.2 $$ Hl
  have hi : x.2.2[x.2.2.length - 1]? = some st := by
    rw [← List.getLast?_eq_getElem?]; exact Hlast
  ihave #Hidx := monoListIdxOwn_get (x.2.2.length - 1) st hi $$ Hlb
  isplitl
  · iexists x
    iframe
    iframe #
    ipureintro; exact Hlast
  · imodintro
    unfold leasingSeen
    iexists _
    iexact Hidx

/-- **A step of the cache**: the whole of the KV's part for `st` becomes the part for `st'`, the
log gaining `st'` after `st`. -/
theorem leasingX_step (lkv : Loc) (γ : LeasingNames) (st st' : LeaseCacheSt) :
    leasingX (GF := GF) lkv γ st 1 ==∗ leasingX lkv γ st' 1 ∗ leasingStep γ st st' := by
  unfold leasingX leasingXBody
  iintro ⟨%x, Hs, Hsc, Hl, %Hlast, Hn, #Hso, #Hsco⟩
  imod monoListAuthOwn_update_app (γ := γ.log) [st'] $$ Hl with ⟨Hl, #Hlb⟩
  have hne : x.2.2 ≠ [] := by intro h; rw [h] at Hlast; simp at Hlast
  have hi : x.2.2[x.2.2.length - 1]? = some st := by
    rw [← List.getLast?_eq_getElem?]; exact Hlast
  have hi2 : (x.2.2 ++ [st'])[x.2.2.length - 1 + 1]? = some st' := by
    have := List.length_pos_iff.mpr hne
    rw [show x.2.2.length - 1 + 1 = x.2.2.length by omega]; simp
  have hi1' : (x.2.2 ++ [st'])[x.2.2.length - 1]? = some st := by
    rw [List.getElem?_append_left (by have := List.length_pos_iff.mpr hne; omega)]; exact hi
  ihave #H1 := monoListIdxOwn_get (x.2.2.length - 1) st hi1' $$ Hlb
  ihave #H2 := monoListIdxOwn_get (x.2.2.length - 1 + 1) st' hi2 $$ Hlb
  imodintro
  isplitl
  · iexists (x.1, x.2.1, x.2.2 ++ [st'])
    iframe
    iframe #
    ipureintro; simp
  · unfold leasingStep
    iexists _
    iframe #

/-- The step premise of the cache's writers (`Evict`, `Add`, `Delete`, ...), for the transition `f`. -/
theorem leasingX_stepF (lkv : Loc) (γ : LeasingNames) (f : LeaseCacheSt → LeaseCacheSt) :
    ⊢ ∀ st : LeaseCacheSt, leasingX (GF := GF) lkv γ st 1 ={⊤}=∗
      leasingX lkv γ (f st) 1 ∗ leasingStep γ st (f st) := by
  iintro %st HX
  imod leasingX_step lkv γ st (f st) $$ HX with ⟨HX, Hs⟩
  imodintro
  iframe

/-- The KV's part does not depend on the waiter channels (`Lock`, `LockRange`, `LockWriteOps`). -/
theorem leasingX_waitc (lkv : Loc) (γ : LeasingNames) :
    ⊢ lcWaitcStep (GF := GF) (leasingX lkv γ) := by
  unfold lcWaitcStep
  iintro !>
  iintro %st %st' %_ HX
  imod leasingX_step lkv γ st st' $$ HX with ⟨HX, -⟩
  imodintro
  iexact HX

/-- **The `session` field** under the cache's lock (any fraction): its value `s`, what a set
session gives (`sessionOk`), `sessionReady` if it is set, and the way back. -/
theorem leasingX_session (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt) (q : Qp) :
    leasingX (GF := GF) lkv γ st q ⊢ ∃ s : Loc,
      structFieldRef leasingKV go!"session" lkv ↦{DFrac.own q.half} s ∗ □ sessionOk γ s ∗
      □ (if s = null then iprop(True) else sessionReady γ) ∗
      (structFieldRef leasingKV go!"session" lkv ↦{DFrac.own q.half} s -∗ leasingX lkv γ st q) := by
  unfold leasingX leasingXBody
  iintro ⟨%x, Hs, Hsc, Hl, %Hlast, Hn, #Hso, #Hsco⟩
  ihave #Hlb := monoNatLbOwn_get γ.sess q (sessN x.1) $$ Hn
  iexists x.1
  iframe Hs
  iframe #
  isplitr
  · imodintro
    unfold sessN sessionReady
    by_cases h : x.1 = null
    · simp only [h, ↓reduceIte]; itrivial
    · simp only [h, ↓reduceIte]
      iapply (monoNatLbOwn_le 1 (by simp)) $$ Hlb
  iintro Hs
  iexists x
  iframe
  iframe #
  ipureintro; exact Hlast

/-- **The `session` field once a session was set**: it is not nil. -/
theorem leasingX_session_ready (lkv : Loc) (γ : LeasingNames) (st : LeaseCacheSt) (q : Qp) :
    sessionReady (GF := GF) γ ∗ leasingX lkv γ st q ⊢ ∃ s : Loc,
      structFieldRef leasingKV go!"session" lkv ↦{DFrac.own q.half} s ∗ ⌜s ≠ null⌝ ∗
      □ sessionOk γ s ∗
      (structFieldRef leasingKV go!"session" lkv ↦{DFrac.own q.half} s -∗ leasingX lkv γ st q) := by
  unfold leasingX leasingXBody
  iintro ⟨#Hr, %x, Hs, Hsc, Hl, %Hlast, Hn, #Hso, #Hsco⟩
  unfold sessionReady
  ihave %Hv := monoNatLbOwn_valid γ.sess q (sessN x.1) 1 $$ Hn Hr
  have hne : x.1 ≠ null := by
    intro h; simp [sessN, h] at Hv
  iexists x.1
  iframe Hs
  iframe #
  isplitr
  · ipureintro; exact hne
  iintro Hs
  iexists x
  iframe
  iframe #
  ipureintro; exact Hlast

/-! ## The wait group -/

theorem leasingWg_mask : (↑leasingWgWGN : CoPset) ⊆ ⊤ \ ↑leasingWgN :=
  sync.wg_mask_ndot_ne nroot "leasingWaitGroup" "leasingWgCounter" (by decide)

/-- The "open" token's fractions add up to at most `1`. -/
theorem leasingOpen_excl (γ : LeasingNames) (q : Qp) :
    leasingOpen (GF := GF) γ q ∗ leasingOpen γ 1 ⊢ False := by
  unfold leasingOpen
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives % ⟨Hv, -⟩
  exfalso
  have h1 := Qp.le_iff.1 Hv
  have h2 := q.2
  simp only [Qp.val_add, Qp.val_one] at h1
  grind

theorem leasingWg_ctr_bound {k d n : Nat} {T : Nat} (Hbound : T + leasingWgOwedMax ≤ 2 ^ 31)
    (Hk : k + n < T) (Hd : d ≤ leasingWgOwedMax) : k + d + n < 2 ^ 31 := by
  unfold leasingWgOwedMax at *; omega

/-! ## The pool of the cache's reader slots -/

/-- The leasing KV's pool of its cache's reader slots. -/
theorem isLeasingKV_pool (lkv : Loc) (γ : LeasingNames) (pfx : GoString) :
    isLeasingKV (GF := GF) lkv γ pfx ⊢ threadPool.isThreadPool leasingPoolN γ.rp (lkvReader lkv γ pfx) := by
  iintro #Hlkv
  iunfold isLeasingKV at Hlkv
  icases Hlkv with ⟨%_, %_, %_, %_, %_, %_, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hpool, -⟩
  iexact Hpool

/-- **A thread borrows a reader slot** of the leasing KV's cache with its thread token. -/
theorem lkv_borrow (lkv : Loc) (γ : LeasingNames) (pfx : GoString) :
    isLeasingKV (GF := GF) lkv γ pfx ∗ threadTok ⊢
      |={⊤}=> ▷ lkvReader lkv γ pfx ∗ threadPool.ownThreadLoan γ.rp := by
  iintro ⟨#Hlkv, Htok⟩
  ihave #Hpool := isLeasingKV_pool lkv γ pfx $$ Hlkv
  iapply threadPool.borrow leasingPoolN γ.rp (lkvReader lkv γ pfx) ⊤ (fun _ _ => CoPset.mem_full)
  iframe #; iframe

/-- **A borrowed reader slot given back**, for the thread token. -/
theorem lkv_giveBack (lkv : Loc) (γ : LeasingNames) (pfx : GoString) :
    isLeasingKV (GF := GF) lkv γ pfx ∗ threadPool.ownThreadLoan γ.rp ∗ lkvReader lkv γ pfx ⊢
      |={⊤}=> threadTok := by
  iintro ⟨#Hlkv, Hloan, Hrd⟩
  ihave #Hpool := isLeasingKV_pool lkv γ pfx $$ Hlkv
  iapply threadPool.giveBack leasingPoolN γ.rp (lkvReader lkv γ pfx) ⊤ (fun _ _ => CoPset.mem_full)
  iframe #; iframe

/-- A transaction being built names its leasing KV. -/
theorem ownTxnLeasing_lkv (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) :
    ownTxnLeasing (GF := GF) txn lkv γ pfx ctx cs b ⊢
      ownTxnLeasing txn lkv γ pfx ctx cs b ∗ isLeasingKV lkv γ pfx := by
  iintro H
  unfold ownTxnLeasing
  icases H with ⟨%t, %B, %csl, %tsl, %esl, %tops, %eops, H1, H2, H3, H4, #Hlkv, H5⟩
  iframe #
  iexists t, B, csl, tsl, esl, tops, eops
  iframe

/-- The pool's namespace is outside the wait-group counter's. -/
theorem leasingPool_mask : (↑leasingPoolN : CoPset) ⊆ ⊤ \ ↑leasingWgN :=
  sync.wg_mask_ndot_ne nroot "leasingReaderPool" "leasingWgCounter" (by decide)

/-- `lkv.wg.Add(1)` (`get`'s, before starting a lease monitor) with a loan receipt of the reader-slot
pool (`R` its resource), with a fraction of the "open" token (no `Close` waits meanwhile): the
receipt is deposited for a running token (the monitor keeps the borrowed slot; the caller receives a
fresh thread token at its `go` statement, `wp_fork_tok_self`). The counter's bound: the deposited
receipts and this one are fewer than the live threads (`threadPool.loans_lt`). -/
theorem wp_leasingWg_Add (lkv : Loc) (γ : LeasingNames) (q : Qp) (R : IProp GF)
    (Hbound : threadBound GF + leasingWgOwedMax ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ threadPool.isThreadPool leasingPoolN γ.rp R ∗
        leasingOpen γ q ∗ threadPool.ownThreadLoan γ.rp }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); leasingWgRunning γ ∗ leasingOpen γ q }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, #Hpool, Hopen, Hloan⟩ HΦ
  iapply sync.WaitGroup.wp_Add (lkvWg lkv) (W64 1) γ.wg leasingWgWGN $$ [] [Hopen Hloan HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, >Hwgo, >Hwt, >Hrun, >Hk, >Hoauth, >Hcap, >Hcauth,
    >%Hctr, >%Hkd, Hwn⟩
  unfold threadPool.ownThreadLoan
  icombine Hk Hloan as Hk
  imod threadPool.loans_lt leasingPoolN γ.rp R _ leasingPool_mask (k + 1) $$ [Hpool Hk]
    with ⟨%Hlt, Hk⟩
  · iframe #; iexact Hk
  iapply fupd_mask_intro leasingWg_mask
  iintro Hmask
  inext
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply leasingOpen_excl γ q $$ [$Hopen $Hop1]
  subst Hw0
  icombine Hcauth Hcap gives %Hd
  have hb := leasingWg_ctr_bound (n := 1) Hbound Hlt Hd
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have hle : sint.Z ctr + 1 ≤ 2 ^ 31 - 1 := by omega
  have hn : sint.nat (ctr + W32 (sint.Z (W64 1))) = sint.nat ctr + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwt
  iintro Hwt Hwgo
  imod Hmask with -
  imod ownTokAuth_S γ.wr k $$ Hrun with ⟨Hrun, Hrtok⟩
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap Hcauth] with -
  · inext
    unfold leasingWgInv
    iexists ctr + W32 (sint.Z (W64 1)), 0, k + 1, d
    rw [hn]
    iframe
    isplitr
    · ipureintro
      have : sint.Z (ctr + W32 (sint.Z (W64 1))) = sint.Z ctr + 1 := by
        rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
      omega
    isplitr
    · ipureintro; omega
    ileft; ipureintro; rfl
  imodintro
  iapply HΦ
  unfold leasingWgRunning
  iframe

/-- `lkv.wg.Done()` by a goroutine started with `wp_leasingWg_Add`: it gets its loan receipt back
(which, with its slot, the pool exchanges for the thread token it exits with). -/
theorem wp_leasingWg_Done (lkv : Loc) (γ : LeasingNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ leasingWgRunning γ }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadPool.ownThreadLoan γ.rp }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hrtok⟩ HΦ
  iapply sync.WaitGroup.wp_Done (lkvWg lkv) γ.wg leasingWgWGN $$ [] [Hrtok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro leasingWg_mask
  iintro Hmask
  inext
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth,
    %Hctr, %Hkd, Hwn⟩
  unfold leasingWgRunning
  icombine Hrun Hrtok gives %Hle
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  icases ownToks_add_1 1 k' γ.rp $$ Hk with ⟨Hk, Htok⟩
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.wr k' $$ Hrun Hrtok with Hrun
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap Hcauth Hwn] with -
  · inext
    unfold leasingWgInv
    iexists ctr - W32 1, wn, k', d
    rw [hn]
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  unfold threadPool.ownThreadLoan
  iexact Htok

end lemmas

end EtcdGrove
end Perennial
