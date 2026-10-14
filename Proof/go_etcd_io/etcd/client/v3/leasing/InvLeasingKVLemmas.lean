/-
Lemmas about the leasing KV's vocabulary (`InvLeasingKV.lean`): the KV's part of the cache's lock
(`leasingX`: what a reader learns, the steps of the log), and the wait group (`get`'s `Add(1)`
and its goroutine's `Done()`, after `InvCache.lean`'s). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- `lkv.wg.Add(1)` (`get`'s, before starting a lease monitor) by a thread with its thread token,
with a fraction of the "open" token (no `Close` waits meanwhile): the thread's token is deposited
(the caller receives a fresh one at its `go` statement, `wp_fork_tok_self`) for a running token. -/
theorem wp_leasingWg_Add (lkv : Loc) (γ : LeasingNames) (q : Qp)
    (Hbound : threadBound GF + leasingWgOwedMax ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ leasingOpen γ q ∗ threadTok }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); leasingWgRunning γ ∗ leasingOpen γ q }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hopen, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Add (lkvWg lkv) (W64 1) γ.wg leasingWgWGN $$ [] [Hopen Htok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro leasingWg_mask
  iintro Hmask
  inext
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth,
    %Hctr, %Hkd, Hwn⟩
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply leasingOpen_excl γ q $$ [$Hopen $Hop1]
  subst Hw0
  icases threadToks_add_one_lt k $$ [Htok Hk] with ⟨%Hlt, Hk⟩
  · iframe
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

/-- `lkv.wg.Done()` by a goroutine started with `wp_leasingWg_Add`: it gets a thread token back
(to exit with). -/
theorem wp_leasingWg_Done (lkv : Loc) (γ : LeasingNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ leasingWgRunning γ }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
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
  icases (threadToks_add k' 1).1 $$ Hk with ⟨Hk, Htok⟩
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
  iexact Htok

end lemmas

end EtcdGrove
end Perennial
