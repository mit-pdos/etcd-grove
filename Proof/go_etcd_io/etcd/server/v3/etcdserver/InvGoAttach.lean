/-
**`GoAttach`'s goroutines** (`server.go`: `GoAttach`, `run`'s deferred shutdown): the server's
`wgMu` (a `sync.RWMutex`), `wg` (a `sync.WaitGroup`) and `stopping` (a capacity-1 channel closed
once, `StopChan.lean`). Lean-first (the request path's unit 4c, 2026-10-13); see
`notes/decisions.md`, "The server's goroutines: the FIFO scheduler as a chain of saved
postconditions, the construction premise".

**The protocol.** `GoAttach(f)` read-locks `wgMu`, checks that `stopping` is not closed (a
non-blocking receive), `wg.Add(1)`s and starts `f` in a goroutine that `wg.Done()`s when `f`
returns; `run`'s shutdown write-locks `wgMu`, closes `stopping`, unlocks, and later `wg.Wait()`s.
So no `Add` from zero races the `Wait` (Perennial's `WaitGroup` spec forbids it): the ghost flag
`open` (`γ.b`, a ghost variable, half the lock's resource, half the invariant's) is `true` until
the close; while it is, the invariant holds the wait group's "no waiters" (`ownWaitGroupWaiters 0`,
which an `Add` from zero needs), and the lock's resource holds the closer's flag of `stopping` (a
fraction per reader: a reader sees the channel open, `stop_chan_nonblocking_receive_open`); the
writer, with all of it, closes `stopping`, sets `open` to `false` and takes the "no waiters" out
for its `Wait`.

**The counter's bound** (Perennial's `WaitGroup.Add` asks for no `int32` overflow): as the cache's
wait group (`Proof/go_etcd_io/etcd/cache/v3/InvCache.lean`, `cacheWgInv`), each goroutine started
deposits a **thread token** (`threadToks k`, Perennial's `Threads.lean`): the caller's at its `Add`,
which the `go` statement gives back fresh (`wp_fork_tok`), the goroutine taking a deposited one at
its `Done` to exit with. So the counter `k` is below `threadBound GF`, at most `2 ^ 31` (the
construction premise's bound on live goroutines).

**What a caller of `GoAttach` holds** (`srvGoRes s`): a reader slot of `wgMu` (`srvWgReader s`,
with the persistent protocol `srvGoAttachOk s γ`: Perennial's `RWMutex` bounds the readers) and
its thread token; it gets both back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Perennial.Proof.sync
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- The ghost names of `GoAttach`'s protocol: the flag `open`, the closer's token (`run`'s
shutdown's, deposited when it closes `stopping`), the wait group's, the started
goroutines' receipts, the `stopping` channel's (its channel names and its closer's flag),
(H2, 2026-11-05) the waiter's token (`wt`: the invariant's while open, handed to the closer with
the wait group's "no waiters", deposited by its `Wait`), and (revoke-open pass 2, 2026-11-06) the
pending adds' receipts (`pend`: an `Add` whose `go` statement has not run yet, `goPending`). -/
structure GoNames where
  b : GName
  close : GName
  wg : sync.WaitGroupNames
  run : GName
  ch : ChanNames
  chi : BroadcastInternalNames
  wt : GName
  pend : GName

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvWgAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"wg" s
abbrev srvWgMuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"wgMu" s
abbrev srvCtxAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"ctx" s
abbrev srvStoppingAddr' (s : Loc) : Loc := structFieldRef EtcdServer go!"stopping" s

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The wait group's namespace (`sync.isWaitGroup`). -/
def goAttachWGN : Namespace := nroot.@"srvWaitGroup"
/-- The counter's invariant's namespace (`goAttachInv`). -/
def goAttachN : Namespace := nroot.@"srvGoAttach"

theorem goAttach_mask : (↑goAttachWGN : CoPset) ⊆ ⊤ \ ↑goAttachN :=
  sync.wg_mask_ndot_ne nroot "srvWaitGroup" "srvGoAttach" (by decide)

/-- The `stopping` channel's part of the lock's resource at fraction `q`: while open, a fraction
of the closer's flag; once closed, the flag discarded (persistent). -/
def stopPart (γ : GoNames) (b : Bool) (q : Qp) : IProp GF :=
  if b then dghostVar γ.chi.doneGn (DFrac.own q.half) false
  else dghostVar γ.chi.doneGn DFrac.discard true

/-- **`wgMu`'s resource** at fraction `q`: half the flag `open` (scaled) and the channel's part. -/
def wgMuP (γ : GoNames) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, ghostVar γ.b q.half b ∗ stopPart γ b q)

/-- **The counter's invariant**: the other half of `open`; the wait group's counter `ctr`, `d`
goroutines started (their receipts' authority) with their level-0 tokens deposited and `q` adds
pending with their callers' level-1 tokens (revoke-open Q4, 2026-11-06: until then `k` started
goroutines with their whole thread tokens; `GoAttach`'s `Add` deposits the caller's `levelTok 1`,
the `go` statement deposits the fresh token's level 0 and returns the pending level 1, so the
counter `d + q` is below `2 * threadBound GF`; pass 2: the pending adds' receipts' authority at
`q`, so that the `go` statement, holding its `Add`'s receipt, finds a level-1 token to take); while open,
no waiter (and the waiter's token); once closed, the closer's token (so `run`'s shutdown, holding
it, knows it closes an open channel). (H2, 2026-11-05) The receipts' authority is whole, or, once
the shutdown's `Wait` has seen the counter at `0` (with the protocol closed), half of it at `0`: the
other half is the waiter's `goWaited`, which no running receipt survives (`goWaited_running`); the
waiter's token is then deposited, so there is one `goWaited`. -/
def goAttachInv (γ : GoNames) : IProp GF :=
  iprop(∃ (b : Bool) (ctr : w32) (d q : Nat) (dq : DFrac), ghostVar γ.b (1 : Qp).half b ∗
    sync.ownWaitGroup γ.wg ctr ∗ levelToks 0 d ∗ levelToks 1 q ∗ ownTokAuthDfrac γ.run dq d ∗
    ownTokAuth γ.pend q ∗ ⌜0 ≤ sint.Z ctr ∧ sint.nat ctr = d + q⌝ ∗
    ⌜dq = DFrac.own 1 ∨ (dq = DFrac.own (1 : Qp).half ∧ d = 0 ∧ q = 0 ∧ b = false)⌝ ∗
    (⌜b = false⌝ ∗ token γ.close ∗ (⌜dq = DFrac.own 1⌝ ∨ token γ.wt) ∨
      ⌜b = true⌝ ∗ sync.ownWaitGroupWaiters γ.wg 0 ∗ token γ.wt))

/-- **`GoAttach`'s protocol at `s`** (persistent): the `stopping` channel, the wait group, the
counter's invariant, `wgMu`'s write side, the context field (set by `start` before any goroutine,
read by the apply thread's alarm goroutine), the logger (`GoAttach` warns when stopped; revoke-open
Q3, 2026-11-06: with the transport's pool of `lgMu` readers, `raftPool`, from which the stopped branch
borrows with the caller's level-1 token), and the bound on live goroutines (`2 * threadBound GF ≤
2 ^ 31`: the counter counts started goroutines and pending adds). -/
def srvGoAttachOk (s : Loc) (γ : GoNames) : IProp GF :=
  iprop(∃ (ch : Loc) (c : GoInterface), srvStoppingAddr' s ↦□ ch ∗
    isStopChanInternal ch γ.ch γ.chi iprop(True) ∗
    sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗ inv goAttachN (goAttachInv γ) ∗
    sync.isRWMutexGuard (srvWgMuAddr s) (wgMuP γ) ∗ srvCtxAddr s ↦□ c ∗
    (∃ l : Loc, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝) ∗ raftPool (srvLgReader s) ∗
    ⌜2 * threadBound GF ≤ 2 ^ 31⌝)

instance srvGoAttachOk_persistent (s : Loc) (γ : GoNames) :
    Persistent (srvGoAttachOk (GF := GF) s γ) := by
  unfold srvGoAttachOk; infer_instance

/-- **A reader slot of `s.wgMu`** at the protocol's names `γ`, with the protocol. -/
def srvWgReaderAt (s : Loc) (γ : GoNames) : IProp GF :=
  iprop(srvGoAttachOk s γ ∗ sync.ownRWMutex (srvWgMuAddr s) (wgMuP γ))

/-- **A reader slot of `s.wgMu`**, with the protocol. -/
def srvWgReader (s : Loc) : IProp GF :=
  iprop(∃ γ : GoNames, srvWgReaderAt s γ)

/-- **What a goroutine needs to `GoAttach`**: a reader slot of `wgMu` and its thread token. -/
def srvGoRes (s : Loc) : IProp GF := iprop(srvWgReader s ∗ threadTok)

/-- (H2, 2026-11-05) **`srvGoRes` at the protocol's names `γ`** (`GoAttach`'s spec: the receipt
its goroutine gets is at `γ`). -/
def srvGoResAt (s : Loc) (γ : GoNames) : IProp GF := iprop(srvWgReaderAt s γ ∗ threadTok)

/-- A started goroutine's receipt (its `Done` takes a deposited thread token back). -/
def goRunning (γ : GoNames) : IProp GF := ownToks γ.run 1

/-- (revoke-open pass 2, 2026-11-06) **A pending add's receipt**: `GoAttach`'s `Add` deposited the
caller's level-1 token; its `go` statement takes one back (`goAttach_fork`). -/
def goPending (γ : GoNames) : IProp GF := ownToks γ.pend 1

/-- (H2, 2026-11-05) **The shutdown's `Wait` returned** (exclusive): half the receipts' authority
at `0` (`wp_goAttach_Wait`). -/
def goWaited (γ : GoNames) : IProp GF := ownTokAuthDfrac γ.run (DFrac.own (1 : Qp).half) 0

theorem srvGoRes_open (s : Loc) : srvGoRes (GF := GF) s ⊢ ∃ γ : GoNames, srvGoResAt s γ := by
  iintro H
  iunfold srvGoRes at H
  iunfold srvWgReader at H
  icases H with ⟨⟨%γ, Hr⟩, Ht⟩
  iexists γ
  iunfold srvGoResAt
  iframe Hr Ht

theorem srvGoResAt_close (s : Loc) (γ : GoNames) : srvGoResAt (GF := GF) s γ ⊢ srvGoRes s := by
  iintro H
  iunfold srvGoResAt at H
  icases H with ⟨Hr, Ht⟩
  iunfold srvGoRes
  iframe Ht
  iunfold srvWgReader
  iexists γ
  iexact Hr

/-- No receipt is running once `Wait` returned. -/
theorem goWaited_running (γ : GoNames) : goWaited (GF := GF) γ ∗ goRunning γ ⊢ False := by
  iintro ⟨Hw, Hr⟩
  iunfold goWaited at Hw
  iunfold goRunning at Hr
  icombine Hw Hr gives %Hle
  omega

/-- A closure's postcondition given its receipt back (`GoAttach`'s callers whose closures only
frame it). -/
theorem goRunning_frame (γ : GoNames) (Q : IProp GF) :
    goRunning γ ⊢ ▷ (goRunning γ -∗ Q) -∗ ▷ (True -∗ Q) := by
  iintro Hr HQ
  inext
  iintro -
  iapply HQ
  iexact Hr

/-- `wgMu`'s resource is fractional (for `sync.init_RWMutex`). -/
instance wgMuP_fractional (γ : GoNames) : Fractional (wgMuP (GF := GF) γ) where
  fractional q1 q2 := by
    have hgv := fun (b : Bool) => (ghostVar_fractional (GF := GF) γ.b b).fractional q1.half q2.half
    have hdv := (dghostVar_fractional (GF := GF) γ.chi.doneGn false).fractional q1.half q2.half
    unfold wgMuP stopPart
    rw [Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro ⟨%b, Hg, Hs⟩
      icases (hgv b).1 $$ Hg with ⟨Hg1, Hg2⟩
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hs with #Hs
        isplitl [Hg1]
        · iexists false; iframe Hg1; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hs
        · iexists false; iframe Hg2; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hs
      · simp only [↓reduceIte]
        icases hdv.1 $$ Hs with ⟨Hs1, Hs2⟩
        isplitl [Hg1 Hs1]
        · iexists true; iframe Hg1; simp only [↓reduceIte]; iexact Hs1
        · iexists true; iframe Hg2; simp only [↓reduceIte]; iexact Hs2
    · iintro ⟨⟨%b1, Hg1, Hs1⟩, ⟨%b2, Hg2, Hs2⟩⟩
      ihave %Hag := ghostVar_agree γ.b _ _ _ _ $$ Hg1 Hg2
      cases Hag
      iexists b1
      isplitl [Hg1 Hg2]
      · iapply (hgv b1).2; iframe Hg1 Hg2
      cases b1
      · simp only [Bool.false_eq_true, ↓reduceIte] at *; iexact Hs1
      · simp only [↓reduceIte] at *; iapply hdv.2; iframe Hs1 Hs2

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : sync.Assumptions]

/-- **`s.wg.Add(1)`, by a reader that saw `open`** (a fraction of the flag at `true`), depositing
its caller's level-1 token as a pending add's: a pending receipt (revoke-open pass 2, 2026-11-06;
until then it deposited a whole thread token as a started goroutine's). The counter counts started
goroutines (level-0 tokens) and pending adds (level-1 tokens), hence the doubled bound. -/
theorem wp_goAttach_Add (s : Loc) (γ : GoNames) (q : Qp)
    (Hbound : 2 * threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗
        inv goAttachN (goAttachInv γ) ∗ ghostVar γ.b q true ∗ levelTok 1 }}
      (App (Val (srvWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); goPending γ ∗ ghostVar γ.b q true }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hb, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Add (srvWgAddr s) (W64 1) γ.wg goAttachWGN $$ [] [Hb Htok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro goAttach_mask
  iintro Hmask
  inext
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, %pq, %dq, Hbi, Hwgo, Hk, Hq, Hrun, Hp, ⟨%Hctr, %Hkd⟩, %Hdq, Hw⟩
  ihave %Hag := ghostVar_agree γ.b _ _ _ _ $$ Hb Hbi
  cases Hag
  have Hdq1 : dq = DFrac.own 1 := by
    rcases Hdq with h | ⟨-, -, -, h⟩
    · exact h
    · cases h
  subst Hdq1
  icases Hw with (⟨%Hf, -⟩ | ⟨-, Hw, Hwt⟩)
  · cases Hf
  icases levelToks_add_one_lt 1 pq $$ [Htok Hq] with ⟨%Hlt, Hq⟩
  · iframe
  icases (persistent_entails_left (levelToks_lt (GF := GF) 0 k)) $$ Hk with ⟨Hk, %Hklt⟩
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
  iframe Hw
  iintro Hw Hwgo
  imod Hmask with -
  imod ownTokAuth_S γ.pend pq $$ Hp with ⟨Hp, Hptok⟩
  imod Hclose $$ [Hbi Hwgo Hk Hq Hrun Hp Hw Hwt] with -
  · inext
    iunfold goAttachInv
    iexists true, ctr + W32 (sint.Z (W64 1)), k, pq + 1, DFrac.own 1
    rw [hn]
    iframe Hbi Hwgo Hk Hq Hrun Hp
    isplitr
    · ipureintro
      have : sint.Z (ctr + W32 (sint.Z (W64 1))) = sint.Z ctr + 1 := by
        rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
      omega
    isplitr
    · ipureintro; exact Or.inl rfl
    iright
    iframe Hw Hwt
    ipureintro; rfl
  imodintro
  iapply HΦ
  iunfold goPending
  iframe

/-- (revoke-open pass 2, 2026-11-06) **The `go` statement of a pending add** (at the fork,
`wp_fork_tok_upd`): the fresh thread token's level 0 is deposited as a started goroutine's (its
receipt minted), and the pending add's level-1 token comes back to the caller; the goroutine keeps
the fresh token's levels from 1. The counter does not move. -/
theorem goAttach_fork (γ : GoNames) :
    inv goAttachN (goAttachInv (GF := GF) γ) ∗ goPending γ ∗ threadTok ⊢
      |={⊤}=> levelTok 1 ∗ goRunning γ ∗ threadTokFrom 1 := by
  iintro ⟨#Hinv, Hpt, Htok⟩
  iinv Hinv with Hi Hclose
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, %pq, %dq, >Hbi, >Hwgo, >Hk, >Hq, >Hrun, >Hp, >%Hc, >%Hdq, Hw⟩
  iunfold goPending at Hpt
  icombine Hp Hpt gives %Hle
  have Hdq1 : dq = DFrac.own 1 := by
    rcases Hdq with h | ⟨-, -, h, -⟩
    · exact h
    · omega
  subst Hdq1
  obtain ⟨q', rfl⟩ : ∃ q', pq = q' + 1 := ⟨pq - 1, by omega⟩
  icases (levelToks_add 1 q' 1).1 $$ Hq with ⟨Hq, H1⟩
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨H0, Hfrom⟩
  icases levelToks_add_one_lt 0 k $$ [H0 Hk] with ⟨-, Hk⟩
  · iframe
  imod ownTokAuth_delete_S γ.pend q' $$ Hp Hpt with Hp
  imod ownTokAuth_S γ.run k $$ Hrun with ⟨Hrun, Hrtok⟩
  imod Hclose $$ [Hbi Hwgo Hk Hq Hrun Hp Hw] with -
  · inext
    iunfold goAttachInv
    iexists b, ctr, k + 1, q', DFrac.own 1
    iframe
    ipureintro
    exact ⟨⟨Hc.1, by omega⟩, Or.inl rfl⟩
  imodintro
  iframe H1 Hfrom
  iunfold goRunning
  iexact Hrtok

/-- **`s.wg.Done()`, with a receipt**: the goroutine gets a deposited level-0 token back (to exit
with; revoke-open, 2026-11-06: until then a whole thread token). -/
theorem wp_goAttach_Done (s : Loc) (γ : GoNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗
        inv goAttachN (goAttachInv γ) ∗ goRunning γ }}
      (App (Val (srvWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); levelTok 0 }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hrtok⟩ HΦ
  iapply sync.WaitGroup.wp_Done (srvWgAddr s) γ.wg goAttachWGN $$ [] [Hrtok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro goAttach_mask
  iintro Hmask
  inext
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, %pq, %dq, Hbi, Hwgo, Hk, Hq, Hrun, Hp, ⟨%Hctr, %Hkd⟩, %Hdq, Hw⟩
  iunfold goRunning at Hrtok
  icombine Hrun Hrtok gives %Hle
  have Hdq1 : dq = DFrac.own 1 := by
    rcases Hdq with h | ⟨-, h, -, -⟩
    · exact h
    · omega
  subst Hdq1
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  icases (levelToks_add 0 k' 1).1 $$ Hk with ⟨Hk, Htok⟩
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.run k' $$ Hrun Hrtok with Hrun
  imod Hclose $$ [Hbi Hwgo Hk Hq Hrun Hp Hw] with -
  · inext
    iunfold goAttachInv
    iexists b, ctr - W32 1, k', pq, DFrac.own 1
    rw [hn]
    iframe
    ipureintro
    exact ⟨⟨by omega, by omega⟩, Or.inl rfl⟩
  imodintro
  iapply HΦ
  iexact Htok

/-- (2026-11-05, R2b-3d stage 5c) **The shutdown's close of the protocol** (`run`'s deferred
`wgMu.Lock(); close(s.stopping); wgMu.Unlock()`, the ghost side): the writer holding the closer's
token and the lock's half of the flag learns the flag was open (the token would be in the invariant
otherwise), sets it closed, deposits the token and takes the wait group's "no waiters" out, with
the waiter's token (H2), for its `Wait`. -/
theorem goAttach_close (γ : GoNames) (b : Bool) :
    inv goAttachN (goAttachInv (GF := GF) γ) ∗ token γ.close ∗ ghostVar γ.b (1 : Qp).half b ⊢
      |={⊤}=> ⌜b = true⌝ ∗ ghostVar γ.b (1 : Qp).half false ∗ sync.ownWaitGroupWaiters γ.wg 0 ∗
        token γ.wt := by
  iintro ⟨#Hinv, Htok, Hb⟩
  iinv Hinv with Hi Hclose
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b', %ctr, %k, %pq, %dq, >Hbi, Hwgo, Hk, Hq, Hrun, Hp, Hc, >%Hdq, Hw⟩
  ihave %Hag := ghostVar_agree γ.b _ _ _ _ $$ Hb Hbi
  subst Hag
  icases Hw with (⟨>%Hf, >Htok', -⟩ | ⟨>%Ht, >Hw, >Hwt⟩)
  · iexfalso; iapply token_exclusive γ.close $$ Htok Htok'
  subst Ht
  have Hdq1 : dq = DFrac.own 1 := by
    rcases Hdq with h | ⟨-, -, -, h⟩
    · exact h
    · cases h
  subst Hdq1
  imod ghostVar_update_halves false γ.b _ _ $$ Hb Hbi with ⟨Hb, Hbi⟩
  imod Hclose $$ [Hbi Hwgo Hk Hq Hrun Hp Hc Htok] with -
  · inext
    iunfold goAttachInv
    iexists false, ctr, k, pq, DFrac.own 1
    iframe Hbi Hwgo Hk Hq Hrun Hp Hc
    isplitr
    · ipureintro; exact Or.inl rfl
    ileft
    iframe Htok
    isplitr
    · ipureintro; rfl
    ileft; ipureintro; rfl
  imodintro
  iframe Hb Hw Hwt
  ipureintro; rfl

/-- (R2b-3d stage 5c) **`s.wg.Wait()` at the shutdown**, with the wait group's "no waiters" and
the waiter's token (`goAttach_close`'s): it returns once every goroutine `GoAttach` started has
called `Done`, and (H2, 2026-11-05) gives `goWaited`. At the counter's `0`, the protocol is closed
(the waiter's token is not in the invariant), so no receipt is left: the authority is split, half
kept with the token, half returned. -/
theorem wp_goAttach_Wait (s : Loc) (γ : GoNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗
        inv goAttachN (goAttachInv γ) ∗ sync.ownWaitGroupWaiters γ.wg 0 ∗ token γ.wt }}
      (App (Val (srvWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); goWaited γ }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hw, Hwt⟩ HΦ
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑goAttachWGN) (fun _ _ => CoPset.mem_full) with Hmask
  imod sync.alloc_wait_token (srvWgAddr s) γ.wg goAttachWGN 0 (by decide) $$ Hwg Hw with ⟨-, Htok⟩
  imod Hmask with -
  imodintro
  iapply sync.WaitGroup.wp_Wait (srvWgAddr s) γ.wg goAttachWGN $$ [Htok] [HΦ Hwt]
  · iframe #; iframe
  have hmask : (↑goAttachN : CoPset) ⊆ ⊤ \ ↑goAttachWGN :=
    sync.wg_mask_ndot_ne nroot "srvGoAttach" "srvWaitGroup" (by decide)
  imod inv_acc (E := ⊤ \ ↑goAttachWGN) (N := goAttachN) hmask $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, %pq, %dq, Hbi, Hwgo, Hk, Hq, Hrun, Hp, ⟨%Hctr, %Hkd⟩, %Hdq, Hc⟩
  iexists ctr
  iframe Hwgo
  iintro %Hz Hwgo
  imod Hmask with -
  icases Hc with (⟨%Hbf, Hcl, (%Hd1 | Hwt')⟩ | ⟨-, -, Hwt'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive γ.wt $$ Hwt Hwt'
  · iexfalso; iapply token_exclusive γ.wt $$ Hwt Hwt'
  subst Hd1
  have hk0 : k = 0 ∧ pq = 0 := by
    have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
    omega
  obtain ⟨rfl, rfl⟩ := hk0
  icases (ownTokAuth_fractional (GF := GF) γ.run 0).fractional (1 : Qp).half (1 : Qp).half |>.1
    $$ [Hrun] with ⟨Hrun, Hwd⟩
  · rw [Qp.half_add_half]; iexact Hrun
  imod Hclose $$ [Hbi Hwgo Hk Hq Hrun Hp Hcl Hwt] with -
  · inext
    iunfold goAttachInv
    iexists b, ctr, 0, 0, DFrac.own (1 : Qp).half
    iframe Hbi Hwgo Hk Hq Hrun Hp
    isplitr
    · ipureintro; exact ⟨Hctr, Hkd⟩
    isplitr
    · ipureintro; exact Or.inr ⟨rfl, rfl, rfl, Hbf⟩
    ileft
    iframe Hcl
    isplitr
    · ipureintro; exact Hbf
    iright; iexact Hwt
  imodintro
  iintro -
  iapply HΦ
  iunfold goWaited
  iexact Hwd

end lemmas

end EtcdGrove
end Perennial
