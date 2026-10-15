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
goroutines' receipts, and the `stopping` channel's (its channel names and its closer's flag). -/
structure GoNames where
  b : GName
  close : GName
  wg : sync.WaitGroupNames
  run : GName
  ch : ChanNames
  chi : BroadcastInternalNames

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvWgAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"wg" s
abbrev srvWgMuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"wgMu" s
abbrev srvCtxAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"ctx" s
abbrev srvStoppingAddr' (s : Loc) : Loc := structFieldRef EtcdServer go!"stopping" s

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The wait group's namespace (`sync.isWaitGroup`). -/
def goAttachWGN : Namespace := nroot.@"srvWaitGroup"
/-- The counter's invariant's namespace (`goAttachInv`). -/
def goAttachN : Namespace := nroot.@"srvGoAttach"

theorem goAttach_mask : (↑goAttachWGN : CoPset) ⊆ ⊤ \ ↑goAttachN :=
  sync.wg_mask_ndot_ne nroot "srvWaitGroup" "srvGoAttach" (by decide)

theorem goAttachN_mask : (↑goAttachN : CoPset) ⊆ ⊤ \ ↑goAttachWGN :=
  sync.wg_mask_ndot_ne nroot "srvGoAttach" "srvWaitGroup" (by decide)

/-- The `stopping` channel's part of the lock's resource at fraction `q`: while open, a fraction
of the closer's flag; once closed, the flag discarded (persistent). -/
def stopPart (γ : GoNames) (b : Bool) (q : Qp) : IProp GF :=
  if b then dghostVar γ.chi.doneGn (DFrac.own q.half) false
  else dghostVar γ.chi.doneGn DFrac.discard true

/-- **`wgMu`'s resource** at fraction `q`: half the flag `open` (scaled) and the channel's part. -/
def wgMuP (γ : GoNames) (q : Qp) : IProp GF :=
  iprop(∃ b : Bool, ghostVar γ.b q.half b ∗ stopPart γ b q)

/-- **The counter's invariant**: the other half of `open`; the wait group's counter `ctr`, `k`
goroutines started (their receipts' authority) with their thread tokens deposited; while open,
no waiter; once closed, the closer's token (so `run`'s shutdown, holding it, knows it closes an
open channel). -/
def goAttachInv (γ : GoNames) : IProp GF :=
  iprop(∃ (b : Bool) (ctr : w32) (k : Nat), ghostVar γ.b (1 : Qp).half b ∗
    sync.ownWaitGroup γ.wg ctr ∗ threadToks k ∗ ownTokAuth γ.run k ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.nat ctr = k⌝ ∗
    (⌜b = false⌝ ∗ token γ.close ∨ ⌜b = true⌝ ∗ sync.ownWaitGroupWaiters γ.wg 0))

/-- **`GoAttach`'s protocol at `s`** (persistent): the `stopping` channel, the wait group, the
counter's invariant, `wgMu`'s write side, the context field (set by `start` before any goroutine,
read by the apply thread's alarm goroutine), the logger (`GoAttach` warns when stopped), and the
bound on live goroutines. -/
def srvGoAttachOk (s : Loc) (γ : GoNames) : IProp GF :=
  iprop(∃ (ch : Loc) (c : GoInterface), srvStoppingAddr' s ↦□ ch ∗
    isStopChanInternal ch γ.ch γ.chi iprop(True) ∗
    sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗ inv goAttachN (goAttachInv γ) ∗
    sync.isRWMutexGuard (srvWgMuAddr s) (wgMuP γ) ∗ srvCtxAddr s ↦□ c ∗
    (∃ l : Loc, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝) ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)

instance srvGoAttachOk_persistent (s : Loc) (γ : GoNames) :
    Persistent (srvGoAttachOk (GF := GF) s γ) := by
  unfold srvGoAttachOk; infer_instance

/-- **A reader slot of `s.wgMu`**, with the protocol. -/
def srvWgReader (s : Loc) : IProp GF :=
  iprop(∃ γ : GoNames, srvGoAttachOk s γ ∗ sync.ownRWMutex (srvWgMuAddr s) (wgMuP γ))

/-- **What a goroutine needs to `GoAttach`**: a reader slot of `wgMu` and its thread token. -/
def srvGoRes (s : Loc) : IProp GF := iprop(srvWgReader s ∗ threadTok)

/-- A started goroutine's receipt (its `Done` takes a deposited thread token back). -/
def goRunning (γ : GoNames) : IProp GF := ownToks γ.run 1

/-- `wgMu`'s resource is fractional (for `sync.init_RWMutex`). -/
instance wgMuP_fractional (γ : GoNames) : Fractional (wgMuP (GF := GF) γ) where
  fractional q1 q2 := by
    have hgv := fun (b : Bool) => (ghostVar_fractional (GF := GF) γ.b b).fractional q1.half q2.half
    have hdv := (dghostVar_fractional (GF := GF) γ.chi.doneGn false).fractional q1.half q2.half
    unfold wgMuP stopPart
    rw [qp_half_add]
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- **`s.wg.Add(1)`, by a reader that saw `open`** (a fraction of the flag at `true`), depositing
its thread token: a receipt. -/
theorem wp_goAttach_Add (s : Loc) (γ : GoNames) (q : Qp)
    (Hbound : threadBound GF ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗
        inv goAttachN (goAttachInv γ) ∗ ghostVar γ.b q true ∗ threadTok }}
      (App (Val (srvWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); goRunning γ ∗ ghostVar γ.b q true }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hb, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Add (srvWgAddr s) (W64 1) γ.wg goAttachWGN $$ [] [Hb Htok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro goAttach_mask
  iintro Hmask
  inext
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, Hbi, Hwgo, Hk, Hrun, ⟨%Hctr, %Hkd⟩, Hw⟩
  ihave %Hag := ghostVar_agree γ.b _ _ _ _ $$ Hb Hbi
  cases Hag
  icases Hw with (⟨%Hf, -⟩ | ⟨-, Hw⟩)
  · cases Hf
  icases threadToks_add_one_lt k $$ [Htok Hk] with ⟨%Hlt, Hk⟩
  · iframe
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
  imod ownTokAuth_S γ.run k $$ Hrun with ⟨Hrun, Hrtok⟩
  imod Hclose $$ [Hbi Hwgo Hk Hrun Hw] with -
  · inext
    iunfold goAttachInv
    iexists true, ctr + W32 (sint.Z (W64 1)), k + 1
    rw [hn]
    iframe
    isplitr
    · ipureintro
      have : sint.Z (ctr + W32 (sint.Z (W64 1))) = sint.Z ctr + 1 := by
        rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
      omega
    iright
    iframe Hw
    ipureintro; rfl
  imodintro
  iapply HΦ
  iunfold goRunning
  iframe

/-- **`s.wg.Done()`, with a receipt**: the goroutine gets a deposited thread token back (to exit
with). -/
theorem wp_goAttach_Done (s : Loc) (γ : GoNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗
        inv goAttachN (goAttachInv γ) ∗ goRunning γ }}
      (App (Val (srvWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hrtok⟩ HΦ
  iapply sync.WaitGroup.wp_Done (srvWgAddr s) γ.wg goAttachWGN $$ [] [Hrtok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro goAttach_mask
  iintro Hmask
  inext
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, Hbi, Hwgo, Hk, Hrun, ⟨%Hctr, %Hkd⟩, Hw⟩
  iunfold goRunning at Hrtok
  icombine Hrun Hrtok gives %Hle
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  icases (threadToks_add k' 1).1 $$ Hk with ⟨Hk, Htok⟩
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.run k' $$ Hrun Hrtok with Hrun
  imod Hclose $$ [Hbi Hwgo Hk Hrun Hw] with -
  · inext
    iunfold goAttachInv
    iexists b, ctr - W32 1, k'
    rw [hn]
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  iexact Htok

/-- **`s.wg.Wait()`** by the closer, with the "no waiters" it took out at the close: it returns
(once every started goroutine is `Done`; nothing is claimed). -/
theorem wp_goAttach_Wait (s : Loc) (γ : GoNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (srvWgAddr s) γ.wg goAttachWGN ∗
        inv goAttachN (goAttachInv γ) ∗ sync.ownWaitGroupWaiters γ.wg 0 }}
      (App (Val (srvWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hw0⟩ HΦ
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑goAttachWGN) (fun _ _ => CoPset.mem_full) with Hmask
  imod sync.alloc_wait_token (srvWgAddr s) γ.wg goAttachWGN 0 (by decide) $$ Hwg Hw0
    with ⟨Hw1, Htok⟩
  imod Hmask with -
  imodintro
  iapply sync.WaitGroup.wp_Wait (srvWgAddr s) γ.wg goAttachWGN $$ [Htok] [HΦ]
  · iframe #; iframe
  iinv Hinv with Hi Hclose <;> try exact goAttachN_mask
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, Hbi, Hwgo, Hk, Hrun, Hp, Hw⟩
  iexists ctr
  iframe Hwgo
  iintro %Hz Hwgo
  imod Hmask with -
  imod Hclose $$ [Hbi Hwgo Hk Hrun Hp Hw] with -
  · inext
    iunfold goAttachInv
    iexists b, ctr, k
    iframe
  imodintro
  iintro -
  iapply HΦ
  itrivial

/-- **`run`'s shutdown, the ghost step at `close(s.stopping)`**: with the closer's token and the
write lock's whole resource at `open` (the closer's flag of `stopping` already spent on the
close, which gave the flag discarded at `true`), the flag `open` becomes `false`, the closer's
token goes into the invariant and the "no waiters" comes out (for `Wait`); the lock's resource is
the closed one. -/
theorem goAttach_shutdown (γ : GoNames) :
    ⊢ inv goAttachN (goAttachInv (GF := GF) γ) -∗ token γ.close -∗ ghostVar γ.b (1 : Qp).half true -∗
      dghostVar γ.chi.doneGn DFrac.discard true ={⊤}=∗
      wgMuP γ 1 ∗ sync.ownWaitGroupWaiters γ.wg 0 := by
  iintro #Hinv Htok Hb #Hd
  iinv Hinv with Hi Hclose
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b, %ctr, %k, >Hbi, Hwgo, Hk, Hrun, Hp, Hw⟩
  ihave %Hag := ghostVar_agree γ.b _ _ _ _ $$ Hb Hbi
  cases Hag
  imod Hw with (⟨%Hf, -⟩ | ⟨-, Hw⟩)
  · cases Hf
  imod ghostVar_update_halves false γ.b true true $$ Hb Hbi with ⟨Hb, Hbi⟩
  imod Hclose $$ [Hbi Hwgo Hk Hrun Hp Htok] with -
  · inext
    iunfold goAttachInv
    iexists false, ctr, k
    iframe
    ileft
    iframe Htok
    ipureintro; rfl
  imodintro
  iframe Hw
  iunfold wgMuP
  iexists false
  rw [show (1 : Qp).half = (1 : Qp).half from rfl]
  iframe Hb
  iunfold stopPart
  simp only [Bool.false_eq_true, ↓reduceIte]
  iexact Hd

/-- The closer's token and a closed `open` are exclusive: the closer knows `stopping` is open
(the lock's resource at `false` cannot be what it locked). -/
theorem goAttach_closer_open (γ : GoNames) (b : Bool) (q : Qp) :
    ⊢ inv goAttachN (goAttachInv (GF := GF) γ) -∗ token γ.close -∗ ghostVar γ.b q b ={⊤}=∗
      ⌜b = true⌝ ∗ token γ.close ∗ ghostVar γ.b q b := by
  iintro #Hinv Htok Hb
  iinv Hinv with Hi Hclose
  iunfold goAttachInv at Hi
  icases Hi with ⟨%b', %ctr, %k, >Hbi, Hwgo, Hk, Hrun, Hp, Hw⟩
  ihave %Hag := ghostVar_agree γ.b _ _ _ _ $$ Hb Hbi
  cases Hag
  imod Hw with (⟨%Hf, Htok'⟩ | ⟨%Ht, Hw⟩)
  · iexfalso
    iapply token_exclusive $$ Htok Htok'
  imod Hclose $$ [Hbi Hwgo Hk Hrun Hp Hw] with -
  · inext
    iunfold goAttachInv
    iexists b, ctr, k
    iframe
    iright
    iframe Hw
    ipureintro; exact Ht
  imodintro
  iframe Htok Hb
  ipureintro; exact Ht

end lemmas

end EtcdGrove
end Perennial
