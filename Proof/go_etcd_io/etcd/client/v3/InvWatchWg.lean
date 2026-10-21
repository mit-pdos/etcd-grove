/-
**The wait group of a gRPC watch stream's substreams** (`watchGRPCStream.wg`, `client/v3/watch.go`;
the watch slice's unit W-C, 2026-10-15). Lean-first, no Rocq counterpart.

`run` is the only thread that calls `Add` and `Wait` on it (`Add(1)` before each `go
w.serveSubstream(...)`, `Wait()` once, in its deferred teardown); each `serveSubstream` calls `Done`
once, at its end. `run` adds once per `Watch`, without a bound, so the join idiom
(`sync.join.ownAdder`, whose counter of `Add`s since the last `Wait` must stay below `2^31 - 1`)
does not fit. The counter is instead backed by **thread tokens** (Perennial's `Threads.lean`), as
the cache's (`cacheWgInv`): the invariant `wgsWgInv` holds one thread token per goroutine added
and not yet `Done`, so `k` goroutines running give `k < threadBound GF`, and the counter stays
below `2^31` when `threadBound GF ≤ 2^31` (a premise, `wgsWgAdder`'s).

* `run` holds `wgsWgAdder wg` (and its own thread token): its `Add(1)` deposits its thread token
  and returns a running token (`wgsWgDone wg`), which goes to the new goroutine; `run` receives a
  fresh thread token at the `go` statement (`wp_fork_tok_self`), so it keeps one throughout.
* `serveSubstream` holds `wgsWgDone wg`: its `Done()` gives back a deposited thread token, the one
  it exits with (its postcondition `threadTok`).
* `run`'s `Wait()` needs only `wgsWgAdder wg` (it takes nothing out).

No waiter is ever registered while `run` may still `Add`: `run` keeps the waiters' authority at
`0` (`ownWaitGroupWaiters γ 0`, `wgsWgAdder`) until its `Wait`, which consumes it.
-/
module

public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode

/-- The ghost names of a stream's wait group: Perennial's and the running tokens'. -/
structure WgsWgNames where
  γwg : sync.WaitGroupNames
  γwr : GName

/-- The namespace of the stream's `sync.WaitGroup` (`isWaitGroup`). -/
abbrev wgsWgWN : Namespace := nroot.@"wgsWaitGroup"

/-- The namespace of the counter invariant `wgsWgInv`. -/
abbrev wgsWgCN : Namespace := nroot.@"wgsWgCounter"

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

/-- **The counter invariant**: the counter is `k`, the number of running tokens (`γwr`) given
out, and a thread token is deposited for each. -/
def wgsWgInv (γ : WgsWgNames) : IProp GF :=
  iprop(∃ (ctr : w32) (k : Nat), sync.ownWaitGroup γ.γwg ctr ∗ ownTokAuth γ.γwr k ∗ threadToks k ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.nat ctr = k⌝)

/-- The wait group `wg` with the names `γ` (persistent). -/
def isWgsWg (wg : Loc) (γ : WgsWgNames) : IProp GF :=
  iprop(sync.isWaitGroup wg γ.γwg wgsWgWN ∗ inv wgsWgCN (wgsWgInv γ))

instance isWgsWg_persistent (wg : Loc) (γ : WgsWgNames) : Persistent (isWgsWg (GF := GF) wg γ) := by
  unfold isWgsWg; infer_instance

/-- **The right to call `Done`** on `wg` once (a goroutine added and not yet done): its running
token; the `Done` returns a thread token. -/
def wgsWgDone (wg : Loc) : IProp GF :=
  iprop(∃ γ : WgsWgNames, isWgsWg wg γ ∗ ownToks γ.γwr 1)

/-- **The right to `Add(1)` to and `Wait` on** `wg` (no waiter registered), under the thread
bound `threadBound GF ≤ 2^31`. -/
def wgsWgAdder (wg : Loc) : IProp GF :=
  iprop(∃ γ : WgsWgNames, isWgsWg wg γ ∗ sync.ownWaitGroupWaiters γ.γwg 0 ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

theorem wgsWg_mask : (↑wgsWgWN : CoPset) ⊆ ⊤ \ ↑wgsWgCN :=
  sync.wg_mask_ndot_ne nroot "wgsWaitGroup" "wgsWgCounter" (by decide)

/-- **A fresh wait group** (the zero value, `newWatcherGRPCStream`'s struct literal), under the
thread bound. -/
theorem wgsWg_init (wg : Loc) (Hb : threadBound GF ≤ 2 ^ 31) :
    typedPointsto (GF := GF) wg (zero_val sync.WaitGroup) (DFrac.own 1) ⊢ |={⊤}=> wgsWgAdder wg := by
  iintro Hwg
  imod sync.init_WaitGroup wgsWgWN wg $$ Hwg with ⟨%γwg, #Hiswg, Hctr, Hwait⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γwr, Hauth⟩
  let γ : WgsWgNames := ⟨γwg, γwr⟩
  imod inv_alloc wgsWgCN ⊤ (wgsWgInv (GF := GF) γ) $$ [Hctr Hauth] with #Hinv
  · inext
    unfold wgsWgInv
    iexists (W32 0), 0
    simp only [γ]
    iframe
    isplitr
    · iapply threadToks_zero
    ipureintro
    exact ⟨by decide, by decide⟩
  imodintro
  unfold wgsWgAdder isWgsWg
  iexists γ
  simp only [γ]
  iframe #
  iframe
  ipureintro; exact Hb

/-- **`wg.Add(1)`** by `run`, with its thread token, which is deposited: a running token for the
goroutine about to start. -/
theorem wp_wgsWg_Add (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wgsWgAdder wg ∗ threadTok }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); wgsWgAdder wg ∗ wgsWgDone wg }} := by
  iintro %Φ ⟨#Hsync, Had, Htok⟩ HΦ
  unfold wgsWgAdder
  icases Had with ⟨%γ, #Hwgs, Hwait, %Hb⟩
  unfold isWgsWg
  icases Hwgs with ⟨#Hwg, #Hinv⟩
  iapply sync.WaitGroup.wp_Add wg (W64 1) γ.γwg wgsWgWN $$ [] [Hwait Htok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro wgsWg_mask
  iintro Hmask
  inext
  iunfold wgsWgInv at Hi
  icases Hi with ⟨%ctr, %k, Hwgo, Hrun, Hk, %Hctr⟩
  icases threadToks_add_one_lt k $$ [Htok Hk] with ⟨%Hlt, Hk⟩
  · iframe
  obtain ⟨Hc0, Hck⟩ := Hctr
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hc0
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hn : sint.nat (ctr + W32 (sint.Z (W64 1))) = sint.nat ctr + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  have hz : sint.Z (ctr + W32 (sint.Z (W64 1))) = sint.Z ctr + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwait
  iintro Hwait Hwgo
  imod Hmask with -
  imod ownTokAuth_S γ.γwr k $$ Hrun with ⟨Hrun, Hrtok⟩
  imod Hclose $$ [Hwgo Hrun Hk] with -
  · inext
    unfold wgsWgInv
    iexists ctr + W32 (sint.Z (W64 1)), k + 1
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  unfold wgsWgDone isWgsWg
  isplitl [Hwait]
  · iexists γ
    iframe #
    iframe
    ipureintro; exact Hb
  iexists γ
  iframe #
  iframe

/-- **`wg.Done()`** by a goroutine with its running token: it gets a deposited thread token back
(to exit with). -/
theorem wp_wgsWg_Done (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wgsWgDone wg }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hsync, Hd⟩ HΦ
  unfold wgsWgDone
  icases Hd with ⟨%γ, #Hwgs, Hrtok⟩
  unfold isWgsWg
  icases Hwgs with ⟨#Hwg, #Hinv⟩
  iapply sync.WaitGroup.wp_Done wg γ.γwg wgsWgWN $$ [] [Hrtok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro wgsWg_mask
  iintro Hmask
  inext
  iunfold wgsWgInv at Hi
  icases Hi with ⟨%ctr, %k, Hwgo, Hrun, Hk, %Hctr⟩
  obtain ⟨Hc0, Hck⟩ := Hctr
  icombine Hrun Hrtok gives %Hle
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hc0
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
  imod ownTokAuth_delete_S γ.γwr k' $$ Hrun Hrtok with Hrun
  imod Hclose $$ [Hwgo Hrun Hk] with -
  · inext
    unfold wgsWgInv
    iexists ctr - W32 1, k'
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  iexact Htok

/-- **`wg.Wait()`** by `run` (once, at its end): the adder's right is spent (a waiter is now
registered). -/
theorem wp_wgsWg_Wait (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wgsWgAdder wg }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, Had⟩ HΦ
  unfold wgsWgAdder
  icases Had with ⟨%γ, #Hwgs, Hwait, -⟩
  unfold isWgsWg
  icases Hwgs with ⟨#Hwg, #Hinv⟩
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑wgsWgWN) (fun _ _ => CoPset.mem_full) with Hcl
  imod sync.alloc_wait_token wg γ.γwg wgsWgWN 0 (by decide) $$ Hwg Hwait with ⟨-, Hwt⟩
  imod Hcl with -
  imodintro
  iapply sync.WaitGroup.wp_Wait wg γ.γwg wgsWgWN $$ [Hwt] [HΦ]
  · iframe #
    iframe
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold wgsWgInv at Hi
  icases Hi with ⟨%ctr, %k, Hwgo, Hrun, Hk, %Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hrun Hk] with -
  · inext
    unfold wgsWgInv
    iexists ctr, k
    iframe
    ipureintro; exact Hctr
  imodintro
  iintro -
  iapply HΦ
  itrivial

end lemmas

end client
end EtcdGrove
end Perennial
