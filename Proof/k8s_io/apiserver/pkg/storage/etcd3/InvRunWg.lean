/-
Lean-first (no Rocq counterpart).

# `watchChan.run`'s wait group (`resultChanWG`): a join whose goroutines may `Add` (k8s 7f-5b)

`run` adds at most three goroutines (`startWatching`, and the serial processing goroutine or the
concurrent branch's scheduler and collector) and then `Wait`s; the concurrent branch's scheduler,
itself one of them, runs `wg.Add(1); go …` once per event, without a bound, **while `run` may be in
`Wait()`**, at a count of at least `1` (its own slot, released by its deferred `Done` after its last
`Add`). Go allows it (`Add`'s "called concurrently with Wait" panic needs the count at `0` before the
add), and so does Perennial's raw `sync.WaitGroup.Add.spec` (its `oldc ≠ 0` disjunct needs no waiter
state); Perennial's thread-token joins (`sync.tokJoin`, `sync.tokJoinL`) do not: only the exclusive
`ownAdder` may `Add`, and `Wait` consumes it (`notes/perennial-changes.md`, "The thread-token
`WaitGroup` joins have no `Add` by a member", the general fix proposed to Perennial separately).
This is a local variant of `sync.tokJoinL` (whose proofs these follow), over the raw specs:

* **Top-level slots**, added by the adder (`rwgAdder`, as `tokJoinL.ownAdder`), at most `K` of them,
  each with a `Done` proposition (`ownAprop`). They hold no thread token: their goroutines run with
  the fresh token of their `go` statement (`startWatching.spec` takes a whole `threadTok`).
* **Member slots**, added by the holder of a top-level slot (`wp_Add_member`: its slot keeps the
  count positive), with the `Done` proposition `True`, backed by thread tokens as `tokJoinL`'s at
  pending level `1`: the adder's `levelTok 1` while pending (`rwgPending`), the forked goroutine's
  level `0` once started (`rwgMemDone`, `wp_fork_member`).

The counter is `added - done + d + q` (top-level slots not done, started and pending members), below
`K + 2 (T - 1)`, so below `2^31` when `K + 2 T ≤ 2^31 + 1` (`isRunWg`'s premise).
-/
module

public import Perennial.Proof.sync.WaitGroupTokJoinL

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s
namespace rwg

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode
open _root_.Perennial.sync

structure RwgNames where
  wgGn : WaitGroupNames
  /-- The propositions of the top-level `Done`s (`ownAprop`). -/
  apGn : GName
  /-- The top-level goroutines added and not done. -/
  ndGn : GName
  /-- The started members, whose slot holds their level-`0` token. -/
  depGn : GName
  /-- The members added and not yet started, whose slot holds a pending level-`1` token. -/
  pendGn : GName

section idiom
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The invariant: the counter is the top-level slots not done (`added - done`, at most `K` added)
plus the started (`d`, level-`0` tokens) and pending (`q`, level-`1` tokens) members; the
propositions of the top-level `Done`s so far. -/
def rwgInv (γ : RwgNames) (K : Nat) : IProp GF :=
  iprop(∃ (ctr : w32) (added done d q : Nat) (Pdone : IProp GF),
    ownWaitGroup γ.wgGn ctr ∗
    ownTokAuthDfrac γ.ndGn (DFrac.own (1 : Qp).half) added ∗ ownToks γ.ndGn done ∗
    ownApropFrag γ.apGn Pdone done ∗ Pdone ∗
    levelToks 0 d ∗ ownTokAuth γ.depGn d ∗ levelToks 1 q ∗ ownTokAuth γ.pendGn q ∗
    ⌜sint.Z ctr = (added : Int) - done + d + q ∧ done ≤ added ∧ added ≤ K⌝)

/-- The wait group, its invariant and the counter's bound (persistent). -/
def isRunWg (N : Namespace) (K : Nat) (wg : Loc) (γ : RwgNames) : IProp GF :=
  iprop(isWaitGroup wg γ.wgGn (N.@"wg") ∗ inv (N.@"inv") (rwgInv (GF := GF) γ K) ∗
    ⌜K + 2 * threadBound GF ≤ 2 ^ 31 + 1⌝)

instance isRunWg_persistent (N : Namespace) (K : Nat) (wg : Loc) (γ : RwgNames) :
    Persistent (isRunWg (GF := GF) N K wg γ) := by
  unfold isRunWg; infer_instance

/-- **Permission to `Add` a top-level goroutine or `Wait`** (`n` added since the start). -/
def rwgAdder (N : Namespace) (K : Nat) (wg : Loc) (n : Nat) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : RwgNames) (P' : IProp GF),
    ownWaitGroupWaiters γ.wgGn 0 ∗ ownApropAuth γ.apGn P' n ∗
    ownTokAuthDfrac γ.ndGn (DFrac.own (1 : Qp).half) n ∗ (P' -∗ P) ∗ isRunWg N K wg γ)

/-- **A top-level slot**: permission to call `Done` with `P`, or to `Add` a member. -/
def rwgDone (N : Namespace) (K : Nat) (wg : Loc) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : RwgNames, ownAprop γ.apGn P ∗ ownToks γ.ndGn 1 ∗ isRunWg N K wg γ)

/-- **A member added and not yet started**, its slot holding the adder's level-`1` token. -/
def rwgPending (N : Namespace) (K : Nat) (wg : Loc) : IProp GF :=
  iprop(∃ γ : RwgNames, ownToks γ.pendGn 1 ∗ isRunWg N K wg γ)

/-- **A started member**: permission to call `Done`, its slot holding its level-`0` token. -/
def rwgMemDone (N : Namespace) (K : Nat) (wg : Loc) : IProp GF :=
  iprop(∃ γ : RwgNames, ownToks γ.depGn 1 ∗ isRunWg N K wg γ)

theorem init (N : Namespace) (K : Nat) (wg : Loc) (γwg : WaitGroupNames) (E : CoPset)
    (Hb : K + 2 * threadBound GF ≤ 2 ^ 31 + 1) :
    isWaitGroup (GF := GF) wg γwg (N.@"wg") ∗ ownWaitGroup γwg (W32 0) ∗
      ownWaitGroupWaiters γwg 0 ⊢ |={E}=> rwgAdder N K wg 0 iprop(True) := by
  iintro ⟨#His, Hctr, Hwait⟩
  imod ownApropAuth_alloc (GF := GF) with ⟨%γap, Hap⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γnd, Hnd⟩
  icases (join.ownTokAuth_halves γnd 0).1 $$ Hnd with ⟨Hnd1, Hnd2⟩
  imod ownToks_0 (GF := GF) γnd with Hnd0
  ihave Hfrag := ownApropFrag_0 (GF := GF) γap
  imod ownTokAuth_alloc (GF := GF) with ⟨%γdep, Hdep⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γpend, Hpend⟩
  let γ : RwgNames := ⟨γwg, γap, γnd, γdep, γpend⟩
  imod inv_alloc (N.@"inv") E (rwgInv (GF := GF) γ K) $$ [Hctr Hnd1 Hnd0 Hfrag Hdep Hpend]
    with #Hinv
  · inext
    unfold rwgInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    simp only [γ]
    iframe
    isplitr
    · iexact Hfrag
    isplitr
    · iapply levelToks_zero
    isplitr
    · iapply levelToks_zero
    ipureintro
    exact ⟨by decide, by decide, by omega⟩
  imodintro
  unfold rwgAdder
  iexists γ, iprop(True)
  simp only [γ]
  iframe Hwait Hap Hnd2
  isplitr
  · iintro _; itrivial
  unfold isRunWg
  iframe #
  ipureintro; exact Hb

theorem rwgAdder_wand (P' : IProp GF) (N : Namespace) (K : Nat) (wg : Loc) (n : Nat)
    (P : IProp GF) :
    ⊢ (P -∗ P') -∗ rwgAdder N K wg n P -∗ rwgAdder N K wg n P' := by
  iintro Hw Ha
  unfold rwgAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  iexists γ, P0
  iframe Hwait Hap Hadded Hj
  iintro H
  iapply Hw
  iapply Himp $$ H

/-- **Starting a pending member**: a level-`0` token (the fresh token's, at the `go` statement)
takes the place of the pending level-`1` token, which comes back. -/
theorem start (N : Namespace) (K : Nat) (wg : Loc) (E : CoPset) (HE : ↑(N.@"inv") ⊆ E) :
    rwgPending N K wg ∗ levelTok 0 ⊢ |={E}=> rwgMemDone (GF := GF) N K wg ∗ levelTok 1 := by
  iintro ⟨Hpd, Htok0⟩
  unfold rwgPending
  icases Hpd with ⟨%γ, Hpend_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isRunWg at Hj2
  icases Hj2 with ⟨-, #Hinv, -⟩
  imod inv_acc (E := E) HE $$ Hinv with ⟨Hi, Hclose⟩
  iunfold rwgInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded, Hdone_toks, Hdone_ap,
    HPdone, >Hd0, >Hdep, >Hqp, >Hpend, >%Hctr⟩
  icombine Hpend Hpend_tok gives %Hq1
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  icases (levelToks_add 1 q' 1).1 $$ Hqp with ⟨Hqp, Htokp⟩
  imod ownTokAuth_delete_S γ.pendGn q' $$ Hpend Hpend_tok with Hpend
  imod ownTokAuth_S γ.depGn d $$ Hdep with ⟨Hdep, Hdep_tok⟩
  ihave Hd0 := (levelToks_add 0 d 1).2 $$ [Hd0 Htok0]
  · iframe
  imod Hclose $$ [Hwgo Hadded Hdone_toks Hdone_ap HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold rwgInv
    iexists ctr, added, done, d + 1, q', Pdone
    iframe
    ipureintro
    obtain ⟨h0, h1, h2⟩ := Hctr
    refine ⟨by push_cast at h0 ⊢; omega, h1, h2⟩
  imodintro
  iframe Htokp
  unfold rwgMemDone
  iexists γ
  iframe Hdep_tok Hj

/-- **The `go` statement of a pending member**: the fresh thread token's level `0` goes into the
member's slot, the pending level-`1` token back to the forking thread; the member runs with the
right to call `Done` and the fresh token's levels from `1`, and exits with a whole thread token. -/
theorem wp_fork_member (N : Namespace) (K : Nat) (wg : Loc) (s : Stuckness)
    (E : CoPset) (HE : ↑(N.@"inv") ⊆ E) (e : Expr) (Φ : val → IProp GF) :
    ⊢ rwgPending N K wg -∗
      ▷ (rwgMemDone N K wg -∗ threadTokFrom 1 -∗
          WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) -∗
      ▷ (levelTok 1 -∗ Φ #()) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iintro Hpd He HΦ
  iapply wp_fork_tok_upd
  inext
  iintro Htok _
  icases threadTok_level0.1 $$ Htok with ⟨Htok0, Hrest⟩
  imod start N K wg E HE $$ [Hpd Htok0] with ⟨Hd, Htokp⟩
  · iframe
  imodintro
  isplitl [He Hd Hrest]
  · iapply He $$ Hd Hrest
  · iapply HΦ $$ Htokp

/-- **`Add(1)` of a top-level goroutine** (the adder, at most `K` of them): the slot's right to
call `Done` with a chosen `P'`. -/
theorem wp_Add_top
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (P' : IProp GF) (N : Namespace) (K : Nat) (wg : Loc) (n : Nat) (P : IProp GF)
    (hn : n < K) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rwgAdder N K wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); rwgAdder N K wg (n + 1) iprop(P ∗ P') ∗ rwgDone N K wg P' }} := by
  wp_start_folded as Had
  unfold rwgAdder
  icases Had with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isRunWg at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, %Hb⟩
  wp_apply_core wp_Add wg (W64 1) γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold rwgInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, >Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, >Hd0, >Hdep, >Hqp, >Hpend, >%Hctr⟩
  icases persistent_entails_left (levelToks_lt 1 q) $$ Hqp with ⟨Hqp, %Hqlt⟩
  icases persistent_entails_left (levelToks_lt 0 d) $$ Hd0 with ⟨Hd0, %Hdlt⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  icombine Hadded Hadded_inv gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  have hctr_lt : sint.Z ctr + 1 < 2 ^ 31 := by omega
  have hz : sint.Z (ctr + W32 1) = sint.Z ctr + 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwait
  iintro Hwait Hwgo
  imod Hmask with -
  imod ownApropAuth_add P' γ.apGn P0 n $$ Hap with ⟨Hap, Hdone_ap'⟩
  ihave Hadded := (join.ownTokAuth_halves γ.ndGn n).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.ndGn _ $$ Hadded with ⟨Hadded, Hnd_tok⟩
  icases (join.ownTokAuth_halves γ.ndGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold rwgInv
    iexists ctr + W32 (sint.Z (W64 1)), n + 1, done, d, q, Pdone
    iframe
    ipureintro
    rw [h2, hz]
    refine ⟨by push_cast; omega, by omega, by omega⟩
  imodintro
  iapply HΦ
  isplitl [Hwait Hap Hadded Himp]
  · iexists γ, iprop(P0 ∗ P')
    iframe Hwait Hap Hadded Hj
    iintro ⟨H1, H2⟩
    iframe H2
    iapply Himp $$ H1
  unfold rwgDone
  iexists γ
  iframe Hdone_ap' Hnd_tok Hj

/-- **`Add(1)` of a member, by a top-level goroutine** (at any time, during a `Wait` too: its own
slot keeps the count positive, `Add.spec`'s first disjunct), with a level-`1` token, which the new
slot holds as pending until the `go` statement (`wp_fork_member`). -/
theorem wp_Add_member
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (N : Namespace) (K : Nat) (wg : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rwgDone N K wg P ∗ levelTok 1 }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); rwgDone N K wg P ∗ rwgPending N K wg }} := by
  wp_start_folded as ⟨Hd, Htok⟩
  unfold rwgDone
  icases Hd with ⟨%γ, Hap, Hnd_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isRunWg at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, %Hb⟩
  wp_apply_core wp_Add wg (W64 1) γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold rwgInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, >Hadded_inv, >Hdone_toks, Hdone_ap,
    HPdone, >Hd0, >Hdep, >Hqp, >Hpend, >%Hctr⟩
  icases levelToks_add_one_lt 1 q $$ [Htok Hqp] with ⟨%Hqlt, Hqp⟩
  · iframe
  icases persistent_entails_left (levelToks_lt 0 d) $$ Hd0 with ⟨Hd0, %Hdlt⟩
  icombine Hnd_tok Hdone_toks as Hdone_toks
  icombine Hadded_inv Hdone_toks gives %Hle
  icases (ownToks_add done 1 γ.ndGn).1 $$ Hdone_toks with ⟨Hnd_tok, Hdone_toks⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  have hpos : 1 ≤ sint.Z ctr := by push_cast at Hle; omega
  have hctr_lt : sint.Z ctr + 1 < 2 ^ 31 := by omega
  have hne : ctr ≠ W32 0 := by
    intro h; subst h; simp only [show sint.Z (W32 0) = 0 from rfl] at hpos; omega
  have hz : sint.Z (ctr + W32 1) = sint.Z ctr + 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  ileft
  isplitr
  · ipureintro; exact hne
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_S γ.pendGn q $$ Hpend with ⟨Hpend, Hpend_tok⟩
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold rwgInv
    iexists ctr + W32 (sint.Z (W64 1)), added, done, d, q + 1, Pdone
    iframe
    ipureintro
    rw [h2, hz]
    refine ⟨by push_cast; omega, Hc1, Hc2⟩
  imodintro
  iapply HΦ
  isplitl [Hap Hnd_tok]
  · iexists γ
    iframe Hap Hnd_tok Hj
  unfold rwgPending
  iexists γ
  iframe Hpend_tok Hj

/-- **`Done()` of a top-level goroutine**: `P` passed to the `Wait`. -/
theorem wp_Done_top
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (N : Namespace) (K : Nat) (wg : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rwgDone N K wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨Hd, HP⟩
  unfold rwgDone
  icases Hd with ⟨%γ, Hap, Hnd_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isRunWg at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, -⟩
  wp_apply_core wp_Done wg γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  iunfold rwgInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hd0, Hdep, Hqp, Hpend, %Hctr⟩
  icombine Hnd_tok Hdone_toks as Hdone_toks
  icombine Hadded_inv Hdone_toks gives %Hle
  icombine Hap Hdone_ap as Hdone_ap
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by
    have : 1 ≤ sint.Z ctr := by push_cast at Hle; omega
    word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; push_cast at Hle; constructor <;> word
  iintro Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HP HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold rwgInv
    iexists ctr - W32 1, added, 1 + done, d, q, iprop(P ∗ Pdone)
    iframe Hwgo Hadded_inv Hdone_ap Hd0 Hdep Hqp Hpend
    rw [Nat.add_comm 1 done]
    iframe Hdone_toks
    isplitl [HP HPdone]
    · iframe
    ipureintro
    rw [hz]
    push_cast at Hle
    refine ⟨by push_cast; omega, by omega, Hc2⟩
  imodintro
  iapply HΦ
  itrivial

/-- **`Done()` of a started member**: the slot's level-`0` token back, a whole thread token with
the member's levels from `1` (`threadTok_level0`). -/
theorem wp_Done_member
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (N : Namespace) (K : Nat) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rwgMemDone N K wg ∗ threadTokFrom 1 }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  wp_start_folded as ⟨Hd, Hrest⟩
  unfold rwgMemDone
  icases Hd with ⟨%γ, Hdep_tok, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isRunWg at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, -⟩
  wp_apply_core wp_Done wg γ.wgGn (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  iunfold rwgInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hd0, Hdep, Hqp, Hpend, %Hctr⟩
  icombine Hdep Hdep_tok gives %Hd1
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  icases (levelToks_add 0 d' 1).1 $$ Hd0 with ⟨Hd0, Htok⟩
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by
    have : 1 ≤ sint.Z ctr := by push_cast at Hc0; omega
    word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; push_cast at Hc0; constructor <;> word
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.depGn d' $$ Hdep Hdep_tok with Hdep
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold rwgInv
    iexists ctr - W32 1, added, done, d', q, Pdone
    iframe
    ipureintro
    rw [hz]
    refine ⟨by push_cast at Hc0 ⊢; omega, Hc1, Hc2⟩
  imodintro
  iapply HΦ
  iapply threadTok_level0.2
  iframe

/-- **`Wait()`**: the propositions of every top-level `Done` (the count `0`: every slot done), and
a fresh adder. -/
theorem wp_Wait
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (N : Namespace) (K : Nat) (wg : Loc) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rwgAdder N K wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ rwgAdder N K wg 0 iprop(True) }} := by
  wp_start_folded as Ha
  iapply wp_fupd
  unfold rwgAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isRunWg at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv, -⟩
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(N.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wgGn (N.@"wg") 0 (by decide) $$ Hwg Hwait with ⟨Hwaiter, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core wp_Wait wg γ.wgGn (N.@"wg") $$ [Htok] [-]
  · iframe #; iframe
  imod inv_acc (E := ⊤ \ ↑(N.@"wg")) (wg_mask_ndot_ne N "inv" "wg" (by decide)) $$ Hinv
    with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold rwgInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %d, %q, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hd0, Hdep, Hqp, Hpend, %Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %Hctr_zero Hwgo
  have hctr : ctr = W32 0 := by
    apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using Hctr_zero
  subst hctr
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  simp only [show sint.Z (W32 0) = 0 from rfl] at Hc0
  have hdone : added = done := by omega
  have hd : d = 0 := by omega
  have hq : q = 0 := by omega
  subst hdone hd hq
  icombine Hadded Hadded_inv gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  rw [← Heq]
  icombine Hdone_ap Hap gives #HPeq
  imod ownApropAuth_reset γ.apGn P0 Pdone _ $$ Hap Hdone_ap with Hap
  ihave Hadded := (join.ownTokAuth_halves γ.ndGn _).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_sub _ γ.ndGn _ $$ Hadded Hdone_toks with Hadded
  rw [Nat.sub_self]
  icases (join.ownTokAuth_halves γ.ndGn 0).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hmask with -
  ihave Hfrag := ownApropFrag_0 (GF := GF) γ.apGn
  imod ownToks_0 (GF := GF) γ.ndGn with Hdone_toks
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hfrag Hd0 Hdep Hqp Hpend] with -
  · inext
    unfold rwgInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    iframe
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide, by omega⟩
  imodintro
  iintro Hwt
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(N.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod dealloc_wait_token wg γ.wgGn (N.@"wg") (0 + 1) (by decide) $$ Hwg Hwaiter Hwt with H
  imod Hmask with -
  imodintro
  iapply HΦ
  isplitl [HPdone Himp]
  · icases HPeq with ⟨HPa, HPb⟩
    ihave H : (▷ P0 : IProp GF) $$ [HPdone]
    · iapply HPa
      inext
      iexact HPdone
    inext
    iapply Himp $$ H
  iexists γ, iprop(True)
  rw [show (0 : Int) + 1 - 1 = 0 from rfl]
  iframe
  isplitr
  · iintro _; itrivial
  iexact Hj

end idiom

end rwg
end k8s
end EtcdGrove
end Perennial
