/-
Lean-first (no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12;
`notes/trace-check-design.md` §6, Q34; `notes/decisions.md`, "The harness (RunConcurrent)"):
**the harness's two wait-group idioms**, over Perennial's raw `WaitGroup` specs (taken as
hypotheses, as `sync.tokJoin` does).

* **`netJoin`** (`c.net`, the network's goroutines): several adders (the three `app`s, each
  holding a fraction of the adders' right, `njAdder q`), an unbounded number of `Add(1)`s, each
  backed by the caller's thread token, which the slot holds until the goroutine's `Done` hands it
  back (CLAUDE.md, "Bounds": the counter is below the thread bound, `[ThreadBoundLe GF (2 ^ 31)]`).
  Perennial's `sync.tokJoin` has a single adder (`ownAdder`, exclusive) and carries propositions; the
  network's goroutines return nothing and are added from three goroutines at once, hence this local
  form (the general shared-adder join is recorded in `notes/perennial-changes.md`). Once the adders
  have all come back (`njAdder 1`), `njClose` gives the waiters' right, and `wp_Wait` returns.
* **`join3`** (`drivers`, a local `WaitGroup`): one `Add(3)` from a fresh wait group, three `Done`s,
  one `Wait` (`sync.join`'s `Add` is `Add(1)` only).

Neither carries a resource through `Done`/`Wait`: the harness needs none back.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.WaitGroupDefs
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode sync

/-- The network join's names. -/
structure NetJoinNames where
  wg : WaitGroupNames
  /-- the slots holding their thread token -/
  dep : GName
  /-- the adders' right (a fraction of `()`) -/
  ad : GName

/-- The `drivers` join's names. -/
structure Join3Names where
  wg : WaitGroupNames
  /-- the goroutines not yet done -/
  nd : GName

section idioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-! ## `netJoin` -/

/-- The network join's invariant: the counter is the deposited thread tokens; the waiters' right
is here, or the whole adders' right (after `njClose`). -/
def njInv (γ : NetJoinNames) : IProp GF :=
  iprop(∃ (ctr : w32) (j : Nat), ownWaitGroup γ.wg ctr ∗ threadToks j ∗ ownTokAuth γ.dep j ∗
    ⌜sint.Z ctr = j⌝ ∗ (ownWaitGroupWaiters γ.wg 0 ∨ dghostVar γ.ad (DFrac.own 1) ()))

/-- The network join (persistent). -/
def isNetJoin (N : Namespace) (wg : Loc) (γ : NetJoinNames) : IProp GF :=
  iprop(isWaitGroup wg γ.wg (N.@"wg") ∗ inv (N.@"inv") (njInv γ))

instance isNetJoin_persistent (N : Namespace) (wg : Loc) (γ : NetJoinNames) :
    Persistent (isNetJoin (GF := GF) N wg γ) := by
  unfold isNetJoin; infer_instance

/-- **A share `q` of the right to `Add`.** -/
def njAdder (N : Namespace) (wg : Loc) (γ : NetJoinNames) (q : Qp) : IProp GF :=
  iprop(dghostVar γ.ad (DFrac.own q) () ∗ isNetJoin N wg γ)

/-- **A goroutine's right to `Done`** (its slot's thread token deposited). -/
def njDone (N : Namespace) (wg : Loc) (γ : NetJoinNames) : IProp GF :=
  iprop(ownToks γ.dep 1 ∗ isNetJoin N wg γ)

/-- The adders' right, split. -/
theorem njAdder_split (N : Namespace) (wg : Loc) (γ : NetJoinNames) (q1 q2 : Qp) :
    njAdder (GF := GF) N wg γ (q1 + q2) ⊢ njAdder N wg γ q1 ∗ njAdder N wg γ q2 := by
  unfold njAdder
  iintro ⟨H, #Hj⟩
  icases dghostVar_split γ.ad () (DFrac.own q1) (DFrac.own q2) $$ [H] with ⟨H1, H2⟩
  · rw [DFrac.op_own]; iexact H
  iframe H1 H2 Hj

/-- An adder's share knows the join. -/
theorem njAdder_isNetJoin (N : Namespace) (wg : Loc) (γ : NetJoinNames) (q : Qp) :
    njAdder (GF := GF) N wg γ q ⊢ njAdder N wg γ q ∗ isNetJoin N wg γ := by
  unfold njAdder
  iintro ⟨H, #Hj⟩
  iframe H Hj

/-- The adders' right, joined. -/
theorem njAdder_join (N : Namespace) (wg : Loc) (γ : NetJoinNames) (q1 q2 : Qp) :
    njAdder (GF := GF) N wg γ q1 ∗ njAdder N wg γ q2 ⊢ njAdder N wg γ (q1 + q2) := by
  unfold njAdder
  iintro ⟨⟨H1, #Hj⟩, ⟨H2, -⟩⟩
  iframe Hj
  icombine H1 H2 as H
  iexact H

/-- An adder's share is not the whole right: the invariant holds the waiters' right. -/
theorem nj_left {W : IProp GF} (γ : NetJoinNames) (q : Qp) :
    ⊢ dghostVar (GF := GF) γ.ad (DFrac.own q) () -∗ (W ∨ dghostVar γ.ad (DFrac.own 1) ()) -∗
      dghostVar γ.ad (DFrac.own q) () ∗ W := by
  iintro Had Hw
  icases Hw with (Hw | Hw)
  · iframe Had Hw
  · icombine Hw Had gives %Hv
    exfalso
    have := DFrac.valid_own_op Hv.1
    simp at this

/-- **A fresh wait group as the network's join**: the whole adders' right. -/
theorem nj_init (N : Namespace) (wg : Loc) (γwg : WaitGroupNames) (E : CoPset) :
    isWaitGroup (GF := GF) wg γwg (N.@"wg") ∗ ownWaitGroup γwg (W32 0) ∗
      ownWaitGroupWaiters γwg 0 ⊢ |={E}=> ∃ γ : NetJoinNames, njAdder N wg γ 1 := by
  iintro ⟨#His, Hctr, Hwait⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γdep, Hdep⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%γad, Had⟩
  let γ : NetJoinNames := ⟨γwg, γdep, γad⟩
  imod inv_alloc (N.@"inv") E (njInv (GF := GF) γ) $$ [Hctr Hwait Hdep] with #Hinv
  · inext
    unfold njInv
    iexists W32 0, 0
    iframe Hctr Hdep
    isplitr
    · iapply threadToks_zero
    isplitr
    · ipureintro; decide
    ileft; iexact Hwait
  imodintro
  iexists γ
  unfold njAdder isNetJoin
  iframe Had His Hinv

/-- **`wg.Add(1)` by an adder, with its thread token**: the slot holds the token; the goroutine
about to start gets the right to `Done`. -/
theorem netJoin.wp_Add_of [ThreadBoundLe GF (2 ^ 31)]
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (N : Namespace) (wg : Loc) (γ : NetJoinNames) (q : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ njAdder N wg γ q ∗ threadTok }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); njAdder N wg γ q ∗ njDone N wg γ }} := by
  wp_start_folded as ⟨Had, Htok⟩
  unfold njAdder
  icases Had with ⟨Had, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isNetJoin at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv⟩
  wp_apply_core wp_Add wg (W64 1) γ.wg (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold njInv at Hi
  icases Hi with ⟨%ctr, %j, Hwgo, >Hjt, >Hdep, >%Hctr, >Hw⟩
  icases threadToks_add_one_lt j $$ [Htok Hjt] with ⟨%Hlt, Hjt⟩
  · iframe
  have Hb := ThreadBoundLe.le (GF := GF) (2 ^ 31)
  icases nj_left γ q $$ Had Hw with ⟨Had, Hw⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hw
  iintro Hw Hwgo
  imod Hmask with -
  imod ownTokAuth_S γ.dep j $$ Hdep with ⟨Hdep, Hdtok⟩
  have hz : sint.Z (ctr + W32 1) = sint.Z ctr + 1 := by
    have : sint.Z ctr < 2 ^ 31 - 1 := by omega
    word
  imod Hclose $$ [Hwgo Hjt Hdep Hw] with -
  · inext
    unfold njInv
    iexists ctr + W32 (sint.Z (W64 1)), j + 1
    iframe Hwgo Hjt Hdep
    isplitr
    · ipureintro; rw [h2, hz]; push_cast; omega
    ileft; iexact Hw
  imodintro
  iapply HΦ
  unfold njDone
  iframe Had Hj Hdtok

/-- **A goroutine's `wg.Done()`**: its slot's thread token back. -/
theorem netJoin.wp_Done_of
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (N : Namespace) (wg : Loc) (γ : NetJoinNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ njDone N wg γ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  wp_start_folded as Hd
  unfold njDone
  icases Hd with ⟨Hdtok, #Hj⟩
  iunfold isNetJoin at Hj
  icases Hj with ⟨#Hwg, #Hinv⟩
  wp_apply_core wp_Done wg γ.wg (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  iunfold njInv at Hi
  icases Hi with ⟨%ctr, %j, Hwgo, Hjt, Hdep, %Hctr, Hw⟩
  icombine Hdep Hdtok gives %Hj1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  icases (threadToks_add j' 1).1 $$ Hjt with ⟨Hjt, Htok⟩
  ihave %Hlt := threadToks_lt (j' + 1) $$ [Hjt Htok]
  · iapply (threadToks_add j' 1).2; iframe
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; push_cast at Hctr; constructor <;> word
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.dep j' $$ Hdep Hdtok with Hdep
  imod Hclose $$ [Hwgo Hjt Hdep Hw] with -
  · inext
    unfold njInv
    iexists ctr - W32 1, j'
    iframe Hwgo Hjt Hdep Hw
    ipureintro; rw [hz]; push_cast at Hctr; omega
  imodintro
  iapply HΦ
  iexact Htok

/-- **The adders all back**: the waiters' right, out of the invariant (the adders' whole right in
its place, so no `Add` can follow). -/
theorem njClose (N : Namespace) (wg : Loc) (γ : NetJoinNames) :
    njAdder (GF := GF) N wg γ 1 ⊢ |={⊤}=> ownWaitGroupWaiters γ.wg 0 ∗ isNetJoin N wg γ := by
  unfold njAdder
  iintro ⟨Had, #Hj⟩
  ihave #Hj2 := Hj
  iunfold isNetJoin at Hj2
  icases Hj2 with ⟨#Hwg, #Hinv⟩
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold njInv at Hi
  icases Hi with ⟨%ctr, %j, Hwgo, Hjt, Hdep, Hctr, >Hw⟩
  icases nj_left γ 1 $$ Had Hw with ⟨Had, Hw⟩
  imod Hclose $$ [Hwgo Hjt Hdep Hctr Had] with -
  · inext
    unfold njInv
    iexists ctr, j
    iframe Hwgo Hjt Hdep Hctr
    iright; iexact Had
  imodintro
  iframe Hw Hj

/-- **`wg.Wait()`, the adders all back.** -/
theorem netJoin.wp_Wait_of
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (N : Namespace) (wg : Loc) (γ : NetJoinNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownWaitGroupWaiters γ.wg 0 ∗ isNetJoin N wg γ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨Hwait, #Hj⟩
  iunfold isNetJoin at Hj
  icases Hj with ⟨#Hwg, #Hinv⟩
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(N.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wg (N.@"wg") 0 (by decide) $$ Hwg Hwait with ⟨-, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core wp_Wait wg γ.wg (N.@"wg") $$ [Htok] [-]
  · iframe #; iframe
  imod inv_acc (E := ⊤ \ ↑(N.@"wg")) (wg_mask_ndot_ne N "inv" "wg" (by decide)) $$ Hinv
    with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold njInv at Hi
  icases Hi with ⟨%ctr, %j, Hwgo, Hjt, Hdep, Hctr, Hw⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hjt Hdep Hctr Hw] with -
  · inext
    unfold njInv
    iexists ctr, j
    iframe Hwgo Hjt Hdep Hctr Hw
  imodintro
  iintro -
  iapply HΦ
  itrivial

/-! ## `join3` -/

/-- The `drivers` join's invariant: the counter is the goroutines not yet done, at most three. -/
def j3Inv (γ : Join3Names) : IProp GF :=
  iprop(∃ (ctr : w32) (n : Nat), ownWaitGroup γ.wg ctr ∗ ownTokAuth γ.nd n ∗
    ⌜sint.Z ctr = n ∧ n ≤ 3⌝)

/-- The `drivers` join (persistent). -/
def isJoin3 (N : Namespace) (wg : Loc) (γ : Join3Names) : IProp GF :=
  iprop(isWaitGroup wg γ.wg (N.@"wg") ∗ inv (N.@"inv") (j3Inv γ))

instance isJoin3_persistent (N : Namespace) (wg : Loc) (γ : Join3Names) :
    Persistent (isJoin3 (GF := GF) N wg γ) := by
  unfold isJoin3; infer_instance

/-- A driver's right to `Done`. -/
def j3Done (N : Namespace) (wg : Loc) (γ : Join3Names) : IProp GF :=
  iprop(ownToks γ.nd 1 ∗ isJoin3 N wg γ)

/-- The waiter's right to `Wait`. -/
def j3Waiter (N : Namespace) (wg : Loc) (γ : Join3Names) : IProp GF :=
  iprop(ownWaitGroupWaiters γ.wg 0 ∗ isJoin3 N wg γ)

/-- **`wg.Add(3)` on a fresh wait group**: three rights to `Done` and the right to `Wait`. -/
theorem join3.wp_Add_of
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (N : Namespace) (wg : Loc) (γwg : WaitGroupNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isWaitGroup wg γwg (N.@"wg") ∗
        ownWaitGroup γwg (W32 0) ∗ ownWaitGroupWaiters γwg 0 }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 3)))
    {{ RET #(); ∃ γ : Join3Names, j3Done N wg γ ∗ j3Done N wg γ ∗ j3Done N wg γ ∗
        j3Waiter N wg γ }} := by
  wp_start_folded as ⟨#Hwg, Hwgo, Hw⟩
  wp_apply_core wp_Add wg (W64 3) γwg (N.@"wg") $$ [] [-]
  · iframe #
  iapply fupd_mask_intro (fun _ _ => CoPset.mem_full)
  iintro Hmask
  inext
  iexists W32 0
  iframe Hwgo
  isplitr
  · ipureintro; decide
  iright
  iframe Hw
  iintro Hw Hwgo
  imod Hmask with -
  imod ownTokAuth_alloc (GF := GF) with ⟨%γnd, Hnd⟩
  imod ownTokAuth_add 3 γnd 0 $$ Hnd with ⟨Hnd, Htoks⟩
  let γ : Join3Names := ⟨γwg, γnd⟩
  imod inv_alloc (N.@"inv") ⊤ (j3Inv (GF := GF) γ) $$ [Hwgo Hnd] with #Hinv
  · inext
    unfold j3Inv
    iexists W32 0 + W32 (sint.Z (W64 3)), 0 + 3
    iframe Hwgo Hnd
    ipureintro; decide
  icases ownToks_add_1 1 2 γnd $$ Htoks with ⟨Htoks, Ht1⟩
  icases ownToks_add_1 1 1 γnd $$ Htoks with ⟨Ht2, Ht3⟩
  imodintro
  iapply HΦ
  iexists γ
  unfold j3Done j3Waiter isJoin3
  iframe Ht1 Ht2 Ht3 Hw Hwg Hinv

/-- **A driver's `wg.Done()`.** -/
theorem join3.wp_Done_of
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (N : Namespace) (wg : Loc) (γ : Join3Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ j3Done N wg γ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as Hd
  unfold j3Done
  icases Hd with ⟨Hdtok, #Hj⟩
  iunfold isJoin3 at Hj
  icases Hj with ⟨#Hwg, #Hinv⟩
  wp_apply_core wp_Done wg γ.wg (N.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne N "wg" "inv" (by decide))
  iintro Hmask
  inext
  iunfold j3Inv at Hi
  icases Hi with ⟨%ctr, %n, Hwgo, Hnd, %Hctr⟩
  icombine Hnd Hdtok gives %Hn1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by
    have : 1 ≤ sint.Z ctr := by push_cast at Hctr; omega
    word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; push_cast at Hctr; constructor <;> omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.nd n' $$ Hnd Hdtok with Hnd
  imod Hclose $$ [Hwgo Hnd] with -
  · inext
    unfold j3Inv
    iexists ctr - W32 1, n'
    iframe Hwgo Hnd
    ipureintro; rw [hz]; push_cast at Hctr; omega
  imodintro
  iapply HΦ
  itrivial

/-- **The waiter's `wg.Wait()`.** -/
theorem join3.wp_Wait_of
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (N : Namespace) (wg : Loc) (γ : Join3Names) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ j3Waiter N wg γ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as Hw
  unfold j3Waiter
  icases Hw with ⟨Hwait, #Hj⟩
  iunfold isJoin3 at Hj
  icases Hj with ⟨#Hwg, #Hinv⟩
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(N.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wg (N.@"wg") 0 (by decide) $$ Hwg Hwait with ⟨-, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core wp_Wait wg γ.wg (N.@"wg") $$ [Htok] [-]
  · iframe #; iframe
  imod inv_acc (E := ⊤ \ ↑(N.@"wg")) (wg_mask_ndot_ne N "inv" "wg" (by decide)) $$ Hinv
    with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold j3Inv at Hi
  icases Hi with ⟨%ctr, %n, Hwgo, Hnd, Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hnd Hctr] with -
  · inext
    unfold j3Inv
    iexists ctr, n
    iframe Hwgo Hnd Hctr
  imodintro
  iintro -
  iapply HΦ
  itrivial

end idioms

end TraceCheck
end EtcdGrove
end Perennial
