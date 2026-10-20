/-
**The wait groups of `waitCancelSubstreams`** (`client/v3/watch.go`; D24, the watch client's
reconnection). Lean-first, no Rocq counterpart.

`waitCancelSubstreams` starts one goroutine per resuming substream, each after a `wg.Add(1)` on a
local `sync.WaitGroup` (the fork's F4, `issues/etcd-watch-resume-waitgroup-overflow.md`), and a
goroutine that closes the returned channel after `wg.Wait()`. A goroutine whose watch's context is
done posts the substream on `closingc` from a goroutine of its own, after a `w.wg.Add(1)` on the
stream's wait group (`InvWatchWg.lean`), concurrently with the others.

* **The local join** (`wcjAdder`, `wcjDone`): Perennial's join idiom (`sync.join`, each `Done`
  passing a proposition to the `Wait`), its counter backed by **thread tokens** instead of a bound on
  the number of `Add`s: each `Add(1)` deposits the caller's thread token (the caller gets a fresh one
  at the `go` statement, `wp_fork_tok_self`), each `Done` takes one back (the one the goroutine exits
  with). So the counter is below `threadBound GF ≤ 2^31`. A goroutine that adds to the stream's wait
  group spends its slot's token there (`wp_wgsWg_Add_wcj`: its slot then holds the stream's running
  token, `wcjDoneB`), and puts back the token the inner `go` statement gives it (`wp_wcj_fork`); a
  local `Add` counts the borrowed slots against the stream's deposited tokens.
* **The stream's adder, shared** (`wgsWgShared`, `wgsShareTok`): the waiters' authority at `0`
  (what `Add` needs when the counter may be `0`) in an invariant, with a token per goroutine that may
  `Add`, while `run` (in `newWatchClient`) cannot `Wait`.

A gap in Perennial: its join idiom bounds the number of `Add`s since the last `Wait` (`ownAdder`'s
counter below `2^31 - 1`), not the number of goroutines running; a version backed by thread tokens
(as here and in `InvWatchWg.lean`, `cacheWgInv`) is the general fix to propose.
-/
module

public import Perennial.Proof.sync
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Algebra.AuthProp
public import Proof.go_etcd_io.etcd.client.v3.InvWatchWg

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

section forkLc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

open EctxLanguage ProofMode in
/-- **`Fork e` with a ghost update at the fork** (a local copy of Perennial's `wp_fork_tok`, whose
premise is a plain wand): the fresh thread token and a later credit go to an update, at the
forking thread's mask, that makes the forked thread's `WP` and the forking thread's continuation
— so an invariant can be opened at the fork itself (`Fork` may stutter, so it is not atomic and
`iinv` cannot open one around it). A gap in Perennial: `wp_fork_tok` with this premise is the
general version. -/
theorem wp_fork_tok_upd (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (threadTok -∗ £ 1 -∗ |={E}=> (WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }} ∗
        Φ #())) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro H
  iapply wp_lift_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, ⟨c, t⟩⟩
  icases (goose_bstateInterp_eq σ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  have Hred : BaseStep.Reducible (Fork e, ((σ, ⟨c, t⟩) : BcfgState)) := by
    cases t with
    | zero => exact ⟨[], _, _, [], .forkStutter⟩
    | succ t => exact ⟨[], _, _, _, .fork (.base (not_unwinds_Fork e) (BaseStep.ForkS e σ))⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_fill_of_baseStep_reducible (K := []) Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨e₂', rfl, Hbs⟩ :=
    exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible (K := []) Hred Hstep
  cases Hbs with
  | step hp _ => cases hp
  | tick hc _ => cases hc
  | stutter hc _ => cases hc
  | fork Hb =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := baseStep_Fork_inv (baseStep_of_headStep (not_unwinds_Fork e) Hb)
    rename_i t
    icases threadFuel_fork t $$ Ht with ⟨Ht, Htok⟩
    imod Hclose
    imod H $$ Htok Hcred with ⟨He, HΦ⟩
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht
      iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    isplitl [HΦ]
    · iapply wp_value'
      iexact HΦ
    iapply BigSepL.bigSepL_singleton.2
    iapply wp_seq_ThreadExit $$ He
  | forkStutter =>
    imod Hclose
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht
      iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    isplitl [IH H]
    · iapply IH
      inext
      iexact H
    iapply BigSepL.bigSepL_nil.2
    itrivial

end forkLc

/-- The ghost names of the local join. -/
structure WcjNames where
  γwg : sync.WaitGroupNames
  γap : GName
  γnd : GName
  γdep : GName
  γbor : GName

/-- The namespace of the local join (its `WaitGroup` at `.@"wg"`, its invariant at `.@"inv"`). -/
abbrev wcjN : Namespace := nroot.@"wcjoin"

/-- The namespace of the stream's shared adder. -/
abbrev wgsWgSN : Namespace := nroot.@"wgsWgShare"

/-- The namespace of the invariant holding what `waitCancelSubstreams`' goroutines give back. -/
abbrev wcdN : Namespace := nroot.@"wcDone"

/-- The ghost names of the stream's shared adder. -/
structure WgsShNames where
  γsh : GName
  γu : GName

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

/-! ## The stream's adder, shared -/

/-- **The shared adder's invariant**: the tokens handed out (`n`, half the count), and the waiters'
authority at `0`, or (none handed out) `run`'s key. -/
def wgsShareInv (γS : WgsWgNames) (γh : WgsShNames) : IProp GF :=
  iprop(∃ n : Nat, ownTokAuthDfrac γh.γsh (DFrac.own (1 : Qp).half) n ∗
    (sync.ownWaitGroupWaiters γS.γwg 0 ∨ ⌜n = 0⌝ ∗ dghostVar γh.γu (DFrac.own 1) ()))

/-- **`run`'s side of the shared adder** of the stream's wait group `wg` (names `γS`), `n` tokens
handed out. -/
def wgsWgShared (wg : Loc) (γS : WgsWgNames) (γh : WgsShNames) (n : Nat) : IProp GF :=
  iprop(isWgsWg wg γS ∗ inv wgsWgSN (wgsShareInv γS γh) ∗
    ownTokAuthDfrac γh.γsh (DFrac.own (1 : Qp).half) n ∗ dghostVar γh.γu (DFrac.own 1) () ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)

/-- **A goroutine's token of the shared adder**: the right to `Add(1)` (with a thread token). -/
def wgsShareTok (wg : Loc) (γS : WgsWgNames) (γh : WgsShNames) : IProp GF :=
  iprop(isWgsWg wg γS ∗ inv wgsWgSN (wgsShareInv γS γh) ∗ ownToks γh.γsh 1 ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)

/-! ## The local join -/

/-- **The local join's invariant**: the counter is the goroutines added and not done (`added -
done`), each with its slot's thread token deposited (`j`, tickets `γdep`) or borrowed (`b`: a
running token of the stream's wait group in its place, tickets `γbor`); the propositions of the
`Done`s so far. -/
def wcjInv (γ : WcjNames) (γS : WgsWgNames) : IProp GF :=
  iprop(∃ (ctr : w32) (added done j b : Nat) (Pdone : IProp GF),
    sync.ownWaitGroup γ.γwg ctr ∗
    ownTokAuthDfrac γ.γnd (DFrac.own (1 : Qp).half) added ∗ ownToks γ.γnd done ∗
    ownApropFrag γ.γap Pdone done ∗ Pdone ∗
    threadToks j ∗ ownTokAuth γ.γdep j ∗ ownToks γS.γwr b ∗ ownTokAuth γ.γbor b ∗
    ⌜0 ≤ sint.Z ctr ∧ sint.Z ctr = (added : Int) - done ∧ (added : Int) - done = j + b⌝)

/-- The local join's wait group and invariant (persistent). -/
def isWcj (wg : Loc) (γ : WcjNames) (γS : WgsWgNames) : IProp GF :=
  iprop(sync.isWaitGroup wg γ.γwg (wcjN.@"wg") ∗ inv (wcjN.@"inv") (wcjInv γ γS))

instance isWcj_persistent (wg : Loc) (γ : WcjNames) (γS : WgsWgNames) :
    Persistent (isWcj (GF := GF) wg γ γS) := by
  unfold isWcj; infer_instance

/-- **The right to `Add(1)` to and `Wait` on the local join** (`n` added since the last `Wait`):
the `Wait` gives `P`. -/
def wcjAdder (wg : Loc) (γS : WgsWgNames) (n : Nat) (P : IProp GF) : IProp GF :=
  iprop(∃ (γ : WcjNames) (P' : IProp GF),
    sync.ownWaitGroupWaiters γ.γwg 0 ∗ ownApropAuth γ.γap P' n ∗
    ownTokAuthDfrac γ.γnd (DFrac.own (1 : Qp).half) n ∗ (P' -∗ P) ∗ isWcj wg γ γS ∗
    ⌜threadBound GF ≤ 2 ^ 31⌝)

/-- **A goroutine's right to `Done` the local join** with `P`, its slot's token deposited. -/
def wcjDone (wg : Loc) (γS : WgsWgNames) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : WcjNames, ownAprop γ.γap P ∗ ownToks γ.γnd 1 ∗ ownToks γ.γdep 1 ∗ isWcj wg γ γS)

/-- **The same, its slot's token borrowed** (spent on the stream's wait group, whose running token
is in the slot until the inner `go` statement). -/
def wcjDoneB (wg : Loc) (γS : WgsWgNames) (P : IProp GF) : IProp GF :=
  iprop(∃ γ : WcjNames, ownAprop γ.γap P ∗ ownToks γ.γnd 1 ∗ ownToks γ.γbor 1 ∗ isWcj wg γ γS)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

/-! ## The shared adder -/

theorem wgsWg_share (wg : Loc) :
    wgsWgAdder (GF := GF) wg ⊢ |={⊤}=> ∃ (γS : WgsWgNames) (γh : WgsShNames),
      wgsWgShared wg γS γh 0 := by
  iintro Had
  unfold wgsWgAdder
  icases Had with ⟨%γS, #Hwgs, Hwait, %Hb⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γsh, Ha⟩
  icases (sync.join.ownTokAuth_halves γsh 0).1 $$ Ha with ⟨Ha1, Ha2⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%γu, Hu⟩
  let γh : WgsShNames := ⟨γsh, γu⟩
  imod inv_alloc wgsWgSN ⊤ (wgsShareInv (GF := GF) γS γh) $$ [Ha1 Hwait] with #Hinv
  · inext
    unfold wgsShareInv
    iexists 0
    iframe Ha1
    ileft; iexact Hwait
  imodintro
  iexists γS, γh
  unfold wgsWgShared
  iframe Hwgs Hinv Ha2 Hu
  ipureintro; exact Hb

theorem wgsWg_mint (wg : Loc) (γS : WgsWgNames) (γh : WgsShNames) (n : Nat) :
    wgsWgShared (GF := GF) wg γS γh n ⊢ |={⊤}=>
      wgsWgShared wg γS γh (n + 1) ∗ wgsShareTok wg γS γh := by
  iintro Hs
  unfold wgsWgShared
  icases Hs with ⟨#Hwgs, #Hinv, Ha, Hu, %Hb⟩
  iinv Hinv with Hi Hclose
  iunfold wgsShareInv at Hi
  icases Hi with ⟨%m, >Ha2, Hor⟩
  icombine Ha Ha2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  ihave Hf := (sync.join.ownTokAuth_halves γh.γsh n).2 $$ [Ha Ha2]
  · iframe
  imod ownTokAuth_S γh.γsh n $$ Hf with ⟨Hf, Htok⟩
  icases (sync.join.ownTokAuth_halves γh.γsh (n + 1)).1 $$ Hf with ⟨Ha, Ha2⟩
  icases Hor with (Hw | ⟨-, >Hu2⟩)
  rotate_left
  · icombine Hu Hu2 gives %Hc
    obtain ⟨Hv, -⟩ := Hc
    exfalso
    revert Hv
    simp only [CMRA.Valid, DFrac.op_own]
    intro h
    have : (1 : Rat) + 1 ≤ 1 := h
    grind
  imod Hclose $$ [Ha2 Hw] with -
  · inext
    unfold wgsShareInv
    iexists n + 1
    iframe Ha2
    ileft; iexact Hw
  imodintro
  unfold wgsShareTok
  iframe Hwgs Hinv Ha Hu Htok
  ipureintro; exact ⟨Hb, Hb⟩

theorem wgsWg_burn (wg : Loc) (γS : WgsWgNames) (γh : WgsShNames) (n : Nat) :
    wgsWgShared (GF := GF) wg γS γh (n + 1) ∗ wgsShareTok wg γS γh ⊢ |={⊤}=>
      wgsWgShared wg γS γh n := by
  iintro ⟨Hs, Ht⟩
  unfold wgsWgShared
  icases Hs with ⟨#Hwgs, #Hinv, Ha, Hu, %Hb⟩
  unfold wgsShareTok
  icases Ht with ⟨-, -, Htok, -⟩
  iinv Hinv with Hi Hclose
  iunfold wgsShareInv at Hi
  icases Hi with ⟨%m, >Ha2, Hor⟩
  icombine Ha Ha2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  ihave Hf := (sync.join.ownTokAuth_halves γh.γsh (n + 1)).2 $$ [Ha Ha2]
  · iframe
  imod ownTokAuth_delete_S γh.γsh n $$ Hf Htok with Hf
  icases (sync.join.ownTokAuth_halves γh.γsh n).1 $$ Hf with ⟨Ha, Ha2⟩
  icases Hor with (Hw | Hz)
  rotate_left
  · icases Hz with ⟨>%Hn, -⟩
    omega
  imod Hclose $$ [Ha2 Hw] with -
  · inext
    unfold wgsShareInv
    iexists n
    iframe Ha2
    ileft; iexact Hw
  imodintro
  iframe Hwgs Hinv Ha Hu
  ipureintro; exact Hb

theorem wgsWg_unshare (wg : Loc) (γS : WgsWgNames) (γh : WgsShNames) :
    wgsWgShared (GF := GF) wg γS γh 0 ⊢ |={⊤}=> wgsWgAdder wg := by
  iintro Hs
  unfold wgsWgShared
  icases Hs with ⟨#Hwgs, #Hinv, Ha, Hu, %Hb⟩
  iinv Hinv with Hi Hclose
  iunfold wgsShareInv at Hi
  icases Hi with ⟨%m, >Ha2, Hor⟩
  icombine Ha Ha2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  icases Hor with (>Hw | ⟨-, >Hu2⟩)
  rotate_left
  · icombine Hu Hu2 gives %Hc
    obtain ⟨Hv, -⟩ := Hc
    exfalso
    revert Hv
    simp only [CMRA.Valid, DFrac.op_own]
    intro h
    have : (1 : Rat) + 1 ≤ 1 := h
    grind
  imod Hclose $$ [Ha2 Hu] with -
  · inext
    unfold wgsShareInv
    iexists 0
    iframe Ha2
    iright; iframe Hu; ipureintro; rfl
  imodintro
  unfold wgsWgAdder
  iexists γS
  iframe Hwgs Hw
  ipureintro; exact Hb

/-- The shared tokens back, one per element of `l`. -/
theorem wgsWg_burn_list (wg : Loc) (γS : WgsWgNames) (γh : WgsShNames) (n : Nat) {A : Type}
    (l : List A) :
    wgsWgShared (GF := GF) wg γS γh (n + l.length) ∗ ([∗list] _x ∈ l, wgsShareTok wg γS γh) ⊢
      |={⊤}=> wgsWgShared wg γS γh n := by
  induction l generalizing n with
  | nil =>
    iintro ⟨Hs, -⟩
    simp only [List.length_nil, Nat.add_zero]
    iexact Hs
  | cons x l ih =>
    iintro ⟨Hs, Ht⟩
    icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Ht1, Ht⟩
    rw [show n + (x :: l).length = (n + l.length) + 1 by simp; omega]
    imod wgsWg_burn wg γS γh (n + l.length) $$ [Hs Ht1] with Hs
    · iframe
    iapply ih n $$ [Hs Ht]
    iframe


/-! ## The local join -/

/-- **A fresh local join** (`var wg sync.WaitGroup`), for the stream's wait group names `γS`. -/
theorem wcj_init (wg : Loc) (γS : WgsWgNames) (Hb : threadBound GF ≤ 2 ^ 31) :
    typedPointsto (GF := GF) wg (zero_val sync.WaitGroup) (DFrac.own 1) ⊢
      |={⊤}=> wcjAdder wg γS 0 iprop(True) := by
  iintro Hwg
  imod sync.init_WaitGroup (wcjN.@"wg") wg $$ Hwg with ⟨%γwg, #His, Hctr, Hwait⟩
  imod ownApropAuth_alloc (GF := GF) with ⟨%γap, Hap⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γnd, Hnd⟩
  icases (sync.join.ownTokAuth_halves γnd 0).1 $$ Hnd with ⟨Hnd1, Hnd2⟩
  imod ownToks_0 (GF := GF) γnd with Hnd0
  ihave Hfrag := ownApropFrag_0 (GF := GF) γap
  imod ownTokAuth_alloc (GF := GF) with ⟨%γdep, Hdep⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γbor, Hbor⟩
  imod ownToks_0 (GF := GF) γS.γwr with Hwr0
  let γ : WcjNames := ⟨γwg, γap, γnd, γdep, γbor⟩
  imod inv_alloc (wcjN.@"inv") ⊤ (wcjInv (GF := GF) γ γS) $$ [Hctr Hnd1 Hnd0 Hfrag Hdep Hbor Hwr0]
    with #Hinv
  · inext
    unfold wcjInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    simp only [γ]
    iframe
    isplitr
    · itrivial
    isplitr
    · iapply threadToks_zero
    ipureintro
    exact ⟨by decide, by decide, by simp⟩
  imodintro
  unfold wcjAdder
  iexists γ, iprop(True)
  simp only [γ]
  iframe Hwait Hap Hnd2
  isplitr
  · iintro _; itrivial
  isplitr
  · unfold isWcj; iframe #
  ipureintro; exact Hb

theorem wcjAdder_wand (P' : IProp GF) (wg : Loc) (γS : WgsWgNames) (n : Nat) (P : IProp GF) :
    ⊢ (P -∗ P') -∗ wcjAdder wg γS n P -∗ wcjAdder wg γS n P' := by
  iintro Hw Ha
  unfold wcjAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hwcj, %Hb⟩
  iexists γ, P0
  iframe Hwait Hap Hadded Hwcj
  isplitl [Hw Himp]
  · iintro H
    iapply Hw
    iapply Himp $$ H
  ipureintro; exact Hb

/-- **The local join's `Add(1)`**, by the parent with its thread token, which its new slot holds: a
`Done` right for the goroutine about to start. The counter's bound: the deposited tokens, the
borrowed ones (in the stream's wait group, `γS`) and the caller's are distinct. -/
theorem wp_wcj_Add (P' : IProp GF) (wg swg : Loc) (γS : WgsWgNames) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wcjAdder wg γS n P ∗ isWgsWg swg γS ∗
        threadTok }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); wcjAdder wg γS (n + 1) iprop(P ∗ P') ∗ wcjDone wg γS P' }} := by
  iintro %Φ ⟨#Hsync, Had, #HwgsS, Htok⟩ HΦ
  unfold wcjAdder
  icases Had with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hwcj, %Hb⟩
  ihave #Hwcj2 := Hwcj
  iunfold isWcj at Hwcj2
  icases Hwcj2 with ⟨#Hwg, #Hinv⟩
  ihave #HwgsS' := HwgsS
  iunfold isWgsWg at HwgsS'
  icases HwgsS' with ⟨-, #HinvS⟩
  iapply sync.WaitGroup.wp_Add wg (W64 1) γ.γwg (wcjN.@"wg") $$ [] [Hwait Htok HΦ Hap Hadded Himp]
  · iframe #
  iinv Hinv with Hi Hclose
  iinv HinvS with HiS HcloseS
  have Hm : (↑(wcjN.@"wg") : CoPset) ⊆ (⊤ \ ↑(wcjN.@"inv")) \ ↑wgsWgCN := by solve_ndisj
  iapply fupd_mask_intro Hm
  iintro Hmask
  inext
  iunfold wcjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hj, Hdep, Hbor, Hbora, %Hctr⟩
  iunfold wgsWgInv at HiS
  icases HiS with ⟨%ctrS, %k, HwgoS, HrunS, Hk, %HctrS⟩
  icombine HrunS Hbor gives %Hbk
  ihave Hjk := (threadToks_add j k).2 $$ [Hj Hk]
  · iframe
  icases threadToks_add_one_lt (j + k) $$ [Htok Hjk] with ⟨%Hlt, Hjk⟩
  · iframe
  rw [show j + k + 1 = (j + 1) + k by omega] at *
  icases (threadToks_add (j + 1) k).1 $$ Hjk with ⟨Hj, Hk⟩
  icombine Hadded Hadded_inv gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  have hz : sint.Z (ctr + W32 1) = sint.Z ctr + 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwait
  iintro Hwait Hwgo
  imod Hmask with -
  imod ownApropAuth_add P' γ.γap P0 n $$ Hap with ⟨Hap, Hdone_ap'⟩
  ihave Hadded := (sync.join.ownTokAuth_halves γ.γnd n).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.γnd _ $$ Hadded with ⟨Hadded, Hnd_tok⟩
  icases (sync.join.ownTokAuth_halves γ.γnd _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod ownTokAuth_S γ.γdep j $$ Hdep with ⟨Hdep, Hdep_tok⟩
  imod HcloseS $$ [HwgoS HrunS Hk] with -
  · inext
    unfold wgsWgInv
    iexists ctrS, k
    iframe
    ipureintro; exact HctrS
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hj Hdep Hbor Hbora] with -
  · inext
    unfold wcjInv
    iexists ctr + W32 (sint.Z (W64 1)), n + 1, done, j + 1, b, Pdone
    iframe
    ipureintro
    rw [h2, hz]
    refine ⟨by omega, by push_cast; omega, by push_cast; omega⟩
  imodintro
  iapply HΦ
  isplitl [Hwait Hap Hadded Himp]
  · iexists γ, iprop(P0 ∗ P')
    iframe Hwait Hap Hadded
    isplitl [Himp]
    · iintro ⟨H1, H2⟩
      iframe H2
      iapply Himp $$ H1
    isplitr
    · iexact Hwcj
    ipureintro; exact Hb
  unfold wcjDone
  iexists γ
  iframe Hdone_ap' Hnd_tok Hdep_tok Hwcj

/-- **The local join's `Done()`**, by a goroutine with its slot's token deposited: `P` passed to
the `Wait`, the slot's thread token back (the one the goroutine exits with). -/
theorem wp_wcj_Done (wg : Loc) (γS : WgsWgNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wcjDone wg γS P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hsync, Hd, HP⟩ HΦ
  unfold wcjDone
  icases Hd with ⟨%γ, Hap, Hnd_tok, Hdep_tok, #Hwcj⟩
  ihave #Hwcj2 := Hwcj
  iunfold isWcj at Hwcj2
  icases Hwcj2 with ⟨#Hwg, #Hinv⟩
  iapply sync.WaitGroup.wp_Done wg γ.γwg (wcjN.@"wg") $$ [] [Hap Hnd_tok Hdep_tok HP HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  have Hm : (↑(wcjN.@"wg") : CoPset) ⊆ ⊤ \ ↑(wcjN.@"inv") := by solve_ndisj
  iapply fupd_mask_intro Hm
  iintro Hmask
  inext
  iunfold wcjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hj, Hdep, Hbor, Hbora, %Hctr⟩
  icombine Hdep Hdep_tok gives %Hj1
  icombine Hnd_tok Hdone_toks as Hdone_toks
  icombine Hadded_inv Hdone_toks gives %Hle
  icombine Hap Hdone_ap as Hdone_ap
  obtain ⟨Hc0, Hc1, Hc2⟩ := Hctr
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  icases (threadToks_add j' 1).1 $$ Hj with ⟨Hj, Htok⟩
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; constructor <;> word
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.γdep j' $$ Hdep Hdep_tok with Hdep
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HP HPdone Hj Hdep Hbor Hbora] with -
  · inext
    unfold wcjInv
    iexists ctr - W32 1, added, 1 + done, j', b, iprop(P ∗ Pdone)
    iframe Hwgo Hadded_inv Hdone_ap Hj Hdep Hbor Hbora
    rw [Nat.add_comm 1 done]
    iframe Hdone_toks
    isplitl [HP HPdone]
    · iframe
    ipureintro
    rw [hz]
    refine ⟨by omega, by push_cast; omega, by push_cast; omega⟩
  imodintro
  iapply HΦ
  iexact Htok

/-- **The local join's `Wait()`**: the propositions of every `Done` since the last `Wait`. -/
theorem wp_wcj_Wait (wg : Loc) (γS : WgsWgNames) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wcjAdder wg γS n P }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ wcjAdder wg γS 0 iprop(True) }} := by
  iintro %Φ ⟨#Hsync, Ha⟩ HΦ
  iapply wp_fupd
  unfold wcjAdder
  icases Ha with ⟨%γ, %P0, Hwait, Hap, Hadded, Himp, #Hwcj, %Hb⟩
  ihave #Hwcj2 := Hwcj
  iunfold isWcj at Hwcj2
  icases Hwcj2 with ⟨#Hwg, #Hinv⟩
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wcjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod sync.alloc_wait_token wg γ.γwg (wcjN.@"wg") 0 (by decide) $$ Hwg Hwait with ⟨Hwaiter, Htok⟩
  imod Hmask with -
  imodintro
  iapply sync.WaitGroup.wp_Wait wg γ.γwg (wcjN.@"wg") $$ [Htok] [Hap Hadded Himp Hwaiter HΦ]
  · iframe #; iframe
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold wcjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hj, Hdep, Hbor, Hbora, %Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %Hctr_zero Hwgo
  have hctr : ctr = W32 0 := by
    apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using Hctr_zero
  subst hctr
  obtain ⟨-, Hc1, Hc2⟩ := Hctr
  have hdone : added = done := by simp only [show sint.Z (W32 0) = 0 from rfl] at Hc1; omega
  have hj : j = 0 := by omega
  have hb : b = 0 := by omega
  subst hdone hj hb
  icombine Hadded Hadded_inv gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  rw [← Heq]
  icombine Hdone_ap Hap gives #HPeq
  imod ownApropAuth_reset γ.γap P0 Pdone _ $$ Hap Hdone_ap with Hap
  ihave Hadded := (sync.join.ownTokAuth_halves γ.γnd _).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_sub _ γ.γnd _ $$ Hadded Hdone_toks with Hadded
  rw [Nat.sub_self]
  icases (sync.join.ownTokAuth_halves γ.γnd 0).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hmask with -
  ihave Hfrag := ownApropFrag_0 (GF := GF) γ.γap
  imod ownToks_0 (GF := GF) γ.γnd with Hdone_toks
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hfrag Hj Hdep Hbor Hbora] with -
  · inext
    unfold wcjInv
    iexists W32 0, 0, 0, 0, 0, iprop(True)
    iframe
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide, by simp⟩
  imodintro
  iintro Hwt
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wcjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod sync.dealloc_wait_token wg γ.γwg (wcjN.@"wg") (0 + 1) (by decide) $$ Hwg Hwaiter Hwt with H
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
  isplitr
  · iexact Hwcj
  ipureintro; exact Hb

/-! ## A goroutine adding to the stream's wait group -/

/-- **`w.wg.Add(1)` by a goroutine of the local join** (a token of the shared adder): its slot's
thread token is deposited for the stream's new running token, which takes the slot's place (the
goroutine's right becomes `wcjDoneB`). -/
theorem wp_wgsWg_Add_wcj (wg swg : Loc) (γS : WgsWgNames) (γh : WgsShNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wcjDone wg γS P ∗ wgsShareTok swg γS γh }}
      (App (Val (swg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); wcjDoneB wg γS P ∗ wgsShareTok swg γS γh }} := by
  iintro %Φ ⟨#Hsync, Hd, Ht⟩ HΦ
  unfold wcjDone
  icases Hd with ⟨%γ, Hap, Hnd_tok, Hdep_tok, #Hwcj⟩
  ihave #Hwcj2 := Hwcj
  iunfold isWcj at Hwcj2
  icases Hwcj2 with ⟨-, #Hinv⟩
  unfold wgsShareTok
  icases Ht with ⟨#HwgsS, #HinvSh, Hsh_tok, %Hb⟩
  ihave #HwgsS2 := HwgsS
  iunfold isWgsWg at HwgsS2
  icases HwgsS2 with ⟨#HwgS, #HinvS⟩
  iapply sync.WaitGroup.wp_Add swg (W64 1) γS.γwg wgsWgWN $$ [] [Hap Hnd_tok Hdep_tok Hsh_tok HΦ]
  · iframe #
  iinv HinvS with HiS HcloseS
  iinv HinvSh with HiSh HcloseSh
  iinv Hinv with Hi Hclose
  have Hm : (↑wgsWgWN : CoPset) ⊆ ((⊤ \ ↑wgsWgCN) \ ↑wgsWgSN) \ ↑(wcjN.@"inv") := by
    solve_ndisj
  iapply fupd_mask_intro Hm
  iintro Hmask
  inext
  iunfold wgsWgInv at HiS
  icases HiS with ⟨%ctrS, %k, HwgoS, HrunS, Hk, %HctrS⟩
  iunfold wgsShareInv at HiSh
  icases HiSh with ⟨%m, Hsha, Hor⟩
  icombine Hsha Hsh_tok gives %Hm1
  icases Hor with (Hw | ⟨%Hm0, -⟩)
  rotate_left
  · omega
  iunfold wcjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hj, Hdep, Hbor, Hbora, %Hctr⟩
  icombine Hdep Hdep_tok gives %Hj1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  icases (threadToks_add j' 1).1 $$ Hj with ⟨Hj, Htok⟩
  icases threadToks_add_one_lt k $$ [Htok Hk] with ⟨%Hlt, Hk⟩
  · iframe
  obtain ⟨Hc0, Hck⟩ := HctrS
  have hc : ((sint.nat ctrS : Nat) : Int) = sint.Z ctrS := Int.toNat_of_nonneg Hc0
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hn : sint.nat (ctrS + W32 (sint.Z (W64 1))) = sint.nat ctrS + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  have hz : sint.Z (ctrS + W32 (sint.Z (W64 1))) = sint.Z ctrS + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  iexists ctrS
  iframe HwgoS
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hw
  iintro Hw HwgoS
  imod Hmask with -
  imod ownTokAuth_S γS.γwr k $$ HrunS with ⟨HrunS, Hrtok⟩
  imod ownTokAuth_delete_S γ.γdep j' $$ Hdep Hdep_tok with Hdep
  imod ownTokAuth_S γ.γbor b $$ Hbora with ⟨Hbora, Hbor_tok⟩
  ihave Hbor := ownToks_add_2 1 b γS.γwr $$ [Hbor Hrtok]
  · iframe
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hj Hdep Hbor Hbora] with -
  · inext
    unfold wcjInv
    iexists ctr, added, done, j', b + 1, Pdone
    iframe
    ipureintro
    obtain ⟨h0, h1, h2⟩ := Hctr
    refine ⟨h0, h1, by push_cast at h2 ⊢; omega⟩
  imod HcloseSh $$ [Hsha Hw] with -
  · inext
    unfold wgsShareInv
    iexists m
    iframe Hsha
    ileft; iexact Hw
  imod HcloseS $$ [HwgoS HrunS Hk] with -
  · inext
    unfold wgsWgInv
    iexists ctrS + W32 (sint.Z (W64 1)), k + 1
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  isplitl [Hap Hnd_tok Hbor_tok]
  · unfold wcjDoneB
    iexists γ
    iframe Hap Hnd_tok Hbor_tok Hwcj
  iframe HwgsS HinvSh Hsh_tok
  ipureintro; exact Hb

/-- **The inner `go` statement of a goroutine of the local join** (after `wp_wgsWg_Add_wcj`): at
the fork, the stream's running token leaves the slot for the new goroutine and the fork's fresh
thread token takes its place (the goroutine's right is `wcjDone` again). -/
theorem wp_wcj_fork (wg swg : Loc) (γS : WgsWgNames) (P : IProp GF) (e : Expr)
    (Φ : val → IProp GF) :
    wcjDoneB wg γS P ∗ isWgsWg swg γS ∗
      ▷ (wgsWgDone swg -∗ WP e {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) ∗
      ▷ (wcjDone wg γS P -∗ Φ #()) ⊢
    WP (Fork e) {{ Φ }} := by
  iintro ⟨Hd, #HwgsS, He, HΦ⟩
  unfold wcjDoneB
  icases Hd with ⟨%γ, Hap, Hnd, Hbor_tok, #Hwcj⟩
  ihave #Hwcj2 := Hwcj
  iunfold isWcj at Hwcj2
  icases Hwcj2 with ⟨-, #Hinv⟩
  iapply wp_fork_tok_upd
  inext
  iintro Htok Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑(wcjN.@"inv")) $$ Hlc Hi with Hi
  iunfold wcjInv at Hi
  icases Hi with ⟨%ctr, %added, %done, %j, %b, %Pdone, Hwgo, Hadded_inv, Hdone_toks, Hdone_ap,
    HPdone, Hj, Hdep, Hbor, Hbora, %Hctr⟩
  icombine Hbora Hbor_tok gives %Hb1
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  icases ownToks_add_1 1 b' γS.γwr $$ Hbor with ⟨Hbor, Hrtok⟩
  imod ownTokAuth_delete_S γ.γbor b' $$ Hbora Hbor_tok with Hbora
  ihave Hj := (threadToks_add j 1).2 $$ [Hj Htok]
  · iframe
  imod ownTokAuth_S γ.γdep j $$ Hdep with ⟨Hdep, Hdep_tok⟩
  imod Hclose $$ [Hwgo Hadded_inv Hdone_toks Hdone_ap HPdone Hj Hdep Hbor Hbora] with -
  · inext
    unfold wcjInv
    iexists ctr, added, done, j + 1, b', Pdone
    iframe
    ipureintro
    obtain ⟨h0, h1, h2⟩ := Hctr
    refine ⟨h0, h1, by push_cast at h2 ⊢; omega⟩
  imodintro
  isplitl [He Hrtok]
  · iapply He
    unfold wgsWgDone
    iexists γS
    iframe HwgsS Hrtok
  iapply HΦ
  unfold wcjDone
  iexists γ
  iframe Hap Hnd Hdep_tok Hwcj

end lemmas

end client
end EtcdGrove
end Perennial
