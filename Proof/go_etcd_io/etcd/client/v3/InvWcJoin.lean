/-
**The wait groups of `waitCancelSubstreams`** (`client/v3/watch.go`; D25, the watch client's
reconnection). Lean-first, no Rocq counterpart.

`waitCancelSubstreams` starts one goroutine per resuming substream, each after a `wg.Add(1)` on a
local `sync.WaitGroup` (the fork's F4, `issues/etcd-watch-resume-waitgroup-overflow.md`), and a
goroutine that closes the returned channel after `wg.Wait()`. A goroutine whose watch's context is
done posts the substream on `closingc` from a goroutine of its own, after a `w.wg.Add(1)` on the
stream's wait group (`InvWatchWg.lean`), concurrently with the others.

* **The local join** is Perennial's thread-token join (`sync.tokJoin`, at `wcjN`): each `Add(1)`
  deposits the caller's thread token (the caller gets a fresh one at the `go` statement,
  `wp_fork_tok_self`), each `Done` takes one back. A goroutine that adds to the stream's wait group
  lends its slot's token there (`wp_wgsWg_Add_wcj`: the slot then holds the stream's running token,
  the receipt `wcjL`, and the goroutine's right is `ownLent`), and refills the slot with the token
  of the inner `go` statement, at the fork itself (`wp_wcj_fork`, Perennial's `wp_fork_tok_upd`).
  The lending law (`wcj_law`): the deposited tokens and the borrowed slots are distinct thread
  tokens, the latter in the stream's counter invariant.
* **The stream's adder, shared** (`wgsWgShared`, `wgsShareTok`): the waiters' authority at `0`
  (what `Add` needs when the counter may be `0`) in an invariant, with a token per goroutine that may
  `Add`, while `run` (in `newWatchClient`) cannot `Wait`.
-/
module

public import Perennial.Proof.sync.WaitGroupTokJoin
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

/-- The namespace of the local join (`sync.tokJoin`'s: its `WaitGroup` at `.@"wg"`, its invariant
at `.@"inv"`). -/
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

/-- **A lent slot's receipt**: a running token of the stream's wait group (names `γS`). -/
abbrev wcjL (γS : WgsWgNames) : IProp GF := ownToks γS.γwr 1

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

theorem wcj_receipts_toks (γS : WgsWgNames) (b : Nat) :
    sync.tokJoin.receipts (wcjL (GF := GF) γS) b ⊢ |==> ownToks γS.γwr b := by
  induction b with
  | zero => iintro -; iapply ownToks_0
  | succ b ih =>
    simp only [sync.tokJoin.receipts]
    iintro ⟨H1, Hr⟩
    imod ih $$ Hr with Hr
    imodintro
    rw [show b + 1 = 1 + b by omega]
    iapply (ownToks_add b 1 γS.γwr).2
    iframe

theorem wcj_toks_receipts (γS : WgsWgNames) (b : Nat) :
    ownToks γS.γwr b ⊢ sync.tokJoin.receipts (wcjL (GF := GF) γS) b := by
  induction b with
  | zero => simp only [sync.tokJoin.receipts]; iintro -; itrivial
  | succ b ih =>
    simp only [sync.tokJoin.receipts]
    rw [show b + 1 = 1 + b by omega]
    iintro H
    icases (ownToks_add b 1 γS.γwr).1 $$ H with ⟨H1, H⟩
    iframe H1
    iapply ih $$ H

/-- **The local join's lending law**: the deposited thread tokens and the borrowed slots' are
distinct, the latter in the stream's counter invariant. -/
theorem wcj_law (swg : Loc) (γS : WgsWgNames) :
    isWgsWg (GF := GF) swg γS ⊢ sync.tokJoin.lendLaw wcjN (wcjL γS) := by
  iintro #HwgsS
  iunfold isWgsWg at HwgsS
  icases HwgsS with ⟨-, #HinvS⟩
  unfold sync.tokJoin.lendLaw
  imodintro
  iintro %m %b Hm Hr
  imod wcj_receipts_toks γS b $$ Hr with Hr
  iinv HinvS with HiS HcloseS
  iunfold wgsWgInv at HiS
  icases HiS with ⟨%ctrS, %k, HwgoS, >HrunS, >Hk, HctrS⟩
  icombine HrunS Hr gives %Hbk
  ihave Hmk := (threadToks_add m k).2 $$ [Hm Hk]
  · iframe
  ihave %Hlt := threadToks_lt (m + k) $$ Hmk
  icases (threadToks_add m k).1 $$ Hmk with ⟨Hm, Hk⟩
  imod HcloseS $$ [HwgoS HrunS Hk HctrS] with -
  · inext
    unfold wgsWgInv
    iexists ctrS, k
    iframe
  imodintro
  iframe Hm
  isplitr
  · ipureintro; omega
  iapply wcj_toks_receipts γS b $$ Hr

/-- **A fresh local join** (`var wg sync.WaitGroup`), lending to the stream's wait group `swg`. -/
theorem wcj_init (wg swg : Loc) (γS : WgsWgNames) (Hb : threadBound GF ≤ 2 ^ 31) :
    typedPointsto (GF := GF) wg (zero_val sync.WaitGroup) (DFrac.own 1) ∗ isWgsWg swg γS ⊢
      |={⊤}=> sync.tokJoin.ownAdder wcjN (wcjL γS) wg 0 iprop(True) := by
  iintro ⟨Hwg, #HwgsS⟩
  imod sync.init_WaitGroup (wcjN.@"wg") wg $$ Hwg with ⟨%γwg, #His, Hctr, Hwait⟩
  ihave #Hlaw := wcj_law swg γS $$ HwgsS
  iapply sync.tokJoin.init wcjN (wcjL γS) wg γwg ⊤ Hb
  iframe #
  iframe

/-! ## A goroutine adding to the stream's wait group -/

/-- **`w.wg.Add(1)` by a goroutine of the local join** (a token of the shared adder): its slot's
thread token is lent to the stream's wait group, whose new running token takes the slot's place
(the goroutine's right becomes `ownLent`). -/
theorem wp_wgsWg_Add_wcj (wg swg : Loc) (γS : WgsWgNames) (γh : WgsShNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.tokJoin.ownDone wcjN (wcjL γS) wg P ∗
        wgsShareTok swg γS γh }}
      (App (Val (swg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); sync.tokJoin.ownLent wcjN (wcjL γS) wg P ∗ wgsShareTok swg γS γh }} := by
  iintro %Φ ⟨#Hsync, Hd, Ht⟩ HΦ
  unfold wgsShareTok
  icases Ht with ⟨#HwgsS, #HinvSh, Hsh_tok, %Hb⟩
  ihave #HwgsS2 := HwgsS
  iunfold isWgsWg at HwgsS2
  icases HwgsS2 with ⟨#HwgS, #HinvS⟩
  iapply sync.WaitGroup.wp_Add swg (W64 1) γS.γwg wgsWgWN $$ [] [Hd Hsh_tok HΦ]
  · iframe #
  iinv HinvS with HiS HcloseS
  iinv HinvSh with HiSh HcloseSh
  have HE : (↑(wcjN.@"inv") : CoPset) ⊆ (⊤ \ ↑wgsWgCN) \ ↑wgsWgSN := by solve_ndisj
  imod sync.tokJoin.lend_acc wcjN (wcjL γS) wg P _ HE $$ Hd with ⟨Htok, Hclose⟩
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
  imod Hclose $$ Hrtok with Hl
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
  iframe Hl
  iframe HwgsS HinvSh Hsh_tok
  ipureintro; exact Hb

/-- **The inner `go` statement of a goroutine of the local join** (after `wp_wgsWg_Add_wcj`): at
the fork, the stream's running token leaves the slot for the new goroutine and the fork's fresh
thread token takes its place (the goroutine's right is `ownDone` again). -/
theorem wp_wcj_fork (wg swg : Loc) (γS : WgsWgNames) (P : IProp GF) (e : Expr)
    (Φ : val → IProp GF) :
    sync.tokJoin.ownLent wcjN (wcjL γS) wg P ∗ isWgsWg swg γS ∗
      ▷ (wgsWgDone swg -∗ WP e {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) ∗
      ▷ (sync.tokJoin.ownDone wcjN (wcjL γS) wg P -∗ Φ #()) ⊢
    WP (Fork e) {{ Φ }} := by
  iintro ⟨Hl, #HwgsS, He, HΦ⟩
  iapply wp_fork_tok_upd
  inext
  iintro Htok -
  have HE : (↑(wcjN.@"inv") : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  imod sync.tokJoin.unlend_acc wcjN (wcjL γS) wg P ⊤ HE $$ Hl with ⟨Hrtok, Hclose⟩
  imod Hclose $$ Htok with Hd
  imodintro
  isplitl [He Hrtok]
  · iapply He
    unfold wgsWgDone
    iexists γS
    iframe HwgsS Hrtok
  iapply HΦ $$ Hd

end lemmas

end client
end EtcdGrove
end Perennial
