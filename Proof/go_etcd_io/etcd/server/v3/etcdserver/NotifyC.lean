/-
**`notifyc`, the raft loop's two sends** (D43 M3, 2026-10-25). `raftNode.start` makes a fresh
`notifyc := make(chan struct{}, 1)` for each `Ready`, hands it to the apply thread in the
`toApply`, and sends on it once; on a `Ready` that commits a conf change it sends a second time
before `Advance` (raft.go; the leader too since the fork's `goose-lean-leaderwait`). The apply
thread receives once, after `applyEntries` (`applyAll`'s `<-apply.notifyc`). With capacity `1`
the second send completes only once the first value was received, so it is the raft loop's sign
that the batch is applied: here the receiver deposits a resource `R` at its receive, which the
second send claims (raft's dynamic mode: the driver's configuration view, back for `Advance`).

The idiom is over the raw channel state (`ownChan`), since `Spsc` keeps no capacity. Ghost state:
the sender's count of sends `n` and the receiver's flag `b`, each a `dghostVar` in halves (the
invariant's and the side's). The states: `(0, false)` empty; `(1, false)` the first value
buffered; `(1, true)` received, the buffer empty, `R` deposited; `(2, true)` the second value
buffered, `R` taken. The second send at `(1, false)` would make the buffer `[(), ()]`, which a
capacity-`1` channel's state refutes (`ownChan_cap_valid`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- The names of a `notifyc`: the channel's, the sender's count, the receiver's flag. -/
structure NotifyNames where
  ch : ChanNames
  snd : GName
  rcv : GName

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The state-dependent part of the invariant (see the file header). -/
def notifyMatch (R : IProp GF) (s : ChanState Unit) : Nat → Bool → IProp GF
  | 0, false => iprop(⌜s = .Buffered []⌝)
  | 1, false => iprop(⌜s = .Buffered [()]⌝)
  | 1, true => iprop(⌜s = .Buffered []⌝ ∗ R)
  | 2, true => iprop(⌜s = .Buffered [()]⌝)
  | _, _ => iprop(False)

/-- The invariant of a `notifyc`. -/
def notifyInv (γ : NotifyNames) (R : IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState Unit) (n : Nat) (b : Bool),
    ownChan γ.ch Unit s ∗ dghostVar γ.snd (DFrac.own (1 : Qp).half) n ∗
    dghostVar γ.rcv (DFrac.own (1 : Qp).half) b ∗ notifyMatch R s n b)

/-- **A `notifyc`** (persistent): a capacity-`1` channel with the invariant, depositing `R`. -/
def isNotify (γ : NotifyNames) (ch : Loc) (R : IProp GF) : IProp GF :=
  iprop(isChan ch γ.ch Unit ∗ ⌜sint.Z γ.ch.chanCap = 1⌝ ∗ inv nroot (notifyInv γ R))

instance isNotify_persistent (γ : NotifyNames) (ch : Loc) (R : IProp GF) :
    Persistent (isNotify γ ch R) := by
  unfold isNotify; infer_instance

/-- The sender's count of sends. -/
def notifySnd (γ : NotifyNames) (n : Nat) : IProp GF :=
  dghostVar γ.snd (DFrac.own (1 : Qp).half) n

/-- The receiver's right to its one receive. -/
def notifyRcv (γ : NotifyNames) : IProp GF :=
  dghostVar γ.rcv (DFrac.own (1 : Qp).half) false

theorem is_notify_is_chan (γ : NotifyNames) (ch : Loc) (R : IProp GF) :
    ⊢ isNotify γ ch R -∗ isChan ch γ.ch Unit := by
  unfold isNotify
  iintro ⟨$, -⟩

theorem dghostVar_halves' {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    dghostVar (GF := GF) γ (DFrac.own 1) a ⊢
      dghostVar γ (DFrac.own (1 : Qp).half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half) a := by
  have h := dghostVar_split (GF := GF) γ a (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact wand_entails h

/-- A fresh capacity-`1` channel as a `notifyc`, for any `R`. -/
theorem start_notify (R : IProp GF) (ch : Loc) (γc : ChanNames) (Hcap : sint.Z γc.chanCap = 1) :
    ⊢ isChan ch γc Unit -∗ ownChan γc Unit (.Buffered []) ={⊤}=∗
      ∃ γ : NotifyNames, ⌜γ.ch = γc⌝ ∗ isNotify γ ch R ∗ notifySnd γ 0 ∗ notifyRcv γ := by
  iintro #Hch Hoc
  imod dghostVar_alloc (0 : Nat) with ⟨%gs, Hs⟩
  icases dghostVar_halves' _ _ $$ Hs with ⟨HsI, HsF⟩
  imod dghostVar_alloc false with ⟨%gr, Hr⟩
  icases dghostVar_halves' _ _ $$ Hr with ⟨HrI, HrF⟩
  imod inv_alloc nroot ⊤ (notifyInv ⟨γc, gs, gr⟩ R) $$ [Hoc HsI HrI] with #Hinv
  · inext
    unfold notifyInv
    iexists .Buffered [], 0, false
    iframe
    simp only [notifyMatch]
    itrivial
  imodintro
  iexists ⟨γc, gs, gr⟩
  unfold isNotify notifySnd notifyRcv
  iframe
  iframe #
  isplit <;> ipureintro <;> first | rfl | exact Hcap

/-- **The first send**: from no send to one. -/
theorem notify_send1_au (γ : NotifyNames) (ch : Loc) (R : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 -∗ isNotify γ ch R -∗ notifySnd γ 0 -∗ ▷ (notifySnd γ 1 -∗ Φ) -∗ sendAu γ.ch () Φ := by
  unfold isNotify sendAu notifySnd
  iintro Hlc ⟨#Hch, %Hcap, #Hinv⟩ Hs HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notifyInv
  icases Hi with ⟨%s, %n, %b, Hoc, HsI, HrI, Hm⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hs HsI
  subst Hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  cases b
  · simp only [notifyMatch]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (1 : Nat) _ _ _ $$ Hs HsI with ⟨Hs, HsI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI] with -
    · inext
      iexists .Buffered [()], 1, false
      iframe
      simp only
      itrivial
    imodintro
    iapply HΦ $$ Hs
  · simp only [notifyMatch]
    iexfalso
    iexact Hm

/-- **The second send**: from one send to two, once the receiver has received, which a
capacity-`1` channel ensures; it claims `R`. -/
theorem notify_send2_au (γ : NotifyNames) (ch : Loc) (R : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isNotify γ ch R -∗ notifySnd γ 1 -∗ ▷ (notifySnd γ 2 ∗ R -∗ Φ) -∗
      sendAu γ.ch () Φ := by
  unfold isNotify sendAu notifySnd
  iintro ⟨Hlc, -⟩ ⟨#Hch, %Hcap, #Hinv⟩ Hs HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notifyInv
  icases Hi with ⟨%s, %n, %b, Hoc, HsI, HrI, Hm⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hs HsI
  subst Hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  cases b
  · -- the first value still buffered: the second would exceed the capacity
    simp only [notifyMatch]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered [()]
    iframe Hoc
    dsimp only
    iintro Hoc
    ihave %Hv := ownChan_cap_valid _ _ _ $$ Hoc
    exfalso
    simp only [ChanCapValid, List.singleton_append, List.length_cons, List.length_nil] at Hv
    omega
  · simp only [notifyMatch]
    icases Hm with ⟨%Hs0, HR⟩
    subst Hs0
    iexists .Buffered []
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (2 : Nat) _ _ _ $$ Hs HsI with ⟨Hs, HsI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI] with -
    · inext
      iexists .Buffered [()], 2, true
      iframe
      simp only
      itrivial
    imodintro
    iapply HΦ $$ [Hs HR]
    iframe

/-- **The receive**, depositing `R`: it waits for the first value. -/
theorem notify_recv_au (γ : NotifyNames) (ch : Loc) (R : IProp GF) (Φ : Unit → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isNotify γ ch R -∗ notifyRcv γ -∗ R -∗ ▷ Φ () true -∗ recvAu γ.ch Unit Φ := by
  unfold isNotify recvAu notifyRcv
  iintro ⟨Hlc, -⟩ ⟨#Hch, %Hcap, #Hinv⟩ Hr HR HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notifyInv
  icases Hi with ⟨%s, %n, %b, Hoc, HsI, HrI, Hm⟩
  ihave %Hb := dghostVar_agree _ _ _ _ _ $$ Hr HrI
  subst Hb
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases n with _ | _ | n
  · -- nothing sent yet: the buffer empty, the receive waits
    simp only [notifyMatch]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
  · simp only [notifyMatch]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered [()]
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves true _ _ _ $$ Hr HrI with ⟨-, HrI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI HR] with -
    · inext
      iexists .Buffered [], 1, true
      simp only
      iframe
    imodintro
    iexact HΦ
  · simp only [notifyMatch]
    iexfalso
    iexact Hm

theorem wp_notify_send1 {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (R : IProp GF) :
    {{ isNotify γ ch R ∗ notifySnd γ 0 }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #()))
    {{ RET #(); notifySnd γ 1 }} := by
  iintro %Φ ⟨#Hn, Hs⟩ HΦ
  ihave #Hch := is_notify_is_chan γ ch R $$ Hn
  iapply chan.wp_send ch () γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notify_send1_au γ ch R (Φ #()) $$ Hlc1 Hn Hs HΦ

theorem wp_notify_receive {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (R : IProp GF) :
    {{ isNotify γ ch R ∗ notifyRcv γ ∗ R }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ RET (PairV #() #true); True }} := by
  iintro %Φ ⟨#Hn, Hr, HR⟩ HΦ
  ihave #Hch := is_notify_is_chan γ ch R $$ Hn
  iapply chan.wp_receive ch γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notify_recv_au γ ch R (fun v ok => Φ (PairV #v #ok)) $$ [$Hlc1 $Hlc2] Hn Hr HR
  inext
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
