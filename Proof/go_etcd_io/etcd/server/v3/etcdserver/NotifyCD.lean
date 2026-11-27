/-
**`notifyc` with a deposit at the first send** (T10s3b B3, 2026-11-27). `NotifyC.lean`'s protocol (one
receive, two sends, the receiver depositing `R` for the second send), where the first send also
deposits a resource `Q` that the receive takes. For the entries' `Ready`: raft's first send on
`notifyc` comes after its *enter* (the WAL `Save`, raft.go), where the raft loop has L2's law at the
entered durable state (`rnLeadLaw`), so it can hand the apply thread the batch's replay job
(`rnReplayJob`), which the payload sent earlier on `applyc` cannot carry.

The states as `NotifyC.lean`'s: `(0, false)` empty; `(1, false)` the first value buffered, `Q`
deposited; `(1, true)` received, `Q` taken, `R` deposited; `(2, true)` the second value buffered, `R`
taken. `isNotifyD γ ch Q R` holds of an invariant at any `Q0` with `□ (Q0 -∗ Q)`, so `Q` can be weakened
(`isNotifyD_weaken`: the apply side restates the job over the apply job's copy of the field).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NotifyC

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The state-dependent part of the invariant (see the file header). -/
def notifyDMatch (Q R : IProp GF) (s : ChanState Unit) : Nat → Bool → IProp GF
  | 0, false => iprop(⌜s = .Buffered []⌝)
  | 1, false => iprop(⌜s = .Buffered [()]⌝ ∗ Q)
  | 1, true => iprop(⌜s = .Buffered []⌝ ∗ R)
  | 2, true => iprop(⌜s = .Buffered [()]⌝)
  | _, _ => iprop(False)

/-- The invariant of a deposit-first `notifyc`. -/
def notifyDInv (γ : NotifyNames) (Q R : IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState Unit) (n : Nat) (b : Bool),
    ownChan γ.ch Unit s ∗ dghostVar γ.snd (DFrac.own (1 : Qp).half) n ∗
    dghostVar γ.rcv (DFrac.own (1 : Qp).half) b ∗ notifyDMatch Q R s n b)

/-- **A deposit-first `notifyc`** (persistent): a capacity-`1` channel whose first send deposits `Q`,
which the receive takes, and whose receive deposits `R`, which the second send takes. -/
def isNotifyD (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) : IProp GF :=
  iprop(isChan ch γ.ch Unit ∗ ⌜sint.Z γ.ch.chanCap = 1⌝ ∗ inv nroot (notifyDInv γ Q R))

instance isNotifyD_persistent (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) :
    Persistent (isNotifyD γ ch Q R) := by
  unfold isNotifyD; infer_instance

/-- **The receiver's view** (persistent): a deposit-first `notifyc` whose first send's deposit gives
(at least) `Q`. -/
def isNotifyDR (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) : IProp GF :=
  iprop(∃ Q0 : IProp GF, □ (Q0 -∗ Q) ∗ isNotifyD γ ch Q0 R)

instance isNotifyDR_persistent (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) :
    Persistent (isNotifyDR γ ch Q R) := by
  unfold isNotifyDR; infer_instance

theorem is_notifyD_is_chan (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) :
    ⊢ isNotifyD γ ch Q R -∗ isChan ch γ.ch Unit := by
  unfold isNotifyD
  iintro ⟨$, -⟩

/-- The receiver's view of the sender's, its deposit weakened. -/
theorem isNotifyDR_of (γ : NotifyNames) (ch : Loc) (Q Q' R : IProp GF) :
    ⊢ isNotifyD γ ch Q R -∗ □ (Q -∗ Q') -∗ isNotifyDR γ ch Q' R := by
  iintro #Hn #Hw
  unfold isNotifyDR
  iexists Q
  iframe Hw Hn

/-- A fresh capacity-`1` channel as a deposit-first `notifyc`, for any `Q`, `R`. -/
theorem start_notifyD (Q R : IProp GF) (ch : Loc) (γc : ChanNames) (Hcap : sint.Z γc.chanCap = 1) :
    ⊢ isChan ch γc Unit -∗ ownChan γc Unit (.Buffered []) ={⊤}=∗
      ∃ γ : NotifyNames, ⌜γ.ch = γc⌝ ∗ isNotifyD γ ch Q R ∗ notifySnd γ 0 ∗ notifyRcv γ := by
  iintro #Hch Hoc
  imod dghostVar_alloc (0 : Nat) with ⟨%gs, Hs⟩
  icases dghostVar_halves' _ _ $$ Hs with ⟨HsI, HsF⟩
  imod dghostVar_alloc false with ⟨%gr, Hr⟩
  icases dghostVar_halves' _ _ $$ Hr with ⟨HrI, HrF⟩
  imod inv_alloc nroot ⊤ (notifyDInv ⟨γc, gs, gr⟩ Q R) $$ [Hoc HsI HrI] with #Hinv
  · inext
    unfold notifyDInv
    iexists .Buffered [], 0, false
    iframe
    simp only [notifyDMatch]
    itrivial
  imodintro
  iexists ⟨γc, gs, gr⟩
  unfold isNotifyD notifySnd notifyRcv
  iframe
  iframe #
  isplit <;> ipureintro <;> first | rfl | exact Hcap

/-- **The first send**: from no send to one, depositing `Q`. -/
theorem notifyD_send1_au (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 -∗ isNotifyD γ ch Q R -∗ notifySnd γ 0 -∗ Q -∗ ▷ (notifySnd γ 1 -∗ Φ) -∗
      sendAu γ.ch () Φ := by
  unfold isNotifyD sendAu notifySnd
  iintro Hlc ⟨#Hch, %Hcap, #Hinv⟩ Hs HQ HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notifyDInv
  icases Hi with ⟨%s, %n, %b, Hoc, HsI, HrI, Hm⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hs HsI
  subst Hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  cases b
  · simp only [notifyDMatch]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (1 : Nat) _ _ _ $$ Hs HsI with ⟨Hs, HsI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI HQ] with -
    · inext
      iexists .Buffered [()], 1, false
      simp only
      iframe
    imodintro
    iapply HΦ $$ Hs
  · simp only [notifyDMatch]
    iexfalso
    iexact Hm

/-- **The second send**: from one send to two, once the receiver has received, which a
capacity-`1` channel ensures; it claims `R`. -/
theorem notifyD_send2_au (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isNotifyD γ ch Q R -∗ notifySnd γ 1 -∗ ▷ (notifySnd γ 2 ∗ R -∗ Φ) -∗
      sendAu γ.ch () Φ := by
  unfold isNotifyD sendAu notifySnd
  iintro ⟨Hlc, -⟩ ⟨#Hch, %Hcap, #Hinv⟩ Hs HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notifyDInv
  icases Hi with ⟨%s, %n, %b, Hoc, HsI, HrI, Hm⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hs HsI
  subst Hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  cases b
  · -- the first value still buffered: the second would exceed the capacity
    simp only [notifyDMatch]
    icases Hm with ⟨%Hs0, HQ⟩
    subst Hs0
    iexists .Buffered [()]
    iframe Hoc
    dsimp only
    iintro Hoc
    ihave %Hv := ownChan_cap_valid _ _ _ $$ Hoc
    exfalso
    simp only [ChanCapValid, List.singleton_append, List.length_cons, List.length_nil] at Hv
    omega
  · simp only [notifyDMatch]
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

/-- **The receive**: it waits for the first value, takes `Q` and deposits `R`. -/
theorem notifyD_recv_au (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) (Φ : Unit → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isNotifyD γ ch Q R -∗ notifyRcv γ -∗ R -∗ ▷ (Q -∗ Φ () true) -∗
      recvAu γ.ch Unit Φ := by
  unfold isNotifyD recvAu notifyRcv
  iintro ⟨Hlc, -⟩ ⟨#Hch, %Hcap, #Hinv⟩ Hr HR HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notifyDInv
  icases Hi with ⟨%s, %n, %b, Hoc, HsI, HrI, Hm⟩
  ihave %Hb := dghostVar_agree _ _ _ _ _ $$ Hr HrI
  subst Hb
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases n with _ | _ | n
  · -- nothing sent yet: the buffer empty, the receive waits
    simp only [notifyDMatch]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
  · simp only [notifyDMatch]
    icases Hm with ⟨%Hs0, HQ⟩
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
    iapply HΦ $$ HQ
  · simp only [notifyDMatch]
    iexfalso
    iexact Hm

theorem wp_notifyD_send1 {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) :
    {{ isNotifyD γ ch Q R ∗ notifySnd γ 0 ∗ Q }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #()))
    {{ RET #(); notifySnd γ 1 }} := by
  iintro %Φ ⟨#Hn, Hs, HQ⟩ HΦ
  ihave #Hch := is_notifyD_is_chan γ ch Q R $$ Hn
  iapply chan.wp_send ch () γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notifyD_send1_au γ ch Q R (Φ #()) $$ Hlc1 Hn Hs HQ HΦ

/-- The receive, through the receiver's view (`isNotifyDR`): it returns `Q`. -/
theorem wp_notifyD_receive {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (Q R : IProp GF) :
    {{ isNotifyDR γ ch Q R ∗ notifyRcv γ ∗ R }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ RET (PairV #() #true); Q }} := by
  iintro %Φ ⟨#Hn, Hr, HR⟩ HΦ
  iunfold isNotifyDR at Hn
  icases Hn with ⟨%Q0, #Hw, #Hn⟩
  ihave #Hch := is_notifyD_is_chan γ ch Q0 R $$ Hn
  iapply chan.wp_receive ch γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notifyD_recv_au γ ch Q0 R (fun v ok => Φ (PairV #v #ok)) $$ [$Hlc1 $Hlc2] Hn Hr HR
  inext
  iintro HQ
  iapply HΦ
  iapply Hw $$ HQ

end proof

end EtcdGrove
end Perennial
