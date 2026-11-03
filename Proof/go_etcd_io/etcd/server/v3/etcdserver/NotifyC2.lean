/-
**`notifyc` of a snapshot batch: two sends, two receives** (2026-10-31, SNAPSHOT-SORRY #3). For a
`Ready` with a snapshot, `raftNode.start` sends on its fresh capacity-`1` `notifyc` twice: once the
snapshot is saved and synced (raft.go, before `ApplySnapshot`), and once more before `Advance` (the
follower's after `processMessages`, the leader's in the `else` branch; a snapshot `Ready` commits no
entries, so no conf-change send). The apply thread receives twice: `applySnapshot`'s
`<-toApply.notifyc` (it waits for the snapshot on disk) and `applyAll`'s `<-apply.notifyc`.
`NotifyC.lean`'s protocol has one receive; this one counts both sides.

Ghost state: the sender's count of sends `n` (`notifySnd`, as `NotifyC.lean`'s) and the receiver's
count of receives `k` (`notifyRcvN`), each a `dghostVar` in halves. The buffer holds `n - k` values,
`k ≤ n ≤ k + 1 ≤ 3`; the `i`th send deposits `S i` (`S1`, `S2`), which the `i`th receive takes. The
second send at `(1, 0)` would make the buffer `[(), ()]`, which a capacity-`1` channel's state
refutes (`ownChan_cap_valid`). Lean-first (no Rocq counterpart).
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
def notify2Match (S1 S2 : IProp GF) (s : ChanState Unit) : Nat → Nat → IProp GF
  | 0, 0 => iprop(⌜s = .Buffered []⌝)
  | 1, 0 => iprop(⌜s = .Buffered [()]⌝ ∗ S1)
  | 1, 1 => iprop(⌜s = .Buffered []⌝)
  | 2, 1 => iprop(⌜s = .Buffered [()]⌝ ∗ S2)
  | 2, 2 => iprop(⌜s = .Buffered []⌝)
  | _, _ => iprop(False)

/-- The invariant of a two-receive `notifyc`. -/
def notify2Inv (γ : NotifyNames) (S1 S2 : IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState Unit) (n k : Nat),
    ownChan γ.ch Unit s ∗ dghostVar γ.snd (DFrac.own (1 : Qp).half) n ∗
    dghostVar γ.rcv (DFrac.own (1 : Qp).half) k ∗ notify2Match S1 S2 s n k)

/-- **A two-receive `notifyc`** (persistent): a capacity-`1` channel with the invariant, the `i`th
send depositing `Si` for the `i`th receive. -/
def isNotify2 (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) : IProp GF :=
  iprop(isChan ch γ.ch Unit ∗ ⌜sint.Z γ.ch.chanCap = 1⌝ ∗ inv nroot (notify2Inv γ S1 S2))

instance isNotify2_persistent (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) :
    Persistent (isNotify2 γ ch S1 S2) := by
  unfold isNotify2; infer_instance

/-- The receiver's count of receives. -/
def notifyRcvN (γ : NotifyNames) (k : Nat) : IProp GF :=
  dghostVar γ.rcv (DFrac.own (1 : Qp).half) k

theorem is_notify2_is_chan (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) :
    ⊢ isNotify2 γ ch S1 S2 -∗ isChan ch γ.ch Unit := by
  unfold isNotify2
  iintro ⟨$, -⟩

/-- A fresh capacity-`1` channel as a two-receive `notifyc`, for any `S1`, `S2`. -/
theorem start_notify2 (S1 S2 : IProp GF) (ch : Loc) (γc : ChanNames)
    (Hcap : sint.Z γc.chanCap = 1) :
    ⊢ isChan ch γc Unit -∗ ownChan γc Unit (.Buffered []) ={⊤}=∗
      ∃ γ : NotifyNames, ⌜γ.ch = γc⌝ ∗ isNotify2 γ ch S1 S2 ∗ notifySnd γ 0 ∗ notifyRcvN γ 0 := by
  iintro #Hch Hoc
  imod dghostVar_alloc (0 : Nat) with ⟨%gs, Hs⟩
  icases dghostVar_halves' _ _ $$ Hs with ⟨HsI, HsF⟩
  imod dghostVar_alloc (0 : Nat) with ⟨%gr, Hr⟩
  icases dghostVar_halves' _ _ $$ Hr with ⟨HrI, HrF⟩
  imod inv_alloc nroot ⊤ (notify2Inv ⟨γc, gs, gr⟩ S1 S2) $$ [Hoc HsI HrI] with #Hinv
  · inext
    unfold notify2Inv
    iexists .Buffered [], 0, 0
    iframe
    simp only [notify2Match]
    itrivial
  imodintro
  iexists ⟨γc, gs, gr⟩
  unfold isNotify2 notifySnd notifyRcvN
  iframe
  iframe #
  isplit <;> ipureintro <;> first | rfl | exact Hcap

/-- **The first send**, depositing `S1`: from no send to one. -/
theorem notify2_send1_au (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 -∗ isNotify2 γ ch S1 S2 -∗ notifySnd γ 0 -∗ S1 -∗ ▷ (notifySnd γ 1 -∗ Φ) -∗
      sendAu γ.ch () Φ := by
  unfold isNotify2 sendAu notifySnd
  iintro Hlc ⟨#Hch, %Hcap, #Hinv⟩ Hs HS HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notify2Inv
  icases Hi with ⟨%s, %n, %k, Hoc, HsI, HrI, Hm⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hs HsI
  subst Hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases k with _ | k
  · simp only [notify2Match]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (1 : Nat) _ _ _ $$ Hs HsI with ⟨Hs, HsI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI HS] with -
    · inext
      iexists .Buffered [()], 1, 0
      iframe
      simp only [notify2Match]
      iframe
    imodintro
    iapply HΦ $$ Hs
  · simp only [notify2Match]
    iexfalso
    iexact Hm

/-- **The second send**, depositing `S2`: from one send to two, once the receiver has received the
first, which a capacity-`1` channel ensures. -/
theorem notify2_send2_au (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) (Φ : IProp GF) :
    ⊢ £ 1 -∗ isNotify2 γ ch S1 S2 -∗ notifySnd γ 1 -∗ S2 -∗ ▷ (notifySnd γ 2 -∗ Φ) -∗
      sendAu γ.ch () Φ := by
  unfold isNotify2 sendAu notifySnd
  iintro Hlc ⟨#Hch, %Hcap, #Hinv⟩ Hs HS HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notify2Inv
  icases Hi with ⟨%s, %n, %k, Hoc, HsI, HrI, Hm⟩
  ihave %Hn := dghostVar_agree _ _ _ _ _ $$ Hs HsI
  subst Hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases k with _ | _ | k
  · -- the first value still buffered: the second would exceed the capacity
    simp only [notify2Match]
    icases Hm with ⟨%Hs0, -⟩
    subst Hs0
    iexists .Buffered [()]
    iframe Hoc
    dsimp only
    iintro Hoc
    ihave %Hv := ownChan_cap_valid _ _ _ $$ Hoc
    exfalso
    simp only [ChanCapValid, List.singleton_append, List.length_cons, List.length_nil] at Hv
    omega
  · simp only [notify2Match]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (2 : Nat) _ _ _ $$ Hs HsI with ⟨Hs, HsI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI HS] with -
    · inext
      iexists .Buffered [()], 2, 1
      iframe
      simp only [notify2Match]
      iframe
    imodintro
    iapply HΦ $$ Hs
  · simp only [notify2Match]
    iexfalso
    iexact Hm

/-- **The first receive**, taking `S1`: it waits for the first value. -/
theorem notify2_recv1_au (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ £ 1 -∗ isNotify2 γ ch S1 S2 -∗ notifyRcvN γ 0 -∗
      ▷ (notifyRcvN γ 1 -∗ S1 -∗ Φ () true) -∗ recvAu γ.ch Unit Φ := by
  unfold isNotify2 recvAu notifyRcvN
  iintro Hlc ⟨#Hch, %Hcap, #Hinv⟩ Hr HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notify2Inv
  icases Hi with ⟨%s, %n, %k, Hoc, HsI, HrI, Hm⟩
  ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hr HrI
  subst Hk
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases n with _ | _ | n
  · -- nothing sent yet: the buffer empty, the receive waits
    simp only [notify2Match]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
  · simp only [notify2Match]
    icases Hm with ⟨%Hs0, HS⟩
    subst Hs0
    iexists .Buffered [()]
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (1 : Nat) _ _ _ $$ Hr HrI with ⟨Hr, HrI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI] with -
    · inext
      iexists .Buffered [], 1, 1
      simp only [notify2Match]
      iframe
    imodintro
    iapply HΦ $$ Hr HS
  · simp only [notify2Match]
    iexfalso
    iexact Hm

/-- **The second receive**, taking `S2`: it waits for the second value. -/
theorem notify2_recv2_au (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ £ 1 -∗ isNotify2 γ ch S1 S2 -∗ notifyRcvN γ 1 -∗
      ▷ (notifyRcvN γ 2 -∗ S2 -∗ Φ () true) -∗ recvAu γ.ch Unit Φ := by
  unfold isNotify2 recvAu notifyRcvN
  iintro Hlc ⟨#Hch, %Hcap, #Hinv⟩ Hr HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold notify2Inv
  icases Hi with ⟨%s, %n, %k, Hoc, HsI, HrI, Hm⟩
  ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hr HrI
  subst Hk
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases n with _ | _ | _ | n
  · simp only [notify2Match]
    iexfalso
    iexact Hm
  · -- one sent and received: the buffer empty, the receive waits
    simp only [notify2Match]
    icases Hm with %Hs0
    subst Hs0
    iexists .Buffered []
    iframe Hoc
  · simp only [notify2Match]
    icases Hm with ⟨%Hs0, HS⟩
    subst Hs0
    iexists .Buffered [()]
    iframe Hoc
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (2 : Nat) _ _ _ $$ Hr HrI with ⟨Hr, HrI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsI HrI] with -
    · inext
      iexists .Buffered [], 2, 2
      simp only [notify2Match]
      iframe
    imodintro
    iapply HΦ $$ Hr HS
  · simp only [notify2Match]
    iexfalso
    iexact Hm

theorem wp_notify2_send1 {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) :
    {{ isNotify2 γ ch S1 S2 ∗ notifySnd γ 0 ∗ S1 }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #()))
    {{ RET #(); notifySnd γ 1 }} := by
  iintro %Φ ⟨#Hn, Hs, HS⟩ HΦ
  ihave #Hch := is_notify2_is_chan γ ch S1 S2 $$ Hn
  iapply chan.wp_send ch () γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notify2_send1_au γ ch S1 S2 (Φ #()) $$ Hlc1 Hn Hs HS HΦ

theorem wp_notify2_send2 {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) :
    {{ isNotify2 γ ch S1 S2 ∗ notifySnd γ 1 ∗ S2 }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #()))
    {{ RET #(); notifySnd γ 2 }} := by
  iintro %Φ ⟨#Hn, Hs, HS⟩ HΦ
  ihave #Hch := is_notify2_is_chan γ ch S1 S2 $$ Hn
  iapply chan.wp_send ch () γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notify2_send2_au γ ch S1 S2 (Φ #()) $$ Hlc1 Hn Hs HS HΦ

theorem wp_notify2_receive1 {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) :
    {{ isNotify2 γ ch S1 S2 ∗ notifyRcvN γ 0 }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ RET (PairV #() #true); notifyRcvN γ 1 ∗ S1 }} := by
  iintro %Φ ⟨#Hn, Hr⟩ HΦ
  ihave #Hch := is_notify2_is_chan γ ch S1 S2 $$ Hn
  iapply chan.wp_receive ch γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notify2_recv1_au γ ch S1 S2 (fun v ok => Φ (PairV #v #ok)) $$ Hlc1 Hn Hr
  inext
  iintro Hr HS
  iapply HΦ
  iframe

theorem wp_notify2_receive2 {t : go.GoType} [IntoValTyped (GF := GF) Unit t]
    (γ : NotifyNames) (ch : Loc) (S1 S2 : IProp GF) :
    {{ isNotify2 γ ch S1 S2 ∗ notifyRcvN γ 1 }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ RET (PairV #() #true); notifyRcvN γ 2 ∗ S2 }} := by
  iintro %Φ ⟨#Hn, Hr⟩ HΦ
  ihave #Hch := is_notify2_is_chan γ ch S1 S2 $$ Hn
  iapply chan.wp_receive ch γ.ch $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply notify2_recv2_au γ ch S1 S2 (fun v ok => Φ (PairV #v #ok)) $$ Hlc1 Hn Hr
  inext
  iintro Hr HS
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
