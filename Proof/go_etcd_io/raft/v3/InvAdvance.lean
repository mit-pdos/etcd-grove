/-
(D19i part 1, 2026-10-18) The `advancec` protocol's lemmas (`advInv`, `InvNode.lean`): the
rendezvous at which the floor is raised (`advance_complete`), `run`'s receive (`adv_recv_au`),
the driver's send (`adv_send_au`), and the protocol's allocation (`adv_start`). The receive and
the send follow Perennial's handshake idiom (`Handshake.lean`'s `handshake_receive_au`,
`handshake_send_au`) over the channel's states, with the payloads `advInv` gives each state.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeChan
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std OFE go_etcd_io.raft.v3

section adv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The rendezvous** (whichever side meets the other): the driver's append receipt absorbed,
the floor raised to the committed log `run` handed out (`ownRawNode_raise_floor`), which the
driver's lower bound `ds` is a prefix of; its witness, and `run`'s node after it. (D22 S-d4,
2026-10-21) For the `Ready`'s loan `L` (`run`'s record names it): after a snapshot `Ready` the
receipt is the loan's (`snapReceipt`), which passes to `run` for `RawNode.Advance` (`advRet`'s
`loanRet`), and no floor is raised; after one without, the floor is raised also when a snapshot
was restored since (`RNState.psnap`; D22 S-d4 item 3, the storage's extent `StorExtOk`). -/
theorem advance_complete (γ : NodeNames) (rn : Loc) (id : w64) (ds : List EntryM)
    (L : Option SnapLoan) :
    ⊢ dlvLb (GF := GF) γ ds -∗ advDep γ rn id -∗ advanceP γ L ==∗
      advRet γ rn id ∗ reqWit γ (reqOf L ds) := by
  iintro #Hlb Hdep HP
  iunfold advDep at Hdep
  icases Hdep with ⟨%rs, %d, %ce, Hrn, #Htlb, Hcfg, Hrof, %Hrs⟩
  obtain ⟨Hstor, Hunst, Hdel⟩ := Hrs
  iunfold advanceP at HP
  icases HP with ⟨%d', %ce', %es', %p', Hdlv, Hrof', Hrcpt, %ca_d, #Hcamlb, %HA⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hrof Hrof'
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl, rfl, rfl, HL⟩ := Heq
  -- the driver's lower bound, against `run`'s authority
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, Hcfg⟩
  iunfold dlvLb at Hlb
  ihave %Hpfx := mono_list_auth_lb_valid _ _ _ _ $$ Hdlm Hlb
  obtain ⟨Hmd, Hcap, Hflw, Hsn, Hsi, Hpre⟩ := Hm0
  ihave Hcfg : runCfg γ rs $$ [Hdlm Hcfg]
  · iunfold runCfg
    iframe Hdlm Hcfg
    ipureintro; exact ⟨Hmd, Hcap, Hflw, Hsn, Hsi, Hpre⟩
  cases L with
  | none =>
    have Hsl : rs.slent = none := HL
    rw [rsDlv_none Hsl] at Hpfx
    rw [Hsl]
    simp only [advReceipt, reqOf, dlvAfter, reqWit] at HA ⊢
    -- the receipt: the `Ready`'s entries are appended
    ihave Hrcpt' : appendReceipt rs.storage rs.unpersisted $$ [Hrcpt]
    · rw [Hstor]; iexact Hrcpt
    imod ownRawNode_appended γ.raft rn id rs Hsl $$ Hrn Hrcpt' with Hrn
    imod ownRawNode_raise_floor γ.raft rn id { rs with unpersisted := [] } rfl Hsl $$ Hrn
      with ⟨Hrn, %x, %Hx, #Hfw⟩
    imodintro
    isplitr [Hfw]
    · iunfold advRet
      iexists { { rs with unpersisted := [] } with flw := true }, ca_d
      iframe Hrn Htlb Hcamlb
      isplitl [Hcfg]
      · iapply (runCfg_congr (GF := GF) γ (rs := rs)
          (rs' := { { { rs with unpersisted := [] } with flw := true } with flw := false })
          rfl rfl rfl Hflw.symm rfl rfl rfl) $$ Hcfg
      isplitl [Hdlv]
      · simp only [rsDlv, Hsl]; rw [Hdel]; iexact Hdlv
      isplitl [Hrof Hrof']
      · iexists _
        iframe Hrof Hrof'
      isplitr
      · simp only [loanRet, Hsl]; iempintro
      ipureintro
      exact ⟨Hstor, Hunst, fun _ => rfl, fun h => by simp only; rw [Hdel]; exact HA h⟩
    iexists x
    isplitr
    · simp only; rw [← Hstor]; iexact Hfw
    ipureintro
    have := Hpfx.2.length_le
    simp only at Hx
    omega
  | some l =>
    have Hsl : rs.slent = some l := HL
    rw [Hsl]
    simp only [advReceipt, reqOf, dlvAfter, reqWit] at HA ⊢
    -- a loan: the node takes snapshots, so the static mode
    have Hsin : γ.snapIn = true := by
      cases h : γ.snapIn
      · rw [(Hsn h).2] at Hsl; cases Hsl
      · rfl
    have Hst := (Hsi Hsin).2
    imodintro
    isplitl
    · iunfold advRet
      iexists rs, ca_d
      iframe Hrn Htlb Hcamlb
      isplitl [Hcfg]
      · iapply (runCfg_congr (GF := GF) γ (rs := rs) (rs' := { rs with flw := false })
          rfl rfl rfl Hflw.symm rfl rfl rfl) $$ Hcfg
      isplitl [Hdlv]
      · simp only [rsDlv, Hsl]; iexact Hdlv
      isplitl [Hrof Hrof']
      · iexists _
        iframe Hrof Hrof'
      isplitl [Hrcpt]
      · simp only [loanRet, Hsl]; rw [Hstor]; iexact Hrcpt
      ipureintro
      have H1 : rs.slent = none → rs.unpersisted = [] := fun h => by rw [Hsl] at h; cases h
      have H2 : γ.mode.isDyn = true → NoConfIn rs.delivered ca_d rs.delivered.length :=
        fun h => by rw [Hst] at h; cases h
      first | exact ⟨Hstor, Hunst, H1, H2⟩ | exact ⟨Hunst, H1, H2⟩ | exact ⟨H1, H2⟩ | exact H2
    itrivial

/-- **`run`'s receive on `advancec`**, with its node at the rendezvous (`advDep`): back with
the node after it (`advRet`). -/
theorem adv_recv_au (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isAdvChan γ rn id ch -∗ advDep γ rn id -∗ ▷ (advRet γ rn id -∗ Φ () true) -∗
      recvAu γ.advancec Unit Φ := by
  unfold isAdvChan recvAu
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hchan, #Hinv⟩ Hdep Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc1 Hi with Hi
  unfold advInv
  icases Hi with ⟨%s, Hch, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨_, _⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H Hdep] with -
    · inext
      iexists .RcvPending
      iframe
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hch, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      iintro Hid
      imod Hmask with -
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ Hi
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case SndPending =>
    iintro H
    imod Hmask with -
    icases Hi with ⟨%L, HP, %ds, Hreq, #Hlb⟩
    imod advance_complete γ rn id ds L $$ Hlb Hdep HP with ⟨Hret, #Hw⟩
    imod Hclose $$ [H Hreq] with -
    · inext
      iexists .RcvCommit
      iframe H
      iexists reqOf L ds
      iframe Hreq Hw
    imodintro
    iapply Hau $$ Hret
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- **The driver's send on `advancec`** (`node.Advance`), with its payload for its `Ready`'s loan
`L`, its lower bound `ds` on the committed log and its request: back with `run`'s answer for `ds`
(`reqWit`: the floor's witness after a `Ready` without a snapshot, D22 S-d4). -/
theorem adv_send_au (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) (ds : List EntryM)
    (L : Option SnapLoan) (q0 : Option Nat) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isAdvChan γ rn id ch -∗ advanceP γ L -∗ dlvLb γ ds -∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) q0 -∗ dghostVar γ.req (DFrac.own (1 : Qp).half) q0 -∗
      ▷ (reqWit γ (reqOf L ds) -∗
          (∃ q : Option Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) q ∗
            dghostVar γ.req (DFrac.own (1 : Qp).half) q) -∗ Φ) -∗
      sendAu γ.advancec () Φ := by
  unfold isAdvChan sendAu
  iintro ⟨Hlc1, Hlc2, Hlc3⟩ ⟨#Hchan, #Hinv⟩ HP #Hlb Hr1 Hr2 Hau
  imod dghostVar_update_halves (reqOf L ds) γ.req q0 q0 $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc1 Hi with Hi
  unfold advInv
  icases Hi with ⟨%s, Hch, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with b | _ | _ | _ | _ | _ | d
  all_goals dsimp only
  case Idle =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H HP Hr1] with -
    · inext
      iexists .SndPending ()
      isplitl [H]
      · iexact H
      iexists L
      isplitl [HP]
      · iexact HP
      iexists ds
      iframe Hr1 Hlb
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑advN) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hch, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    case RcvCommit =>
      iintro Hid
      imod Hmask with -
      icases Hi with ⟨%q, Hr1, #Hw⟩
      ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hr1 Hr2
      subst Hk
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ [] [Hr1 Hr2]
      · iexact Hw
      · iexists _; iframe Hr1 Hr2
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    iintro Hsd
    imod Hmask with -
    imod advance_complete γ rn id ds L $$ Hlb Hi HP with ⟨Hret, #Hw⟩
    imod Hclose $$ [Hsd Hret] with -
    · inext
      iexists .SndCommit ()
      iframe
    imodintro
    iapply Hau $$ [] [Hr1 Hr2]
    · iexact Hw
    · iexists _; iframe Hr1 Hr2
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- The protocol, on an idle channel. -/
theorem adv_start (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) :
    ⊢ isChan ch γ.advancec Unit -∗ ownChan γ.advancec Unit .Idle ={⊤}=∗ isAdvChan (GF := GF) γ rn id ch := by
  iintro #Hch Hchan
  unfold isAdvChan
  iframe Hch
  iapply inv_alloc
  inext
  unfold advInv
  iexists .Idle
  iframe

theorem isAdvChan_isChan (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) :
    ⊢ isAdvChan (GF := GF) γ rn id ch -∗ isChan ch γ.advancec Unit := by
  iintro H
  unfold isAdvChan
  icases H with ⟨$, -⟩

end adv

end EtcdGrove
end Perennial
