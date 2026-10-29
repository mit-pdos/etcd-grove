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
    (L : Option SnapLoan) (x : Nat × CCState) :
    ⊢ dlvLb (GF := GF) γ ds -∗ advDep γ rn id -∗ advanceP γ L x ==∗
      advRet γ rn id ∗ reqWit γ (reqOf L ds) ∗ capAns γ (loanReq γ.mode L x) := by
  iintro #Hlb Hdep HP
  iunfold advDep at Hdep
  icases Hdep with ⟨%rs, %d, %ce, Hrn, #Htlb, Hcfg, Hrof, %Hrs⟩
  obtain ⟨Hstor, Hunst, Hdel⟩ := Hrs
  iunfold advanceP at HP
  icases HP with ⟨%d', %ce', %es', %p', Hdlv, Hrof', Hrcpt, Hpay, %ca_d, #Hcamlb, #HA⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hrof Hrof'
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl, rfl, rfl, HL⟩ := Heq
  -- the driver's lower bound, against `run`'s authority
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, %ca_r, Hcap_r, Hcam, %Hinv, #Hinv2⟩
  iunfold dlvLb at Hlb
  ihave %Hpfx := mono_list_auth_lb_valid _ _ _ _ $$ Hdlm Hlb
  ihave %Hcle := monoNatLbOwn_valid _ _ _ _ $$ Hcam Hcamlb
  obtain ⟨Hmd, Hcap, Hflw, Hsn, Hsi, Hpre⟩ := Hm0
  cases L with
  | none =>
    have Hsl : rs.slent = none := HL
    ihave Hcfg : runCfg γ rs $$ [Hdlm Hcap_r Hcam]
    · iunfold runCfg
      iframe Hdlm
      isplitr
      · ipureintro; exact ⟨Hmd, Hcap, Hflw, Hsn, Hsi, Hpre⟩
      iexists ca_r
      iframe Hcap_r Hcam Hinv2
      ipureintro; exact Hinv
    rw [rsDlv_none Hsl] at Hpfx
    rw [Hsl]
    simp only [advReceipt, reqOf, dlvAfter, reqWit, loanReq, Option.map_none, capAns]
    -- the receipt: the `Ready`'s entries are appended
    ihave Hrcpt' : appendReceipt rs.storage rs.unpersisted $$ [Hrcpt]
    · rw [Hstor]; iexact Hrcpt
    imod ownRawNode_appended γ.raft rn id rs Hsl $$ Hrn Hrcpt' with Hrn
    imod ownRawNode_raise_floor γ.raft rn id { rs with unpersisted := [] } rfl Hsl ds Hpfx.2
      $$ Hrn with ⟨Hrn, %x, %Hx, #Hfw, #Hts⟩
    imodintro
    isplitr [Hfw Hts]
    · iunfold advRet
      iexists { { rs with unpersisted := [] } with flw := true }, ca_d
      iframe Hrn Htlb Hcamlb
      isplitl [Hcfg]
      · iapply (runCfgR_of_runCfg (GF := GF) γ { { rs with unpersisted := [] } with flw := true }
          (.inl Hsl)).2
        iapply (runCfg_congr (GF := GF) γ (rs := rs)
          (rs' := { { { rs with unpersisted := [] } with flw := true } with flw := false })
          rfl rfl rfl Hflw.symm rfl rfl rfl) $$ Hcfg
      isplitl [Hdlv]
      · simp only [rsDlv, Hsl]; rw [Hdel]; iexact Hdlv
      isplitl [Hrof Hrof']
      · iexists _
        iframe Hrof Hrof'
      isplitr
      · simp only [loanRet, Hsl]; iempintro
      isplitr
      · ipureintro; exact ⟨Hstor, Hunst, fun _ => rfl⟩
      simp only; rw [Hdel]; iexact HA
    isplitr
    · iexists x
      isplitr [Hts]
      · simp only; rw [← Hstor]; iexact Hfw
      isplitr [Hts]
      · ipureintro
        have := Hpfx.2.length_le
        simp only at Hx
        omega
      simp only; rw [← Hstor]; iexact Hts
    itrivial
  | some l =>
    have Hsl : rs.slent = some l := HL
    have Hsin : γ.snapIn = true := by
      cases h : γ.snapIn
      · rw [(Hsn h).2] at Hsl; cases Hsl
      · rfl
    have Hns := Hsi Hsin
    have Hdp := Hpre l Hsl
    rw [Hsl]
    simp only [rsDlv, Hsl] at Hpfx Hcap Hinv ⊢
    simp only [advReceipt, reqOf, dlvAfter, reqWit, loanReq, Option.map_some, capAns, capPay]
    ihave %Hx := dghostVar_agree _ _ _ _ _ $$ Hcap_r Hpay
    subst Hx
    -- A1 at the `RawNode`'s committed log, from the driver's over the loan's
    ihave #HA' : undecFree γ.raft γ.mode rs.delivered ca_d rs.delivered.length $$ []
    · iapply undecFree_of_prefix γ.raft γ.mode Hdp (Nat.le_refl _)
      iapply undecFree_mono γ.raft γ.mode (Nat.le_refl _) Hdp.length_le
      iexact HA
    cases hd : γ.mode.isDyn with
    | false =>
      have Hst : rs.mode.isDyn = false := by rw [Hmd, hd]
      ihave #Hcl := monoNatLbOwn_get _ _ _ $$ Hcam
      ihave Hcfg : runCfg γ rs $$ [Hdlm Hcap_r Hcam]
      · iunfold runCfg
        simp only [rsDlv, Hsl]
        iframe Hdlm
        isplitr
        · ipureintro; exact ⟨Hmd, Hcap, Hflw, by rw [← Hsl]; exact Hsn, Hsi, by rw [← Hsl]; exact Hpre⟩
        iexists ca_r
        iframe Hcap_r Hcam Hinv2
        ipureintro; exact Hinv
      rw [loanCfg_static hd]
      imodintro
      isplitl [Hrn Hcfg Hdlv Hrof Hrof' Hrcpt]
      · iunfold advRet
        iexists rs, ca_d
        iframe Hrn Htlb Hcamlb
        isplitl [Hcfg]
        · iapply (runCfgR_of_runCfg (GF := GF) γ rs (.inr Hst)).2
          iapply (runCfg_congr (GF := GF) γ (rs := rs) (rs' := { rs with flw := false })
            rfl rfl rfl Hflw.symm rfl rfl rfl) $$ Hcfg
        isplitl [Hdlv]
        · simp only [rsDlv, Hsl]; iexact Hdlv
        isplitl [Hrof Hrof']
        · iexists _
          iframe Hrof Hrof'
        isplitl [Hrcpt]
        · simp only [loanRet, Hsl]; rw [Hstor]; iexact Hrcpt
        have H1 : rs.slent = none → rs.unpersisted = [] := fun h => by rw [Hsl] at h; cases h
        iframe HA'
        ipureintro; exact ⟨Hstor, Hunst, H1⟩
      isplitr
      · itrivial
      iframe Hpay Hcl
      ipureintro; exact Hns
    | true =>
      have Hdy : rs.mode.isDyn = true := by rw [Hmd, hd]
      have Hle : ca_r ≤ l.dlv.length := Nat.le_trans Hinv Hcap
      imod dghostVar_update_halves (l.dlv.length, rs.mode.foldCfg l.decs l.dlv rs.cfg) γ.cap _ _
        $$ Hcap_r Hpay with ⟨Hcap_r, Hpay⟩
      imod mono_nat_own_update l.dlv.length Hle $$ Hcam with ⟨Hcam, #Hcl⟩
      have Hlc : loanCfg γ.mode (some l) (ca_r, rs.cfg) =
          (l.dlv.length, rs.mode.foldCfg l.decs l.dlv rs.cfg) := by
        simp only [loanCfg, hd, ↓reduceIte, Hmd]
      rw [Hlc]
      imodintro
      isplitl [Hrn Hdlm Hcap_r Hcam Hdlv Hrof Hrof' Hrcpt]
      · iunfold advRet
        iexists rs, ca_d
        iframe Hrn Htlb Hcamlb
        isplitl [Hdlm Hcap_r Hcam]
        · iapply (runCfgR_loan (GF := GF) γ rs l Hsl Hdy).2
          iunfold runCfgLoan
          try rw [show rsDlv rs = l.dlv by simp only [rsDlv, Hsl]]
          iframe Hdlm Hcap_r Hcam
          isplitr
          · ipureintro; exact ⟨Hmd, Hsin, Hns, Hdp⟩
          rw [Hmd]
          iapply undecFree_mono γ.raft γ.mode (Nat.le_trans Hcle.2 Hinv) (Nat.le_refl _)
          iexact HA'
        isplitl [Hdlv]
        · simp only [rsDlv, Hsl]; iexact Hdlv
        isplitl [Hrof Hrof']
        · iexists _
          iframe Hrof Hrof'
        isplitl [Hrcpt]
        · simp only [loanRet, Hsl]; rw [Hstor]; iexact Hrcpt
        have H1 : rs.slent = none → rs.unpersisted = [] := fun h => by rw [Hsl] at h; cases h
        iframe HA'
        ipureintro; exact ⟨Hstor, Hunst, H1⟩
      isplitr
      · itrivial
      iframe Hpay Hcl
      ipureintro; exact Hns

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
    icases Hi with ⟨%L, %x, HP, %ds, Hreq, #Hlb⟩
    imod advance_complete γ rn id ds L x $$ Hlb Hdep HP with ⟨Hret, #Hw, Hans⟩
    imod Hclose $$ [H Hreq Hans] with -
    · inext
      iexists .RcvCommit
      iframe H
      iexists ((reqOf L ds, loanReq γ.mode L x) : AdvReq)
      iframe Hreq Hw Hans
    imodintro
    iapply Hau $$ Hret
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- **The driver's send on `advancec`** (`node.Advance`), with its payload for its `Ready`'s loan
`L`, its lower bound `ds` on the committed log and its request: back with `run`'s answer for `ds`
(`reqWit`: the floor's witness after a `Ready` without a snapshot, D22 S-d4). -/
theorem adv_send_au (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) (ds : List EntryM)
    (L : Option SnapLoan) (x : Nat × CCState) (q0 : AdvReq) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isAdvChan γ rn id ch -∗ advanceP γ L x -∗ dlvLb γ ds -∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) q0 -∗ dghostVar γ.req (DFrac.own (1 : Qp).half) q0 -∗
      ▷ (reqWit γ (reqOf L ds) -∗ capAns γ (loanReq γ.mode L x) -∗
          (∃ q : AdvReq, dghostVar γ.req (DFrac.own (1 : Qp).half) q ∗
            dghostVar γ.req (DFrac.own (1 : Qp).half) q) -∗ Φ) -∗
      sendAu γ.advancec () Φ := by
  unfold isAdvChan sendAu
  iintro ⟨Hlc1, Hlc2, Hlc3⟩ ⟨#Hchan, #Hinv⟩ HP #Hlb Hr1 Hr2 Hau
  imod dghostVar_update_halves ((reqOf L ds, loanReq γ.mode L x) : AdvReq) γ.req q0 q0
    $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
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
      iexists L, x
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
      icases Hi with ⟨%q, Hr1, #Hw, Hans⟩
      ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hr1 Hr2
      subst Hk
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ [] [Hans] [Hr1 Hr2]
      · iexact Hw
      · iexact Hans
      · iexists _; iframe Hr1 Hr2
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    iintro Hsd
    imod Hmask with -
    imod advance_complete γ rn id ds L x $$ Hlb Hi HP with ⟨Hret, #Hw, Hans⟩
    imod Hclose $$ [Hsd Hret] with -
    · inext
      iexists .SndCommit ()
      iframe
    imodintro
    iapply Hau $$ [] [Hans] [Hr1 Hr2]
    · iexact Hw
    · iexact Hans
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
