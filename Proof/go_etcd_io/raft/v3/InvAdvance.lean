/-
(D19i part 1, 2026-10-18) The `advancec` protocol's lemmas (`advInv`, `InvNode.lean`): the
rendezvous at which the floor is raised (`advance_complete`), `run`'s receive (`adv_recv_au`),
the driver's send (`adv_send_au`), and the protocol's allocation (`adv_start`). The receive and
the send follow Perennial's handshake idiom (`Handshake.lean`'s `handshake_receive_au`,
`handshake_send_au`) over the channel's states, with the payloads `advInv` gives each state.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std OFE go_etcd_io.raft.v3

section adv
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The rendezvous** (whichever side meets the other): the driver's append receipt absorbed,
the floor raised to the committed log `run` handed out (`ownRawNode_raise_floor`), which the
driver's lower bound `ds` is a prefix of; its witness, and `run`'s node after it. -/
theorem advance_complete (γ : NodeNames) (rn : Loc) (id : w64) (ds : List EntryM) :
    ⊢ dlvLb (GF := GF) γ ds -∗ advDep γ rn id -∗ advanceP γ () ==∗
      advRet γ rn id ∗ ∃ x : w64, storFloor γ.stor x ∗ ⌜(ds.length : Int) ≤ uint.Z x⌝ := by
  iintro #Hlb Hdep HP
  iunfold advDep at Hdep
  icases Hdep with ⟨%rs, %d, %ce, Hrn, #Htlb, Hcfg, Hrof, %Hrs⟩
  obtain ⟨Hstor, Hunst, Hdel⟩ := Hrs
  iunfold advanceP at HP
  icases HP with ⟨%d', %ce', %es', %p', Hdlv, Hrof', Hrcpt, %ca_d, #Hcamlb, %HA⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hrof Hrof'
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Heq
  -- the driver's lower bound, against `run`'s authority
  iunfold runCfg at Hcfg
  icases Hcfg with ⟨%Hm0, Hdlm, Hcfg⟩
  iunfold dlvLb at Hlb
  ihave %Hpfx := mono_list_auth_lb_valid _ _ _ _ $$ Hdlm Hlb
  -- the receipt: the `Ready`'s entries are appended
  ihave Hrcpt' : appendReceipt rs.storage rs.unpersisted $$ [Hrcpt]
  · rw [Hstor]; iexact Hrcpt
  imod ownRawNode_appended γ.raft rn id rs Hm0.2.2.2.2 $$ Hrn Hrcpt' with Hrn
  imod ownRawNode_raise_floor γ.raft rn id { rs with unpersisted := [] } rfl Hm0.2.2.2.1
    Hm0.2.2.2.2 $$ Hrn
    with ⟨Hrn, %x, %Hx, #Hfw⟩
  imodintro
  isplitr [Hfw]
  · iunfold advRet
    iexists { { rs with unpersisted := [] } with flw := true }, ca_d
    iframe Hrn Htlb Hcamlb
    isplitl [Hdlm Hcfg]
    · iunfold runCfg
      iframe Hdlm Hcfg
      ipureintro; exact ⟨Hm0.1, Hm0.2.1, rfl, Hm0.2.2.2⟩
    isplitl [Hdlv]
    · simp only; rw [Hdel]; iexact Hdlv
    isplitl [Hrof Hrof']
    · iexists _
      iframe Hrof Hrof'
    ipureintro
    exact ⟨Hstor, Hunst, rfl, rfl, fun h => by simp only; rw [Hdel]; exact HA h⟩
  iexists x
  isplitr
  · simp only; rw [← Hstor]; iexact Hfw
  ipureintro
  have := Hpfx.2.length_le
  simp only at Hx
  omega

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
    icases Hi with ⟨HP, %ds, Hreq, #Hlb⟩
    imod advance_complete γ rn id ds $$ Hlb Hdep HP with ⟨Hret, %x, #Hfw, %Hx⟩
    imod Hclose $$ [H Hreq] with -
    · inext
      iexists .RcvCommit
      iframe H
      iexists ds.length, x
      iframe Hreq Hfw
      ipureintro; exact Hx
    imodintro
    iapply Hau $$ Hret
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- **The driver's send on `advancec`** (`node.Advance`), with its payload, its lower bound
`ds` on the committed log and its request: back with the floor's witness for `ds`. -/
theorem adv_send_au (γ : NodeNames) (rn : Loc) (id : w64) (ch : Loc) (ds : List EntryM)
    (k0 : Nat) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isAdvChan γ rn id ch -∗ advanceP γ () -∗ dlvLb γ ds -∗
      dghostVar γ.req (DFrac.own (1 : Qp).half) k0 -∗ dghostVar γ.req (DFrac.own (1 : Qp).half) k0 -∗
      ▷ ((∃ x : w64, storFloor γ.stor x ∗ ⌜(ds.length : Int) ≤ uint.Z x⌝) -∗
          (∃ k : Nat, dghostVar γ.req (DFrac.own (1 : Qp).half) k ∗
            dghostVar γ.req (DFrac.own (1 : Qp).half) k) -∗ Φ) -∗
      sendAu γ.advancec () Φ := by
  unfold isAdvChan sendAu
  iintro ⟨Hlc1, Hlc2, Hlc3⟩ ⟨#Hchan, #Hinv⟩ HP #Hlb Hr1 Hr2 Hau
  imod dghostVar_update_halves ds.length γ.req k0 k0 $$ Hr1 Hr2 with ⟨Hr1, Hr2⟩
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
      icases Hi with ⟨%k, %x, Hr1, #Hfw, %Hx⟩
      ihave %Hk := dghostVar_agree _ _ _ _ _ $$ Hr1 Hr2
      subst Hk
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ [] [Hr1 Hr2]
      · iexists x; iframe Hfw; ipureintro; exact Hx
      · iexists _; iframe Hr1 Hr2
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    iintro Hsd
    imod Hmask with -
    imod advance_complete γ rn id ds $$ Hlb Hi HP with ⟨Hret, %x, #Hfw, %Hx⟩
    imod Hclose $$ [Hsd Hret] with -
    · inext
      iexists .SndCommit ()
      iframe
    imodintro
    iapply Hau $$ [] [Hr1 Hr2]
    · iexists x; iframe Hfw; ipureintro; exact Hx
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
