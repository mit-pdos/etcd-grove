/-
Lean-first (no Rocq counterpart). **Probe B of the trace-check design** (2026-11-11,
`notes/trace-check-design.md` §8, `notes/decisions.md`, "Probe B (the escrow)"), after the escrow was
threaded (2026-11-12, implementation step 1; "Implementation step 1 (gates)"): the escrow itself
(`rtkInv`, its steps, the gates of `advInv`) is now `InvRtk.lean`, `stepIn`'s gates (`fwdGate`,
`netGate`, `trTokR_fwd`, `trTokR_net`) `InvNodeChan.lean`, `TrNetTy`/`TrSent`/`trTokR`
`TracedRecvTok.lean`, `handshake_send_au_fupd` `InvNodeChan.lean`, and the rendezvous over a channel
(the probe's `escInv`, `esc_recv_au`, `esc_send_au`) is `adv_recv_au`/`adv_send_au` (`InvAdvance.lean`).
What is left here are the probe's remaining pieces, for the gated `node.run` (step 4):

- the receiver's premises of `raft.Step.tracedTriple` from `netP`'s traced gate (`netGate_step`);
- the escrow's ghost-level run with a stale claim (`rtk_scenario`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.TracedRawNode

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section escrow
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A run of the escrow** (§8 item 3's stale claim, ghost-level): key 0 allocated and deposited, its
`Advance` without the claim (nothing taken), key 1 allocated (`run`'s half `some` again), then the
driver's stale claim on key 0 swapped while key 1 is pending; then key 1's deposit. -/
theorem rtk_scenario (ρ : RaftNames) (γe : RtkNames) (ms0 ms1 : List QMsg) :
    ⊢ rtkInv (GF := GF) ρ γe -∗ rtkRun γe none -∗ ([∗list] q ∈ ms0, trTokR ρ q.st) -∗
      ([∗list] q ∈ ms1, trTokR ρ q.st) -∗
      |={⊤}=> rtkRun γe none ∗ ([∗list] q ∈ ms0, trTokR ρ q.st) := by
  have hT : (↑rtkN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
  iintro #Hi Hr Ht0 Ht1
  imod rtk_key ρ γe ms0 ⊤ hT $$ Hi Hr with ⟨Hr, He0⟩
  unfold rtkElem
  icases He0 with ⟨%j0, He0, #Hal0⟩
  imod rtk_deposit ρ γe ms0 ⊤ hT $$ Hi Hr Ht0 with Hr
  -- key 0's `Advance`, by a driver without its claim (`ms = []`): `run`'s commit answers a deposit
  -- bound only for a requested key, and its half comes back as it was; here the bound for key 0 is
  -- minted as `run`'s answer to a request for it would be
  imod rtk_depLb ρ γe j0 ⊤ hT $$ Hi Hr Hal0 with ⟨Hr, #Hd0⟩
  -- key 1 allocated: `run`'s half `some` again
  imod rtk_key ρ γe ms1 ⊤ hT $$ Hi Hr with ⟨Hr, -⟩
  -- the stale claim on key 0, swapped while key 1 is pending
  imod rtk_take ρ γe j0 ms0 ⊤ hT $$ Hi He0 Hd0 with Ht0
  -- key 1's deposit
  imod rtk_deposit ρ γe ms1 ⊤ hT $$ Hi Hr Ht1 with Hr
  imodintro
  iframe Hr Ht0

/-! ### The receiver (§8 item 4) -/

/-- A message of a type without abstraction carries a token vacuously. -/
theorem recvTokOf_untyped (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8)
    (h : mtypeOf m.Type' = none) : ⊢ recvTokOf (GF := GF) γd m ents ctx := by
  unfold recvTokOf
  iintro %ty %hty
  rw [h] at hty
  exact absurd hty.1 (by simp)

/-- **The `recvc` arm's premises of `raft.Step.tracedTriple`** from `netP`'s traced gate: the type
(`StepEndTy`) and the received message's token (vacuous for `MsgUnreachable`). `Campaign`'s `MsgHup`
(`hupP`) is the same by `recvTokOf_untyped`. `StepNodeOk` comes from the guard's `Progress` lookup as
in `RawNode.Step.traced` (`ownRaftPhysC_prvals_ok`), unchanged. -/
theorem netGate_step (ρ : RaftNames) (γd : GName) (st : MsgSt) (htr : ρ.reTrace = some γd) :
    netGate (GF := GF) ρ st ⊢
      ⌜StepEndTy st.msg.Type' ∨ AckTy st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx := by
  unfold netGate
  rw [htr]
  iintro (⟨%Hn, Ht⟩ | %Hu)
  · iframe Ht; ipureintro; exact .inl Hn.stepEndTy
  · isplitr
    · ipureintro; left; unfold StepEndTy; simp [Hu]
    iapply recvTokOf_untyped γd st.msg st.ents st.ctx (by rw [Hu]; rfl)

end escrow

end EtcdGrove
end Perennial
