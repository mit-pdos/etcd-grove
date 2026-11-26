/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the transfer messages' `recv` and `send` (#33 parity B1)

`antSim_recvX` (`Stmts.lean`): a `MsgTimeoutNow` or forwarded `MsgTransferLeader` a node handles,
sent to it, is reported (`evRecvX`) and taken (`Recv`, B 199-204): it is no request (`IsReq`), so
`Recv` only sets `pending[n]` to it, which the node's view now says (`told`, the transfer arm).

`antSim_sendX` (`Stmts.lean`): the next unreported transfer message of a node's `Ready` is reported
(`evSendX`) and taken (`Send`, B 510-524): a `MsgTimeoutNow` is the node's own, a `MsgTransferLeader`
forwarded (`isForwarded`), to another server (`XPendOk`); of an unmodelled type (`isUnmodelled`,
B 702), so `Send` only takes back the announced write. C4's transfer part (`XNetOk`) of the new
message: its term is at most the node's (`XPendOk`), which is `currentTerm[n]` (sync disk); a
`MsgTimeoutNow`'s is one at which the transferee acknowledged (`XMsgFacts`: raft's ack in `G.acks`),
so at most the transferee's term (C5's acks, design §6.4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Recv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendRel

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section xmsgs
variable [GooseExts]

/-- Below `mskB1`, the driver neither batches, splits nor writes in parallel. -/
theorem InMask.b1 {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {net : List Msg}
    {xnet : List XMsg} (h : InMask msk R net xnet) :
    R.drv.batch = false ∧ R.drv.parallel = false ∧ R.drv.split = 0 := by
  obtain ⟨-, -, -, -, c1, c2, c3, -⟩ := hmsk
  obtain ⟨-, -, d1, d2, d3, -⟩ := h
  simp only [BLe, mskB1] at c1 c2 c3 d1 d2
  refine ⟨?_, ?_, ?_⟩
  · cases hb : R.drv.batch
    · rfl
    · exact absurd (c1 (d1 hb)) (by decide)
  · cases hb : R.drv.parallel
    · rfl
    · exact absurd (c2 (d2 hb)) (by decide)
  · by_cases hs : R.drv.split = 0
    · exact hs
    · exact absurd (c3 (d3 hs)) (by decide)

theorem orM_ok_true_x (b : Bool) : AntCheck.orM (.ok b) (.ok true) = .ok true := by cases b <;> rfl

theorem isForwarded_transfer : isForwarded go!"transfer" = true := by decide
theorem isUnmodelled_transfer : isUnmodelled go!"transfer" = true := by decide
theorem isUnmodelled_timeoutnow : isUnmodelled go!"timeoutnow" = true := by decide

theorem xmsgOf_typ (x : XMsg) :
    (xmsgOf x).typ = .ok (match x.ty with | .transferLeader => go!"transfer" | .timeoutNow => go!"timeoutnow") :=
  rfl

theorem isReq_xmsgOf (x : XMsg) : isReq (xmsgOf x) = .ok false := by
  unfold isReq
  rw [xmsgOf_typ, eok_bind]
  cases x.ty <;> rfl

/-- `Recv` of a transfer message: no request, so `pending[n]` is set to it. -/
theorem recvX_eq {R : RunCfg} {S : State} (n : Fin R.N) (x : XMsg) (hc : S.cfg = R.cfg)
    (hdst : x.dst = nodeId n) :
    S.step (evRecvX (nodeId n) x) = .ok (some (recvS S n.val (xmsgOf x))) := by
  unfold State.step
  simp (config := { decide := true }) only [evRecvX, idx_name hc, State.bind, State.recv, eok_bind, epure,
    ite_true, ite_false, need, Bool.false_eq_true]
  have hto : (xmsgOf x).to_ = .ok (nameOf (nodeId n)) := by rw [← hdst]; rfl
  simp only [hto, server_of hc n, bne_self_eq_false, isReq_xmsgOf, eok_bind, andM_false, ite_false,
    Bool.false_eq_true, epure]
  rfl

/-- `Send` of a transfer message: from the node or forwarded, to another server, unmodelled. -/
theorem sendX_eq {R : RunCfg} {S : State} (n : Fin R.N) (x : XMsg) (b : Str) (hc : S.cfg = R.cfg)
    (hsrv : S.cfg.server.has (nameOf x.dst) = true) (hne : (nameOf x.dst != nameOf (nodeId n)) = true)
    (hsrc : x.ty = .timeoutNow → x.src = nodeId n) :
    S.step (evSendX (nodeId n) b x) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  unfold State.step
  simp (config := { decide := true }) only [evSendX, idx_name hc, State.bind, State.send, eok_bind, epure,
    pure_bind, ite_true, ite_false, need, Bool.false_eq_true]
  have hto : (xmsgOf x).to_ = .ok (nameOf x.dst) := rfl
  have hfrom : (xmsgOf x).from_ = .ok (nameOf x.src) := rfl
  cases hty : x.ty
  · have ht : (xmsgOf x).typ = .ok go!"transfer" := by rw [xmsgOf_typ, hty]
    simp (config := { decide := true }) only [hto, hfrom, ht, server_of hc n, hsrv, hne, isReq_xmsgOf,
      isForwarded_transfer, isUnmodelled_transfer, eok_bind, epure, pure_bind, orM_ok_true_x, andM_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ite_false, ite_true, Option.isSome_none, Bool.or_false,
      Bool.false_or, Bool.or_true, Bool.true_or]
    rfl
  · have ht : (xmsgOf x).typ = .ok go!"timeoutnow" := by rw [xmsgOf_typ, hty]
    have hs : nameOf x.src = nameOf (nodeId n) := by rw [hsrc hty]
    simp (config := { decide := true }) only [hto, hfrom, ht, hs, server_of hc n, hsrv, hne, isReq_xmsgOf,
      isUnmodelled_timeoutnow, beq_self_eq_true, orM_true, eok_bind, epure, pure_bind, andM_true,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, Option.isSome_none,
      Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]
    rfl

/-- **`recv` of a transfer message** (B 199-204), for the runs a mask below `mskB1` admits. -/
theorem antSim_recvX_in (msk : SimMask) (_hmsk : msk ≤ mskB1) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (x : XMsg),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → x ∈ xnet → x.dst = nodeId n → (V n).xcause = some x →
      SimStep R dec evs G (evRecvX (nodeId n) x) (setV V n { V n with told := true }) net xnet := by
  intro R dec S V net xnet evs G n x _ ⟨hp, hs, hl, hgo⟩ _ hdst hxc
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hstep := recvX_eq n x hc hdst
  have hrel : AntSim R dec (recvS S1 n.val (xmsgOf x)) (setV V n { V n with told := true }) net xnet := by
    obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11,
      by simpa [recvS] using sh12, sh13, sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, fun _ => .inr ⟨x, hxc, ?_⟩, d15,
        d16, d17, d18⟩
      change (S1.pending.set k.val [xmsgOf x])[k.val]! = _
      exact get!_set_self _ (by rw [sh12]; exact k.isLt)
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, fun ht => ?_, d15, d16, d17, d18⟩
      rw [show (recvS S1 n.val (xmsgOf x)).pending[k.val]! = S1.pending[k.val]! from
        get!_set_ne _ _ hne]
      exact d14 ht
  have hgo2 : GlobalOk R (recvS S1 n.val (xmsgOf x)) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

/-- C4's transfer part of a transfer message of node `n`'s `Ready` (`XPendOk`), at its sync disk; a
`MsgTimeoutNow`'s term is one its receiver acknowledged at (`XMsgFacts`, C5's acks). -/
theorem xnetOk_of_xpend {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} {x : XMsg} {G : RaftFacts} (hgo : GlobalOk R S net G) (h : NodeOk R dec S net n v)
    (hdt : v.dur.term = v.ps.term) (hx : XPendOk R.N (nodeId n) v.ps x) (hxf : XMsgFacts G x) :
    (∃ i : Fin R.N, uint.Z x.term ≤ S.currentTerm[i.val]!) ∧
    (x.ty = .timeoutNow → ∀ j : Fin R.N, x.dst = nodeId j → uint.Z x.term ≤ S.currentTerm[j.val]!) := by
  obtain ⟨-, -, hle, -⟩ := hx
  have hct : S.currentTerm[n.val]! = uint.Z v.ps.term := by rw [h.disk.1, hdt]
  refine ⟨⟨n, by rw [hct]; exact hle⟩, fun hty j hj => ?_⟩
  obtain ⟨i, hi, ha⟩ := hxf hty
  exact hgo.2.2.2.2.2.2.2.2 _ ha hi j hj

/-- **`send` of a transfer message** (B 510-524, unmodelled), for the runs a mask below `mskB1` admits
(sync storage: the disk is raft's state). -/
theorem antSim_sendX_in (msk : SimMask) (hmsk : msk ≤ mskB1) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (x : XMsg)
      (rest : List XMsg),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → R.md.async = false → (V n).xpend = x :: rest → Told (V n) →
      XMsgFacts G x →
      SimStep R dec evs G (evSendX (nodeId n) (V n).byE x)
        (setV V n { V n with xpend := rest, undo := none, made := true }) net (xnet ++ [x]) := by
  intro R dec S V net xnet evs G n x rest hin ⟨hp, hs, hl, hgo⟩ hasync hxp _ hxf
  obtain ⟨hbt, hpar, hspl⟩ := hin.b1 hmsk
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hsync := ((hno n).sync hasync hbt hspl hpar)
  have hdt : (V n).dur.term = (V n).ps.term := by rw [hsync.2.1]; rfl
  have hx : XPendOk R.N (nodeId n) (V n).ps x := (hno n).xpend x (by rw [hxp]; exact List.mem_cons_self)
  obtain ⟨hne, ⟨j, hj⟩, -, hsrc⟩ := id hx
  have hsrv : S1.cfg.server.has (nameOf x.dst) = true := by
    rw [hc, R.server_eq, hj]; exact server_has j
  have hne' : (nameOf x.dst != nameOf (nodeId n)) = true := by
    rw [bne_iff_ne]; intro h; exact hne (nameOf_inj h)
  have hstep := sendX_eq n x (V n).byE hc hsrv hne' hsrc
  have hxnew := xnetOk_of_xpend hgo1 (hno n) hdt hx hxf
  have hgo2 : GlobalOk R (sendS S1 n.val S1.msgs S1.confirmed) net G := hgo1
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hrel : AntSim R dec (sendS S1 n.val S1.msgs S1.confirmed)
      (setV V n { V n with xpend := rest, undo := none, made := true }) net (xnet ++ [x]) := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, by simpa [sendS] using sh11,
      sh12, sh13, sh14⟩, hb, hn, fun y hy => ?_, fun k => ?_⟩
    · rcases List.mem_append.mp hy with hy | hy
      · exact hxn y hy
      · rw [List.mem_singleton] at hy; subst hy; exact hxnew
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, fun a b c e => ⟨(d3 a b c e).1, (d3 a b c e).2.1, fun h => absurd rfl h⟩,
        ⟨?_, ?_⟩, d5, d6, d7, d8, d9, d10, d11,
        fun y hy => d12 y (by rw [hxp]; exact List.mem_cons_of_mem _ hy), d13, d14, d15, d16, d17, d18⟩
      · change ((S1.undo.set k.val none)[k.val]!).isNone = true ↔ (none : Option DurW) = none
        rw [get!_set_self _ (by rw [sh11]; exact k.isLt)]; simp
      · intro p hp
        change (S1.undo.set k.val none)[k.val]! = some p at hp
        rw [get!_set_self _ (by rw [sh11]; exact k.isLt)] at hp; cases hp
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, ?_, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩
      unfold UndoIs
      rw [show (sendS S1 n.val S1.msgs S1.confirmed).undo[k.val]! = S1.undo[k.val]! from get!_set_ne _ _ hne]
      exact d4
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

end xmsgs

end AntSim
end EtcdGrove
end Perennial
