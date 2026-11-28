/-
Lean-first (no Rocq counterpart).

# Parity B2: `wrote` without batching (`antSim_wroteP_in`)

`Wrote` (B 502-504) clears the node's undo record: the binding is `sendS` with its facts and
confirmations kept, so `EffTerm` only rises (`effTerm_sendS_ge`) and every fact the relation keeps
stays (#33 parity B2, Sim round 8). Unbatched only: a batch's pending acknowledgements read the undo
record (`PendOkB`), which the `wrote` of a batch comes after.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendD

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section wroteP
variable [GooseExts]

theorem wrote_eq {R : RunCfg} {S : State} (n : Fin R.N) (hc : S.cfg = R.cfg) :
    S.step (evWrote (nodeId n)) = .ok (some (sendS S n.val S.msgs S.confirmed)) := by
  unfold State.step
  simp (config := { decide := true }) only [evWrote, idx_name hc, State.bind, State.wrote, eok_bind,
    epure, ite_true, ite_false]
  rfl

/-- The restart facts after `wrote`: the node's undo record goes. -/
theorem undoBindOk_wrote {R : RunCfg} {S : State} {n : Fin R.N} (hn : n.val < S.undo.length)
    (hu : UndoBindOk R.N S) : UndoBindOk R.N (sendS S n.val S.msgs S.confirmed) := by
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hge := effTerm_sendS_ge (M := S.msgs) (C := S.confirmed) hn
  refine ⟨fun T hT => (hu1 T hT).imp id (fun h i => Int.lt_of_lt_of_le (h i) (hge i.val)),
    fun j => (hu2 j).imp id (fun h => h.imp id (fun h i => Int.lt_of_lt_of_le (h i) (hge i.val))),
    fun j u hu hm => ?_⟩
  obtain ⟨-, hu'⟩ := sendS_undo_some hn hu
  exact hu3 j u hu' hm

/-- C4 after `wrote`. -/
theorem netOkD_wrote {R : RunCfg} {S : State} {net : List Msg} {n : Fin R.N} (hn : n.val < S.undo.length)
    (hnet : NetOkD R S net) : NetOkD R (sendS S n.val S.msgs S.confirmed) net := by
  have hge := effTerm_sendS_ge (M := S.msgs) (C := S.confirmed) hn
  have hsub : ∀ f ∈ S.msgs, f ∈ S.msgs := fun _ h => h
  refine ⟨fun m hm => ?_, fun m hm hty j hdst => ?_, hnet.2.2.1, hnet.2.2.2.1, hnet.2.2.2.2.1,
    hnet.2.2.2.2.2.1, hnet.2.2.2.2.2.2⟩
  · obtain ⟨hty, ⟨i, hsrc, h2, h3⟩, j, hdst, hj⟩ := hnet.1 m hm
    refine ⟨hty, ⟨i, hsrc, h2.imp id (fun ⟨k, hk⟩ => ⟨k, Int.le_trans hk (hge k.val)⟩), h3⟩, j, hdst,
      fun hle => ?_⟩
    obtain ⟨r1, r2, r3, r4⟩ := hj (Int.le_trans (hge j.val) hle)
    exact ⟨r1, r2, r3, fun ht i hi => AckInD.sendS hn hsub (r4 ht i hi)⟩
  · refine ⟨(hnet.2.1 m hm hty j hdst).1, fun u hu hm' hut => ?_⟩
    obtain ⟨-, hu'⟩ := sendS_undo_some hn hu
    exact (hnet.2.1 m hm hty j hdst).2 u hu' hm' hut

/-- A node part after `wrote` at node `n` (the caller's undo record `u` and `made` `b`). -/
theorem nodeOkD_wrote {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {k n : Fin R.N}
    {v : NodeView} (hn : n.val < S.undo.length) (hbat : R.drv.batch = false)
    (h : NodeOkD R dec S net k v) (u : Option DurW) (b : Bool)
    (hu : UndoIs (sendS S n.val S.msgs S.confirmed) k { v with undo := u, made := b })
    (hsd : SyncDisk R { v with undo := u, made := b })
    (huf : UndoFacts R { v with undo := u, made := b })
    (hum : R.md.async = false → R.drv.batch = false → u ≠ none → b = false) :
    NodeOkD R dec (sendS S n.val S.msgs S.confirmed) net k { v with undo := u, made := b } := by
  have hsub : ∀ f ∈ S.msgs, f ∈ S.msgs := fun _ h => h
  obtain ⟨d1, d2, -, -, d5, d6, d7, d8, d9, d10, d11, -, d13, d14, d15, d16, d17, d18, d19, -, d21,
    d22, d23, -, d25⟩ := h
  refine ⟨d1, d2, hsd, hu, d5, d6, d7, d8, ?_, d10, d11, fun hb' => (by rw [hbat] at hb'; cases hb'),
    d13, d14, d15, d16, d17, d18, d19, huf, d21, d22, d23, hum, d25⟩
  intro hl
  obtain ⟨l1, l2, l3, l4, l5⟩ := d9 hl
  exact ⟨l1, l2, fun j i h1 h2 => AckInX.sendS hn hsub (l3 j i h1 h2),
    fun j hj => (l4 j hj).imp id (AckInX.sendS hn hsub), l5⟩

/-- **`wrote`** (B 502-504) over `AntSimD`, unbatched (`antSim_wrote_in.stmt`'s `-parallel` arm, and
any sync unbatched run): the announced write is made, the undo record goes. -/
theorem antSim_wroteP_in (msk : SimMask) (_hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
      InMask msk R net xnet → R.drv.batch = false → SimPreD R dec S V net xnet evs G →
      SimStepD R dec evs G (evWrote (nodeId n)) (setV V n { V n with undo := none, made := true })
        net xnet := by
  intro R dec S V net xnet evs G n _ hbat ⟨hp, hs, hl, hgo⟩
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  obtain ⟨hsh, ⟨hb, hub⟩, hnet, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hn : n.val < S1.undo.length := by rw [sh11]; exact n.isLt
  have hge := effTerm_sendS_ge (M := S1.msgs) (C := S1.confirmed) hn
  have hrel : AntSimD R dec (sendS S1 n.val S1.msgs S1.confirmed)
      (setV V n { V n with undo := none, made := true }) net xnet := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, by simpa [sendS] using sh11,
      sh12, sh13, sh14⟩, ⟨hb, undoBindOk_wrote hn hub⟩, netOkD_wrote hn hnet,
      fun x hx => (hxn x hx).imp fun i hi => Int.le_trans hi (hge i.val), fun k => ?_⟩
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      have hsy := (hno k).2.2.1
      refine nodeOkD_wrote hn hbat (hno k) none true ⟨?_, ?_⟩
        (fun a b c d => ⟨(hsy a b c d).1, (hsy a b c d).2.1, fun h => absurd rfl h⟩)
        (fun d hd => by simp at hd) (fun _ _ h => absurd rfl h)
      · change ((S1.undo.set k.val none)[k.val]!).isNone = true ↔ (none : Option DurW) = none
        rw [get!_set_self _ hn]; simp
      · intro p hp
        change (S1.undo.set k.val none)[k.val]! = some p at hp
        rw [get!_set_self _ hn] at hp; cases hp
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      have hu : UndoIs (sendS S1 n.val S1.msgs S1.confirmed) k (V k) := by
        unfold UndoIs
        rw [show (sendS S1 n.val S1.msgs S1.confirmed).undo[k.val]! = S1.undo[k.val]! from
          get!_set_ne _ _ hne]
        exact (hno k).2.2.2.1
      obtain ⟨-, -, d3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d20, -, -, -, d24, -⟩ := hno k
      exact nodeOkD_wrote (v := V k) hn hbat (hno k) (V k).undo (V k).made hu d3 d20 d24
  have hgo2 : GlobalOk R (sendS S1 n.val S1.msgs S1.confirmed) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc (wrote_eq n hc) (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

end wroteP

end AntSim
end EtcdGrove
end Perennial
