/-
A request `maybeCommit` sends the witness (`WAppSent`, `Spec/raft__maybeCommit.lean`) is the
protocol's `StepC.sendWApp` (2026-10-20, witness support; Lean-first): at a non-joint
configuration with a witness, `OneLessThanQuorumInReplicationSet`'s witness is the configuration's,
the epoch's excluded voter is the protocol's (`exclOf`), its non-witness voters are `rsVoters`, and
the count of the half's `Match` values at least the index is the count of `ackedBy` in the
replication set.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import RaftWitness.Proof.go_etcd_io.raft.v3.Protocol.StepR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris go_etcd_io.raft.v3

section bridge
variable [FfiSyntax]

/-- What `StepC.sendWApp` asks of a request `m` at the protocol state `p` of the configuration
`c`, but the role. -/
def SendWAppOk (c : CfgM) (id : w64) (p : PState) (m : Msg) : Prop :=
  c.wit ≠ W64 0 ∧ c.wit ∈ c.incoming ∧ exclOf c p ≠ c.wit ∧ exclOf c p ∈ c.incoming ∧
  ∃ (i : w64) (e : EntryM) (vs : List w64),
    plogEntryAt p.base p.log i = some e ∧ e.Term' = p.term ∧ e.Subterm' = p.sub ∧
    GMap.size c.incoming / 2 ≤ GMap.size (ackedBy p i ∩ rsVoters c p) ∧
    vs ≡ₚ GMap.elements (rsVoters c p) ∧
    m = Msg.mkV .wapp id c.wit p.term false i p.term p.sub (W64 0) [] vs []

/-- `SendWAppOk` reads the protocol state's log, term, subterm, excluded voter and `Match` values
only. -/
theorem SendWAppOk.congr {c : CfgM} {id : w64} {p p' : PState} {m : Msg}
    (hb : p'.base = p.base) (hl : p'.log = p.log) (ht : p'.term = p.term) (hs : p'.sub = p.sub)
    (hx : p'.rsx = p.rsx) (hm : p'.matched = p.matched) (H : SendWAppOk c id p m) :
    SendWAppOk c id p' m := by
  have he : exclOf c p' = exclOf c p := by unfold exclOf; rw [hx]
  have hr : rsVoters c p' = rsVoters c p := by unfold rsVoters; rw [he]
  have ha : ∀ i, ackedBy p' i = ackedBy p i := by intro i; unfold ackedBy; rw [hm]
  unfold SendWAppOk at *
  rw [he, hr, hb, hl, ht, hs]
  simp only [ha]
  exact H

theorem SendWAppOk.stepC {c : CfgM} {id : w64} {B : Int} {p : PState} {m : Msg}
    (Hr : p.role = .leader) (H : SendWAppOk c id p m) : StepC c id B p [] (psendMsgs p [m]) := by
  obtain ⟨Hw, Hwin, Hx, Hxin, i, e, vs, He, Het, Hes, Hsz, Hvs, rfl⟩ := H
  exact .sendWApp p i e vs Hr Hw Hx Hxin He Het Hes Hsz Hvs

theorem SendWAppOk.stepR {Adm : List EntryM → CCState → Prop} {dec : CCDec} {id : w64} {B : Int}
    {r : RState} {m : Msg} (Hr : r.p.role = .leader) (H : SendWAppOk r.cfg.cfg id r.p m) :
    StepR Adm dec id B r [] { r with p := psendMsgs r.p [m] } := by
  obtain ⟨Hw, Hwin, Hx, Hxin, i, e, vs, He, Het, Hes, Hsz, Hvs, rfl⟩ := H
  exact .sendWApp r i e vs Hr Hw Hwin Hx Hxin He Het Hes Hsz Hvs

/-- The count of a half's `Match` values at least `N ≠ 0` (`rsAcked`, its replication set's
non-witness voters) is at most the count of `ackedBy` in them. -/
theorem countGe_rsAcked_le {V : GSet w64} {pvs : GMap w64 Progress} {r : RSM} {k : Nat}
    {N : w64} (p : PState) (Hm : p.matched = prvalsMatch pvs) (HN : N ≠ W64 0)
    (H : CountGe V (rsAcked pvs r) k N) : k ≤ GMap.size (ackedBy p N ∩ r.nwv) := by
  refine Nat.le_trans H (GMap.subseteq_size ?_)
  rw [GMap.elem_of_subseteq]
  intro x hx
  have hge : uint.Z N ≤ uint.Z (rsAcked pvs r x) := by
    rw [GMap.mem_iff, GMap.lookup_filter] at hx
    cases hv : V !! x with
    | none => rw [hv] at hx; simp at hx
    | some u =>
      rw [hv] at hx
      by_cases hge : uint.Z N ≤ uint.Z (rsAcked pvs r x)
      · exact hge
      · simp [Option.filter, hge] at hx
  unfold rsAcked scopedAcked at hge
  by_cases hn : x ∈ r.nwv
  · rw [if_pos hn] at hge
    rw [GMap.elem_of_intersection]
    refine ⟨?_, hn⟩
    unfold ackedBy
    rw [GMap.elem_of_dom', GMap.mem_iff, GMap.lookup_filter, Hm]
    cases hx' : prvalsMatch pvs !! x with
    | none =>
      exfalso
      have : pvsAcked pvs x = none := by simp [pvsAcked, ← hx', prvalsMatch]
      rw [this] at hge
      simp only [Option.getD_none] at hge
      apply HN; apply uint_Z_inj.mp
      have := uint_Z_nonneg N; simp at hge; word
    | some a =>
      have : pvsAcked pvs x = some a := by simp [pvsAcked, ← hx', prvalsMatch]
      rw [this] at hge
      simp only [Option.getD_some] at hge
      simp [Option.filter, hge]
  · exfalso
    rw [if_neg hn] at hge
    simp only [Option.getD_none] at hge
    apply HN; apply uint_Z_inj.mp
    have := uint_Z_nonneg N; simp at hge; word

/-- **`maybeCommit`'s witness request is `StepC.sendWApp`'s** at a non-joint configuration with
the epoch the leader's (`EpochOkC`), no node `0` among the voters, from any protocol state that
reads the leader's log, term, subterm, excluded voter and `Match` values. -/
theorem WAppSent.ok {c : CfgM} {id : w64} {s : NState} {m : Msg} (p : PState)
    (Hout : c.outgoing = ∅) (Hep : EpochOkC c.incoming c.outgoing c.wit s.ep)
    (H0 : W64 0 ∉ c.incoming)
    (Hpt : p.term = s.term) (Hpb : p.base = s.logst.prev)
    (Hpl : p.log = s.logst.sents ++ s.logst.uents) (Hps : p.sub = s.ep.sub)
    (Hpx : p.rsx = epochRsx s.ep) (Hpm : p.matched = prvalsMatch s.prvals)
    (H : WAppSent c id s m) : SendWAppOk c id p m := by
  obtain ⟨w, i, e, vs0, vs1, res, rfl, Hnone, Hok, Hres, Hi0, He, Het, Hes, Hvs0, -⟩ := H
  -- a half replicates to `w`: the epoch is not bare, so well formed
  have Hrep := (Hok.1 w).1 (by rw [Hres]; rfl)
  unfold EpochOkC at Hep
  have Hbare : s.ep ≠ EpochM.bare (W64 0) := by
    intro h; apply Hnone; left; rw [h]; simp [EpochM.bare, RSM.bare, RSM.rep]
  have Hw : c.wit ≠ W64 0 := by
    intro h; rw [if_pos h] at Hep; exact Hbare Hep
  rw [if_neg Hw] at Hep
  rcases Hep with Hep | Hep
  · exact absurd Hep Hbare
  rcases Hep with ⟨h, -⟩ | ⟨-, H0w, H1w⟩
  · exact absurd h Hw
  rw [Hout] at H1w
  -- the outgoing half has no witness, so the incoming one replicates to `w`
  have H1n : s.ep.rs1.rep = false := by
    have : s.ep.rs1.wit = W64 0 := by
      rw [H1w.1]; simp
    simp [RSM.rep, this]
  rcases Hrep with ⟨Hr0, Hw0⟩ | ⟨Hr1, -⟩
  rotate_left
  · rw [H1n] at Hr1; cases Hr1
  have Hr0' := Hr0
  simp only [RSM.rep, decide_eq_true_iff] at Hr0'
  obtain ⟨Hwnz, Hxw⟩ := Hr0'
  obtain ⟨Hwit, Hexcl, Hnwv⟩ := H0w
  have Hwin : c.wit ∈ c.incoming := by
    by_cases hn : c.wit ∈ c.incoming
    · exact hn
    · rw [if_neg hn] at Hwit; exact absurd Hwit Hwnz
  rw [if_pos Hwin] at Hwit
  have Hww : w = c.wit := by rw [← Hw0, Hwit]
  subst Hww
  rcases Hexcl with h | ⟨Hxin, -, -⟩
  · exact absurd h Hxw
  -- the protocol's excluded voter is the epoch's
  have Hxnz : s.ep.rs0.excl ≠ W64 0 := fun h => H0 (h ▸ Hxin)
  have Hrsx : epochRsx s.ep = s.ep.rs0.excl := by
    unfold epochRsx; rw [if_neg Hxw]
  have Hexclp : exclOf c p = s.ep.rs0.excl := by
    unfold exclOf; rw [Hpx, Hrsx, if_neg Hxnz]
  have Hrsv : rsVoters c p = s.ep.rs0.nwv := by
    unfold rsVoters; rw [Hexclp, Hnwv, Hwit]
  refine ⟨Hw, Hwin, ?_, ?_, i, e, vs0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Hexclp, ← Hwit]; exact Hxw
  · rw [Hexclp]; exact Hxin
  · rw [Hpb, Hpl]; exact He
  · rw [Hpt]; exact Het
  · rw [Hps]; exact Hes
  · rw [Hrsv]
    have Hc := ((Hok.2 _ i Hres).1 Hr0 (Hwit ▸ rfl))
    exact countGe_rsAcked_le p Hpm Hi0 Hc
  · rw [Hrsv]; exact Hvs0
  · rw [Hpt, Hps]; simp [wAbs, wappMsg]

end bridge

end EtcdGrove
end Perennial
