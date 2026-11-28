/-
Lean-first (no Rocq counterpart).

# Parity B2: the kind-independent parts of a `-parallel` leader's view after its `mem`

The view after `antSim_memP_in`'s `mem` is the `Ready`'s drain phase with its write queued and the
disk unchanged (`memView`). It differs from B1's view after a reported `Ready` (`afterReady`, whose
`AfterOk` `afterOk_loc` gives) only in the disk, the undo record and the queued writes, which raft's
facts, the configuration lag, the pending and transfer messages' facts and the leader hint do not
read; the disk with the queued write made is the `afterReady`'s (`write_memRec`). `memView_of`: those
parts of `memNode_of`'s premises, from `AfterOk`, the old view's facts and three kind-dependent facts
(the handed-out entries a prefix of the old disk, the term grown, `CandLt`) (#33 parity B2, Sim
round 14).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section memView
variable [GooseExts]

/-- The view after a `-parallel` leader's `mem`: the drain phase, its pending messages `P`, its write
queued. -/
abbrev memView (v : NodeView) (r₁ : RState) (rd : ReadyD) (P : List Msg) : NodeView :=
  { (v.drainOf r₁ rd) with pend := P, mems := [rd.memRec v] }

/-- **The disk with a `Ready`'s write made is raft's state after it** (`ReadyOutP`: the hard state,
and the entries from their first index; none, the disk's log). -/
theorem write_memRec {R : RunCfg} {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hro : ReadyOutP R n v r₁ rd) (hsn : rd.snap = none) :
    v.dur.write (rd.memRec v) = durOf (accepted r₁) := by
  obtain ⟨-, -, ht, hvo, hc, hne, hhd, -⟩ := hro
  have hlog : (match rd.ents.head? with
      | none => v.dur.log
      | some e0 => v.dur.log.take (uint.nat e0.Index' - 1) ++ rd.ents) = r₁.full := by
    cases he : rd.ents with
    | nil => exact (hne hsn he).symm
    | cons e0 es =>
      rw [he] at hhd
      exact ((hhd e0 rfl).1).symm
  show DurW.mk rd.term rd.vote rd.commit _ = DurW.mk r₁.p.term r₁.p.vote r₁.p.commit r₁.full
  rw [ht, hvo, hc]
  exact congrArg _ hlog

/-- **The kind-independent parts of the view after a `-parallel` leader's `mem`** (`memNode_of`'s
`hNF`, `hCL`, `hpend`, `hxpend`, `hlead`, `hDF`), from `AfterOk` of the `afterReady` view, the old
view's facts, and: the handed-out entries a prefix of the (unchanged) disk, the term grown, `CandLt`
at raft's state. -/
theorem memView_of {R : RunCfg} {dec : CCDec} {V : Fin R.N → NodeView} {n : Fin R.N} {r₁ : RState}
    {rd : ReadyD} {P : List Msg}
    (ha : AfterOk R.syncOff dec V n ((V n).afterReady r₁ rd)) (hv : NodeFactsD R n (V n))
    (hpar0 : (V n).parts = []) (hro : ReadyOutP R n (V n) r₁ rd) (hsn : rd.snap = none)
    (hP : ∀ q, q ∈ P ↔ q ∈ rd.msgs)
    (hpfx : (V n).delivered ++ rd.ce <+: (V n).dur.log)
    (hterm : uint.Z (V n).ps.term ≤ uint.Z r₁.p.term) (hcl : CandLt r₁.p) :
    NodeFactsD R n (memView (V n) r₁ rd P) ∧ ConfLag dec R (memView (V n) r₁ rd P) ∧
      (∀ q ∈ P, PendOk R.N (nodeId n) (memView (V n) r₁ rd P) q) ∧
      (∀ x ∈ rd.xmsgs, XPendOk R.N (nodeId n) (accepted r₁).p x) ∧
      LeadOk n (memView (V n) r₁ rd P) ∧
      ((V n).parts = [] → (V n).dur.write (rd.memRec (V n)) = durOf (accepted r₁)) := by
  have hw := write_memRec hro hsn
  obtain ⟨f1, f2, f3, -, -, f6, f7, -, f9, f10, f11, f12, f13, f14, f15⟩ := ha.facts
  obtain ⟨-, -, v3, v4, -, -, -, v8, -⟩ := hv
  refine ⟨⟨fun _ => f1, f2, fun h => ⟨(f3 h).1, (f3 h).2.1, (v3 h).2.2⟩, v4, hpfx, fun _ => ?_,
    fun q hq => f7 q ((hP q).mp hq), Int.le_trans v8 hterm, f9, f10, f11, f12, f13, f14, f15, hcl⟩,
    ha.confLag, fun q hq => ha.hpend q ((hP q).mp hq), ha.hxpend, ha.hlead, fun _ => hw⟩
  show _ ≤ uint.nat (([rd.memRec (V n)] ++ (V n).parts).foldl DurW.write (V n).dur).commit
  rw [hpar0]
  show _ ≤ uint.nat ((V n).dur.write (rd.memRec (V n))).commit
  rw [hw]
  exact f6

end memView

end AntSim
end EtcdGrove
end Perennial
