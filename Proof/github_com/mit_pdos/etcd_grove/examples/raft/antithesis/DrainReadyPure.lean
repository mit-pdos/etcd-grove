/-
Lean-first (no Rocq counterpart). #33 S4: **the pure facts of a `Ready` in `Cluster.drain`'s loop**
(`Cluster__drain.lean`), from raft's `Ready` post (`ReadyOut`, the queue, the first entry at the
in-progress boundary), the loop head (`RsView`, `Reach`), the binding's relation at the node read from
the invariant (`drain_peek`: `NetOk`, `NodeOk` over a sent list past the loop head's), the node's
numbers (`StateNums`) and the view's normality:
- `drainReady_pure`: the `Ready` at the protocol level (`ReadyOutP`, `readyOutP_of`), the node's log
  normal and each message the view's pending one in order (`DrainMsgOk`: its reading, of the drain's
  shape, `msgShape.stmt`; its numbers within `2 ^ 61`, `readyMsgNums`; to a node, `msgShape.stmt`;
  its term within the ceiling).
Its premise `habs` (every message read by `absMsgOf`, `Ready`'s post) is the caller's; the handled
message's numbers and type (`readyMsgNums`' premise) are `ViewNormal`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainPhases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A list related pointwise to its `filterMap` when every element is read. -/
theorem forall₂_filterMap {α β : Type} (f : α → Option β) (P : α → β → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, f a = some b → P a b) → (∀ a ∈ l, (f a).isSome) →
      List.Forall₂ P l (l.filterMap f)
  | [], _, _ => .nil
  | a :: l, hP, hs => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hs a List.mem_cons_self)
    rw [List.filterMap_cons, hb]
    exact .cons (hP a List.mem_cons_self b hb)
      (forall₂_filterMap f P l (fun a' h => hP a' (List.mem_cons_of_mem _ h))
        (fun a' h => hs a' (List.mem_cons_of_mem _ h)))

/-- **A `Ready`'s pure facts at a loop head** (see the file header). -/
theorem drainReady_pure (hshape : AntSim.msgShape.stmt) {S : AntCheck.State} {net net' : List Msg}
    {j : Fin 3} {v : AntSim.NodeView} {rs : RNState} {ps : PState} {h : HardStateM}
    {es ce : List EntryM} {rms : List QMsg} {ss : Option (w64 × StateType)} {qs : List Msg}
    {ip : Nat}
    (hrv : RsView rs v) (hR : AntSim.Reach (AntSim.nodeId j) net v ps)
    (hip : ip = lcpLen v.ps.log ps.log)
    (hout : ReadyOut (AntSim.nodeId j) rs ps h es ce rms ss none)
    (hqs : qs ≡ₚ ps.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j)))
    (hfirst : ∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1)
    (hbase : ps.base = base0) (hidx : AntSim.LogIdx ps.log)
    (hmatch : ∀ (k : Nat) (e f : EntryM), v.ps.log[k]? = some e → ps.log[k]? = some f →
      e.Term' = f.Term' → e = f)
    (habs : ∀ q ∈ rms, (absMsgOf q.st).isSome)
    (hnet : AntSim.NetOk S net') (hv : AntSim.NodeOk S net' j v) (hpre : net <+: net')
    (hN : ViewNormal v) (hsn : AntSim.StateNums (2 ^ 61) ps)
    (hterm : ∀ q ∈ rms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc) :
    AntSim.ReadyOutP (AntSim.nodeId j) v ps
        (readyDOf ps es (rms.filterMap (fun q => absMsgOf q.st)) qs ce) ∧
      AllNormal ps.log ∧
      List.Forall₂ (DrainMsgOk (AntSim.nodeId j) rs.tc) rms
        (rms.filterMap (fun q => absMsgOf q.st)) := by
  have hR' := hR.mono hpre
  have hmsgs : (readyDOf ps es (rms.filterMap (fun q => absMsgOf q.st)) qs ce).msgs ≡ₚ
      ps.outbox.filter (fun q => decide (q.dst ≠ AntSim.nodeId j)) := hout.2.2.2.2.1
  obtain ⟨hlogN, hsh, hvot⟩ := hshape S net' j v ps
    (readyDOf ps es (rms.filterMap (fun q => absMsgOf q.st)) qs ce) hnet hv hR' hmsgs hN.1
    (fun m hm => ⟨(hN.2 m hm).1, (hN.2 m hm).2.1⟩)
  have hro := readyOutP_of hrv (reach_ce hR) hip hout hfirst hqs hbase hidx hmatch hvot
  have hnums := AntSim.readyMsgNums hnet hv hR' hro hsn (fun m hm => (hN.2 m hm).2.2)
  refine ⟨hro, hlogN, forall₂_filterMap _ _ rms ?_ habs⟩
  intro q hq m hm
  have hmem : m ∈ rms.filterMap (fun q => absMsgOf q.st) := List.mem_filterMap.2 ⟨q, hq, hm⟩
  exact ⟨hm, hout.2.2.2.2.2.1 q hq, hsh m hmem, hnums m hmem, hvot m hmem, hterm q hq⟩

end pure

end AntHarness
end EtcdGrove
end Perennial
