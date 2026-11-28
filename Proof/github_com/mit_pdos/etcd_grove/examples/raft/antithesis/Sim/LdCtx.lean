/-
Lean-first (no Rocq counterpart).

# A reported `Ready`'s context, node-local (`LdCtx`)

`RdCtx` (`Ready.lean`) is what a reported `Ready` starts from in B1: the whole relation `AntSim` at
the state after `GC`, every node's disk raft's state. The leader kinds' `InMemory` evaluations read
less: the binding's facts (`BindingOk`, `GlobalOk`), the network's and the node's own facts, the node's
disk its raft state, and the uniqueness of a term's leader. `LdCtx` is that part, with the network
read at `liftC S1` (the commits raised to the announced ones: the state a B1 lemma reads
while other nodes have writes queued, parity B2's `-parallel`). B1's `RdCtx` gives it
(`RdCtx.toLd`: no write is queued, `liftC S1 = S1`); so does the B2 relation for a `-parallel`
leader with no write queued (`MemCtx.lean`) (#33 parity B2, Sim round 10).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.LiftC

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section ldctx
variable [GooseExts]

/-- **Election safety in the binding**: a leader `k` at its term, and a leader record of `n` at that
term, are the same node (`GlobalOk`'s leaders are raft's, `RaftLaws`' election safety). -/
theorem lead_unique {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n k : Fin R.N}
    (hs : AntSim R dec S V net xnet) (hgo : GlobalOk R S net G) (hl : RaftLaws G)
    (hdk : ∀ k : Fin R.N, (V k).dur = durOf (V k).r)
    (hk : S.role[k.val]! = leader)
    (hn : S.leaders.contains { server := nameOf (nodeId n), term := S.currentTerm[k.val]! } = true) :
    k = n := by
  have hv := hs.2.2.2.2 k
  have hvk : (V k).ps.role = .leader := by
    have h := hv.mem.1
    rw [hk] at h
    exact (roleOf_leader_iff _).mp h.symm
  have hkm := List.contains_iff_mem.mp (hv.leader hvk).1
  have hnm := List.contains_iff_mem.mp hn
  have hct : S.currentTerm[k.val]! = uint.Z (V k).ps.term := by rw [hv.disk.1, hdk k]; rfl
  have h := hgo.leader_server hl hnm hkm hct
  exact name_inj h.symm

/-- **A reported `Ready`'s node-local context** at node `n`, at the binding's state `S1` (after
`GC`): `RdCtx` without the checker's prefix, the `GC` run and the whole relation; in their place the
binding's and the node's facts at `S1`, the network's at `liftC S1`, the node's disk its raft state,
and a term's leader unique. -/
structure LdCtx (R : RunCfg) (dec : CCDec) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState) (rd : ReadyD)
    (S1 : State) : Prop where
  hl : RaftLaws G
  hgo1 : GlobalOk R S1 net G
  hsh : Shape R S1
  hb : BindingOk R dec S1
  hnet : NetOk R (liftC S1) net
  hv : NodeOk R dec S1 net n (V n)
  hdn : (V n).dur = durOf (V n).r
  hlu : ∀ k : Fin R.N, S1.role[k.val]! = leader →
    S1.leaders.contains { server := nameOf (nodeId n), term := S1.currentTerm[k.val]! } = true → k = n
  hc : S1.cfg = R.cfg
  hn3 : n.val < S1.role.length
  hct3 : n.val < S1.currentTerm.length
  hlg3 : n.val < S1.log.length
  d1 : S1.currentTerm[n.val]! = uint.Z (V n).ps.term
  d2 : S1.vote n.val = nameOf (V n).ps.vote
  d3 : S1.log[n.val]! = logOf (V n).ps.log
  d4 : S1.commitIndex[n.val]! = uint.Z (V n).ps.commit
  d5 : S1.role[n.val]! = roleOf (V n).ps.role
  d7 : (V n).ps.outbox = []
  d8 : (V n).ps.base = base0
  d9 : LogIdx (V n).ps.log
  hconf : S1.config[n.val]! = confView R.N (V n).r.cfg
  hcf : (V n).r.cfg.cfg = CfgM.simple R.voters0 ∅
  hcc : R.md.confChanges = false
  hsnf : R.md.snapshots = false
  hq0 : S1.queue[n.val]! = []
  hpre : rd.pre = true → r₁.p.role = .follower
  hsn : rd.snap = none
  hfl : r₁.full = r₁.p.log
  hrf : ReadyFacts G (nodeId n) r₁
  hr : ReachP (R.k n) (CfgM.simple R.voters0 ∅) (nodeId n) net xnet (V n) r₁.p
  hro : ReadyOutP R n (V n) r₁ rd
  htold : (V n).byE = go!"recv" → (V n).told = true
  htb : uint.Z (V n).ps.term + 1 < 2 ^ 64
  hin : ∀ m ∈ net, RdTy m.ty → InMsg m
  hqs : ∀ q ∈ (V n).qs, q.ty ≠ .preVoteResp → SelfMsg (nodeId n) (V n).ps.term q
  hqc : (V n).ps.role = .candidate → ∀ q ∈ (V n).qs, q.ty ≠ .preVoteResp → q.ty = .voteResp
  hso : SelfOut (CfgM.simple R.voters0 ∅) (R.k n) (nodeId n) r₁.p
  hvs : (V n).ps.role ≠ .follower → (V n).ps.vote = nodeId n
  hvs1 : r₁.p.role ≠ .follower → r₁.p.vote = nodeId n
  hk : ReadyKind (CfgM.simple R.voters0 ∅) (nodeId n) net xnet (V n) r₁.p rd

/-- **B1's context is node-local's**: with no write queued anywhere, `liftC S1` is `S1`. -/
theorem RdCtx.toLd {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {evs : List Event} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD}
    {S1 : State} (hx : RdCtx R dec S V net xnet evs G n r₁ rd S1) : LdCtx R dec V net xnet G n r₁ rd S1 := by
  have hL : liftC S1 = S1 := liftC_self fun i hi => by
    rw [hx.hs1.1.2.2.2.2.2.1] at hi
    exact hx.hqa ⟨i, hi⟩
  exact {
    hl := hx.hl, hgo1 := hx.hgo1, hsh := hx.hs1.1, hb := hx.hs1.2.1
    hnet := by rw [hL]; exact hx.hs1.2.2.1
    hv := hx.hs1.2.2.2.2 n
    hdn := hx.hdk n
    hlu := fun k hk hn => lead_unique hx.hs1 hx.hgo1 hx.hl hx.hdk hk hn
    hc := hx.hc, hn3 := hx.hn3, hct3 := hx.hct3, hlg3 := hx.hlg3
    d1 := hx.d1, d2 := hx.d2, d3 := hx.d3, d4 := hx.d4, d5 := hx.d5, d7 := hx.d7, d8 := hx.d8
    d9 := hx.d9, hconf := hx.hconf, hcf := hx.hcf, hcc := hx.hcc, hsnf := hx.hsnf, hq0 := hx.hq0
    hpre := hx.hpre, hsn := hx.hsn, hfl := hx.hfl, hrf := hx.hrf, hr := hx.hr, hro := hx.hro
    htold := hx.htold, htb := hx.htb, hin := hx.hin, hqs := hx.hqs, hqc := hx.hqc, hso := hx.hso
    hvs := hx.hvs, hvs1 := hx.hvs1, hk := hx.hk }

/-- The `Ready`'s state keeps the base `base0` (`ReadyOutP`, snapshots off). -/
theorem LdCtx.base1 {R : RunCfg} {dec : CCDec} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : LdCtx R dec V net xnet G n r₁ rd S1) : r₁.p.base = base0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hsnapC, -⟩ := hx.hro
  exact (hsnapC hx.hsnf).1

/-- The `Ready`'s log's indices are its positions (`ReadyOutP`'s `LogIdx`, no ghost prefix). -/
theorem LdCtx.logIdx1 {R : RunCfg} {dec : CCDec} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : LdCtx R dec V net xnet G n r₁ rd S1) : LogIdx r₁.p.log := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -⟩ := hx.hro
  rw [hx.hfl] at hidx; exact hidx

/-- Bootstrapped, a `Ready`'s term at least the node's old one is past `0`. -/
theorem LdCtx.boot1 {R : RunCfg} {dec : CCDec} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : LdCtx R dec V net xnet G n r₁ rd S1)
    (hle : uint.Z (V n).ps.term ≤ uint.Z r₁.p.term) : R.boot = true → 1 ≤ uint.Z r₁.p.term := by
  intro hb
  have h1 := hx.hb.bootTermOk.1 n
  have e1 : S1.bootTerm = 1 := by
    unfold State.bootTerm; rw [hx.hc]; show (if R.boot = true then (1 : Int) else 0) = 1; simp [hb]
  rw [hx.d1] at h1; omega

/-- The binding's facts at `liftC S1` but the commits are `S1`'s. -/
theorem liftC_msgs (S : State) : (liftC S).msgs = S.msgs := rfl

/-- `InMemory` does not read the commits: it is the same at `liftC S`. -/
theorem inMemory_liftC (S : State) (n : Nat) (ev : Event) :
    (liftC S).inMemory n ev = S.inMemory n ev := rfl

end ldctx

end AntSim
end EtcdGrove
end Perennial
