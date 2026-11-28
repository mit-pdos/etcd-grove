/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's own part after its `mem` (`memNode_of`)

After `antSim_memP_in`'s `mem` (no write queued before it, no split write), the node's view is the
`Ready`'s drain phase with the `Ready`'s write queued (`mems = [rd.memRec]`), the disk unchanged.
`memNode_of`: its `NodeOkD` at `memQ` from the parts that depend on the kind of `Ready` (raft's facts,
the leader's part, the self-acknowledgement, the recorded commit, the queued write's result) and the
drain's facts; the rest is the old view's (the disk, the undo record, the reads, the jobs) or the
queued item (`QueueIs`: the item `Mem` queues is the record's, `memItem_eq`) (#33 parity B2, Sim
round 13).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemRel
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemView

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memNode
variable [GooseExts]

/-- **The item `Mem` queues is the record's** (`MemRec.item`): its `mem` report, and for a drain
caused by a `recv` the message handled (the binding's `pending[n]`, which the node's `told` clause
names: the cause, or the transfer message). -/
theorem memItem_eq {S : State} {N : Nat} {n : Fin N} {v : NodeView} {rd : ReadyD}
    (htold : Told v)
    (ht : v.told = true → (∃ m, v.cause = some m ∧ S.pending[n.val]! = [msgOf m (nodeId n)]) ∨
      (∃ x, v.xcause = some x ∧ S.pending[n.val]! = [xmsgOf x]))
    (hx : ∀ x, v.xcause = some x → x.dst = nodeId n ∧ v.cause = none) :
    (⟨evMem (nodeId n) v.byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents rd.snap true,
        if v.byE == go!"recv" then S.pending[n.val]! else []⟩ : QItem) =
      MemRec.item (nodeId n) (rd.memRec v) := by
  unfold MemRec.item ReadyD.memRec
  simp only [Bool.false_eq_true, ite_false]
  congr 1
  by_cases hb : v.byE = go!"recv"
  · simp only [hb, beq_self_eq_true, ite_true]
    rcases ht (htold hb) with ⟨m, hm, hp⟩ | ⟨x, hxc, hp⟩
    · have hxn : v.xcause = none := by
        cases hxc : v.xcause with
        | none => rfl
        | some x => rw [(hx x hxc).2] at hm; cases hm
      rw [hp, hm, hxn]; rfl
    · rw [hp, hxc, (hx x hxc).2]; rfl
  · have hb' : (v.byE == go!"recv") = false := by simpa using hb
    simp only [hb', hb, Bool.false_eq_true, ite_false]

section main
variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r : MemResult} {c : Int} {i : Int}

/-- **The node's own part after a `-parallel` leader's `mem`**: the view `w` is the `Ready`'s drain
phase (any order of its messages, `P`) with its write queued; the kind-dependent parts are premises. -/
theorem memNode_of (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (ha : R.md.async = false) (hpar : R.drv.parallel = true)
    (hm : (V n).mems = []) (htold : Told (V n))
    {r₁ : RState} {rd : ReadyD} {P : List Msg} (hrl : r₁.p.role = .leader)
    (hNF : NodeFactsD R n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hCL : ConfLag dec R { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hLP : LeaderPartD (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) n
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hpend : R.drv.batch = false → ∀ q ∈ P, PendOk R.N (nodeId n)
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } q)
    (hxpend : ∀ x ∈ rd.xmsgs, XPendOk R.N (nodeId n) (accepted r₁).p x)
    (hqs : ∀ q ∈ rd.qs,
      QsOk R (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) n
        { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } q ∨
      QsAckW n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } q)
    (hlead : LeadOk n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hvself : VoteSelf n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hDF : (V n).parts = [] → (V n).dur.write (rd.memRec (V n)) = durOf (accepted r₁))
    (hMC : MemCommitOk (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i)
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hPW : ParWriteOk R { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] }) :
    NodeOkD R dec (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) net n
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } := by
  have hsh := hs.1
  obtain ⟨d1, d2, -, d4, d5, d6, -, -, -, -, -, -, -, -, d15, d16, d17, -, -, d20, -, d22, -, d24,
    -⟩ := hs.2.2.2.2 n
  have hn6 : n.val < S.role.length := by rw [hsh.2.2.2.2.2.2.1]; exact n.isLt
  have hn13 : n.val < S.queue.length := by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt
  refine ⟨d1, ⟨?_, d2.2.1, ?_, ?_⟩, fun _ _ _ h => absurd hpar (by rw [h]; decide), d4, ?_, d6,
    hCL, hNF, hLP, fun h => absurd h (by show r₁.p.role ≠ .candidate; rw [hrl]; decide),
    hpend, fun _ h => absurd h (List.cons_ne_nil _ _), hxpend, hqs, d15, d16, d17, hlead, hvself,
    d20, ?_, ?_, fun h => absurd h (by rw [ha]; decide), d24, hMC, hPW⟩
  · show r.role[n.val]! = roleOf r₁.p.role
    rw [hok.hrole, get!_set_self _ hn6, hrl]; rfl
  · show r.config[n.val]! = _; rw [hok.hmem.1]; exact d2.2.2.1
  · show r.confAt[n.val]! = _; rw [hok.hmem.2]; exact d2.2.2.2
  · unfold QueueIs at d5 ⊢
    show (S.queue.set n.val (S.queue[n.val]! ++ [_]))[n.val]! = _
    rw [get!_set_self _ hn13, d5, hm]; rfl
  · intro hp
    show [rd.memRec (V n)].foldl DurW.write (V n).dur = durOf (accepted r₁)
    exact hDF hp
  · obtain ⟨j1, j2, j3, j4, j5, j6⟩ := d22
    obtain ⟨hj, haj⟩ := j1 ha
    refine ⟨j1, j2, j3, fun h => absurd h (by rw [ha]; decide), ?_, fun h => absurd h (by rw [ha]; decide)⟩
    show ∀ j ∈ (V n).jobs, _
    rw [hj]; intro j hj'; cases hj'

/-- **A view's commit within its log**, over the node-local context (C3: the binding's commit index
agrees with `chain` up to it, and its log is the view's). -/
theorem LdCtx.commit_le {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : LdCtx R dec V net xnet G n r₁ rd S1) : uint.Z (V n).ps.commit ≤ (V n).ps.log.length := by
  obtain ⟨-, -, hb5, -⟩ := hx.hb
  obtain ⟨h1, h2⟩ := hb5 n
  have hlen := congrArg List.length h2
  rw [hx.d3, hx.d4] at hlen
  rw [hx.d4] at h1
  simp only [List.length_take, logOf_length] at hlen
  omega

/-- **What a leader's `Ready` hands out is on the (unchanged) disk** when its log extends the view's
and its commit is within the view's log (`memNode_lead`'s `hpfx` for a win or a proposal). -/
theorem lead_pfx {v : NodeView} {r₁ : RState} {rd : ReadyD} (hro : ReadyOutP R n v r₁ rd)
    (hfl : r₁.full = r₁.p.log) (hdl : v.dur.log = v.ps.log) (hlog : v.ps.log <+: r₁.p.log)
    (hc : uint.Z r₁.p.commit ≤ v.ps.log.length) :
    v.delivered ++ rd.ce <+: v.dur.log := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := hro
  rw [hfl] at h1
  rw [hdl]
  have hcn : uint.nat r₁.p.commit ≤ v.ps.log.length := by
    have := uint_Z_nonneg r₁.p.commit
    have e : ((uint.nat r₁.p.commit : Nat) : Int) = uint.Z r₁.p.commit := by word
    omega
  exact List.prefix_of_prefix_length_le h1 hlog (Nat.le_trans h2 hcn)

/-- The disk's log is raft's (no write queued: `DiskFold`; snapshots off: no ghost prefix). -/
theorem LdCtx.dlog {r₁ : RState} {rd : ReadyD} {S1 : State}
    (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S1) : (V n).dur.log = (V n).ps.log := by
  have hfp0 : (V n).r.fp = [] := (hx.hv.facts.snap0 hx.hsnf).2.1
  rw [hx.hdn]; show (V n).r.fp ++ (V n).r.p.log = _; rw [hfp0]; rfl

/-- **A leader's entries start at the disk log's end**: a `Ready`'s first entry starts at a conflict
with the disk's log or past its end (`ReadyOutP`), at its position in the full log (`LogIdx`); when
the full log extends the disk's, there is no conflict, so it is the disk log's next index. -/
theorem first_at_end {d full ents : List EntryM} {e0 : EntryM} (hidx : LogIdx full) (hpre : d <+: full)
    (hfull : full = d.take (uint.nat e0.Index' - 1) ++ ents)
    (hconf : ∀ e ∈ d[uint.nat e0.Index' - 1]?, e.Term' ≠ e0.Term') (he : e0 ∈ ents.head?) :
    uint.Z e0.Index' = (d.length : Int) + 1 := by
  obtain ⟨t, ht⟩ := hpre
  have hj : full[(d.take (uint.nat e0.Index' - 1)).length]? = some e0 := by
    rw [hfull, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    cases ents with
    | nil => cases he
    | cons a l =>
      have : a = e0 := by simpa using he
      subst this; rfl
  have hI := hidx _ _ hj
  rw [List.length_take] at hI hj
  by_cases hlt : uint.nat e0.Index' - 1 < d.length
  · exfalso
    have hmin : min (uint.nat e0.Index' - 1) d.length = uint.nat e0.Index' - 1 :=
      Nat.min_eq_left (Nat.le_of_lt hlt)
    rw [hmin] at hj
    have h1 : d[uint.nat e0.Index' - 1]? = full[uint.nat e0.Index' - 1]? := by
      rw [← ht, List.getElem?_append_left hlt]
    rw [hj] at h1
    exact hconf e0 (by rw [h1]; rfl) rfl
  · have hmin : min (uint.nat e0.Index' - 1) d.length = d.length := Nat.min_eq_right (by omega)
    rw [hmin] at hI; exact hI

/-- **A `-parallel` leader's own part after its `mem`, over the node-local context** (`memNode_of`
with its kind-independent premises discharged by `memView_of`: `AfterOk` from `afterOk_loc` at the run
with the driver modes off and `liftC`; `CandLt` and `VoteSelf` from the leader's role; the requests
first): the kind-dependent premises left are the handed-out entries a prefix of the disk, the term
grown, the leader's part, the self-acknowledgement and the recorded commit. -/
theorem memNode_lead {msk : SimMask} (hmsk : msk ≤ mskB2) {Adm : List EntryM → CCState → Prop}
    (hin : InMask msk R net xnet) (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    {r₁ : RState} {rd : ReadyD} (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S)
    (ha : R.md.async = false) (hpar : R.drv.parallel = true)
    (hm : (V n).mems = []) (hpar0 : (V n).parts = []) (htold : Told (V n))
    (hr : ReachIn msk R dec Adm net xnet n (V n) r₁) (hrl : rd.role = .leader)
    (hlog : (V n).ps.log <+: r₁.p.log)
    (hpfx : (V n).delivered ++ rd.ce <+: (V n).dur.log)
    (hterm : uint.Z (V n).ps.term ≤ uint.Z r₁.p.term) (hlt : LogTermsLe r₁.p)
    (hLP : LeaderPartD (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) n
      (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))))
    (hqs : ∀ q ∈ rd.qs,
      QsOk R (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) n
        (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))) q ∨
      QsAckW n (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))) q)
    (hMC : MemCommitOk (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i)
      (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q)))) :
    NodeOkD R dec (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) net n
      (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))) := by
  have hro := hx.hro
  have hrl1 : r₁.p.role = .leader := hro.1.symm.trans hrl
  have hcl : CandLt r₁.p := fun hc => by rw [hrl1] at hc; cases hc
  have hP : ∀ q, q ∈ rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q) ↔ q ∈ rd.msgs :=
    fun q => by
      simp only [List.mem_append, List.mem_filter]
      cases isReqM q <;> simp
  have hA := afterOk_loc (SimMask.b1Of_le hmsk) hin.syncOff hx.hnet (nodeOk_liftC hx.hq0 hx.hv)
    hr.syncOff hro
  have hvD := hs.2.2.2.2 n
  have hsm : SelfMatchLe (nodeId n) (accepted r₁).p rd.qs :=
    selfMatchLe_ready (nodeOkD_factsS hvD).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (fun q hq ht => qsD_lead (nodeOkD_qsS hvD q hq) ht) hx.hr hro hx.d7 hx.hv.leadOk.1 hx.hin
      (fun m hm => (hx.hnet.2.2.1 m hm).2.1) hx.hqs
  obtain ⟨hNF, hCL, hpend, hxpend, hlead, hDF⟩ :=
    memView_of (P := rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q)) hA
      hvD.2.2.2.2.2.2.2.1 hpar0 hro hx.hsn hP hpfx hterm hcl hlt hsm
  have hPW : ParWriteOk R
      (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))) := by
    intro _ _ m hmem
    obtain rfl : m = rd.memRec (V n) := List.mem_singleton.mp hmem
    have hpre0 : rd.pre = false := by
      cases h : rd.pre
      · rfl
      · have := hx.hpre h; rw [hrl1] at this; cases this
    have hkk := kind_leadKeep hx.hk hrl1
    obtain ⟨-, -, -, -, -, -, hhd, -, -, -, -, -, -, -, -, hidx, -⟩ := hro
    refine ⟨rfl, hpar0, hrl, hpre0, hx.hsn, rfl, hrl1, ?_, ?_, ?_, ?_⟩
    · show (V n).dur.term = r₁.p.term; rw [hx.hdn, hkk.1]; rfl
    · show (V n).dur.vote = r₁.p.vote; rw [hx.hdn, hkk.2]; rfl
    · intro e0 he
      obtain ⟨hf, hc⟩ := hhd e0 he
      exact first_at_end (d := (V n).dur.log) hidx
        (show (V n).dur.log <+: r₁.full by rw [hx.dlog, hx.hfl]; exact hlog) hf hc he
    · show uint.Z (V n).dur.commit ≤ uint.Z r₁.p.commit
      exact commit_reachD hmsk hin hs.2.2.1 hvD hm hpar0 hr
  exact memNode_of hs hok ha hpar hm htold hrl1 hNF hCL hLP (fun _ => hpend) hxpend hqs hlead
    (fun h => hx.hvs1 h) hDF hMC hPW

end main

end memNode

end AntSim
end EtcdGrove
end Perennial
