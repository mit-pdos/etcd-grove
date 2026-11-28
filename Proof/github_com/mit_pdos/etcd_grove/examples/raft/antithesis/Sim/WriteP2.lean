/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's `write`, the binding's step and its side conditions

The node's part at its queued write (`ParWriteOk`, `DiskFold`, `DiskIs`, `MemIs`, `QueueIs`) as one
context (`WrCtx`, `wrCtx_of`); the write's `Step` (`write_of`, `OnDisk` of the queued item) and its
`WriteOk` for a leader's store (`wr_lstore`: a win's empty entry or a proposal, its commit kept) and
for a write with nothing stored and the commit kept (`wr_lsame`) (#33 parity B2, Sim round 21).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.WriteRel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section writeP2
variable [GooseExts]

/-- A list's prefix of length `k` equal to another's (of length at least `k`) bounds its length. -/
theorem le_of_take_eq {α : Type} {a b : List α} {k : Nat} (hk : k ≤ a.length) (h : a.take k = b.take k) :
    k ≤ b.length := by
  have := congrArg List.length h
  rw [List.length_take, List.length_take] at this
  omega

/-- **A `-parallel` leader's queued write, at the binding**: what `ParWriteOk`, `DiskFold`, `DiskIs`,
`MemIs` and `QueueIs` say of node `n` with the one queued `mem` `m`. -/
structure WrCtx (R : RunCfg) (S : State) (n : Fin R.N) (v : NodeView) (m : MemRec) : Prop where
  hm : v.mems = [m]
  hpar0 : v.parts = []
  hrole : m.role = .leader
  hpre : m.pre = false
  hsn : m.snap = none
  hbat : m.bat = false
  hpl : v.ps.role = .leader
  hdt : v.dur.term = v.ps.term
  hdv : v.dur.vote = v.ps.vote
  hfirst : ∀ e0 ∈ m.ents.head?, uint.Z e0.Index' = (v.dur.log.length : Int) + 1
  hdc : uint.Z v.dur.commit ≤ uint.Z v.ps.commit
  hec : m.ents = [] ∨ m.commit = v.dur.commit
  hidx : LogIdx (v.dur.write m).log
  hw : v.dur.write m = durOf v.r
  hT : S.currentTerm[n.val]! = uint.Z m.term
  hV : S.vote n.val = nameOf m.vote
  hlog : S.log[n.val]! = logOf v.dur.log
  hcm : S.commitIndex[n.val]! = uint.Z v.dur.commit
  hro : S.role[n.val]! = leader
  hq : S.queue[n.val]! = [MemRec.item (nodeId n) m]

variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {m : MemRec}

theorem wrCtx_of {rest : List MemRec} (hv : NodeOkD R dec S net n (V n)) (ha : R.md.async = false)
    (hbat : R.drv.batch = false) (hm : (V n).mems = m :: rest) : rest = [] ∧ WrCtx R S n (V n) m := by
  obtain ⟨d1, d2, -, -, d5, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d21, -, -, -, -, d26⟩ := hv
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
    d26 ha hbat m (by rw [hm]; exact List.mem_cons_self ..)
  have hrest : rest = [] := by rw [hm] at p1; exact (List.cons.inj p1).2
  have hw : (V n).dur.write m = durOf (V n).r := by
    have h := d21 p2; rw [p1] at h; exact h
  have hmt : m.term = (V n).ps.term := congrArg DurW.term hw
  have hmv : m.vote = (V n).ps.vote := congrArg DurW.vote hw
  refine ⟨hrest, ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, hw,
    by rw [d1.1, p8, hmt], by rw [d1.2.1, p9, hmv], d1.2.2.1, d1.2.2.2,
    by rw [d2.1, p7]; rfl, by unfold QueueIs at d5; rw [d5, p1]; rfl⟩⟩

theorem WrCtx.mt (hx : WrCtx R S n (V n) m) : m.term = (V n).ps.term := congrArg DurW.term hx.hw
theorem WrCtx.mv (hx : WrCtx R S n (V n) m) : m.vote = (V n).ps.vote := congrArg DurW.vote hx.hw
theorem WrCtx.mc (hx : WrCtx R S n (V n) m) : m.commit = (V n).ps.commit := congrArg DurW.commit hx.hw
theorem WrCtx.mlog (hx : WrCtx R S n (V n) m) : ((V n).dur.write m).log = (V n).r.full :=
  congrArg DurW.log hx.hw

/-- The queued item's report and message. -/
theorem WrCtx.hq' (hx : WrCtx R S n (V n) m) :
    S.queue[n.val]! = ⟨evMem (nodeId n) m.byE (roleStr m.pre m.role) m.term m.vote m.commit m.ents m.snap
      true, (MemRec.item (nodeId n) m).m⟩ :: [] := by
  rw [hx.hq]; unfold MemRec.item; rw [hx.hbat]; rfl

theorem WrCtx.rs (hx : WrCtx R S n (V n) m) : roleStr m.pre m.role = roleOf .leader := by
  rw [hx.hpre, hx.hrole]; rfl

/-- The binding's `MemCommit` at the queued write: its commit. -/
theorem WrCtx.memCommit (hx : WrCtx R S n (V n) m) : S.memCommit n.val = .ok (uint.Z m.commit) := by
  unfold AntCheck.State.memCommit; rw [hx.hq]; unfold MemRec.item; rw [hx.hbat]; rfl

/-- The write's step from its `OnDisk`: `Write` pops the item, `Step` counts it. -/
theorem wr_step (hs : AntSimD R dec S V net xnet) (hx : WrCtx R S n (V n) m) {L1 : List Entry} {c : Int}
    {cf : Confirmed} {M : List Fact} {p : Pre} {ch : List Entry} {tl : TermFn Int}
    (hod : S.onDisk n.val ⟨evReady (nodeId n) m.byE (roleOf .leader) m.term m.vote m.commit m.ents,
        (MemRec.item (nodeId n) m).m⟩ false S.role S.leaders S.ledLog S.chain S.termLen S.viol =
      .ok (some (odS S n.val (uint.Z m.term) none L1 c S.role cf M S.votes S.leaders S.ledLog p ch tl
        S.viol))) :
    S.step (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap) =
      .ok (some (wrS S n.val L1 c cf M p ch tl [])) := by
  have hc : S.cfg = R.cfg := hs.1.1
  have hnl : n.val < S.currentTerm.length := by rw [hs.1.2.1]; exact n.isLt
  have hw := write_of (S := S) (n := n.val) (nodeId n) m.byE (roleStr m.pre m.role) m.term m.vote m.commit
    m.ents m.snap _ [] hx.hq' (by rw [hx.rs, hx.hsn]; exact hod)
  rw [step_evWrite n hc, hw, ← odS_wrS S n.val hnl, hx.hT]
  rfl

/-- The leader's full log is certified (its leader log is, `GlobalOk`). -/
theorem wr_fullG (hgo : GlobalOk R S net G) (hx : WrCtx R S n (V n) m)
    (hll : S.ledLog.get (uint.Z (V n).ps.term) = .ok (logOf (V n).r.full)) :
    ∃ l ∈ G.logs, logOf (V n).r.full = logOf l := by
  rcases hgo.2.2.2.1 _ (TermFn.mem_of_get hll) with ⟨-, hp⟩ | ⟨l, hl', hp, -⟩
  · exact ⟨bootLog R, hgo.2.2.2.2.2.2.2.1, (Prod.mk.inj hp).2⟩
  · exact ⟨l, hl', hp⟩

set_option maxHeartbeats 4000000 in
/-- **A leader's store at its write** (a win's empty entry, a proposal): `OnDisk`'s store
(`onDisk_lstore`) of raft's full log (the disk's with the entries appended at its end,
`ParWriteOk`), the commit kept; `WriteOk` with `chain` and `termLen` kept, the leader's
acknowledgement of its last index added and confirmed. -/
theorem wr_lstore (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G) (hl : RaftLaws G)
    (hx : WrCtx R S n (V n) m) {e : EntryM} {es' : List EntryM} (he : m.ents = e :: es') :
    ∃ p, S.step (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap) =
        .ok (some (wrS S n.val (logOf (V n).r.full) (uint.Z m.commit)
          { term := uint.Z m.term, index := ((V n).r.full.length : Int) }
          (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z m.term)
            ((V n).r.full.length : Int))) p S.chain S.termLen [])) ∧
      WriteOk R S G n (logOf (V n).r.full) (uint.Z m.commit)
          { term := uint.Z m.term, index := ((V n).r.full.length : Int) }
          (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z m.term)
            ((V n).r.full.length : Int))) p S.chain S.termLen [] := by
  have hsh := hs.1
  have hc : S.cfg = R.cfg := hsh.1
  have hv := hs.2.2.2.2 n
  obtain ⟨⟨-, hb2, hb3, hb4, hb5, -, -, -, -, -, -, -, -, -, hb15, -, hb17, -⟩, -⟩ := hs.2.1
  obtain ⟨lp1, lp2, -, -, -⟩ := hv.2.2.2.2.2.2.2.2.1 hx.hpl
  have hmt := hx.mt
  have hf := hx.hfirst e (by rw [he]; rfl)
  have hnat : uint.nat e.Index' - 1 = (V n).dur.log.length := by word
  have hfull : (V n).r.full = (V n).dur.log ++ e :: es' := by
    rw [← hx.mlog]; unfold DurW.write; simp only [he, List.head?_cons]; rw [hnat, List.take_length]
  have hc0 : (uint.Z e.Index' - 1).toNat = (V n).dur.log.length := by omega
  have hL1 : (S.log[n.val]!).take (uint.Z e.Index' - 1).toNat ++ logOf (e :: es') = logOf (V n).r.full := by
    rw [hx.hlog, hc0, show (V n).dur.log.length = (logOf (V n).dur.log).length from (logOf_length _).symm,
      List.take_length, hfull]
    unfold logOf; rw [List.map_append]
  have hlen : uint.Z e.Index' - 1 + ((es'.length + 1 : Nat) : Int) = ((V n).r.full.length : Int) := by
    rw [hfull, List.length_append, List.length_cons]; push_cast; omega
  have hcm : uint.Z m.commit = S.commitIndex[n.val]! := by
    rcases hx.hec with h | h
    · rw [he] at h; cases h
    · rw [hx.hcm, h]
  have hll : S.ledLog.get (uint.Z m.term) = .ok (logOf (V n).r.full) := by rw [hmt]; exact lp2
  obtain ⟨L, hLG, hLeq⟩ := wr_fullG hgo hx lp2
  have hsend : sendableIn S.leaders S.ledLog S.chain S.termLen (AppendFact.mk (nameOf (nodeId n))
      (nameOf (nodeId n)) (uint.Z m.term) (uint.Z e.Index' - 1)
      (termAt (logOf (V n).r.full) (uint.Z e.Index' - 1)) (logOf (e :: es')) 0) = .ok true := by
    have h := sendable_leader (S := S) (src := nameOf (nodeId n)) (dst := nameOf (nodeId n))
      (lg := (V n).r.full) (T := uint.Z m.term) (p := (V n).dur.log.length)
      (pt := termAt (logOf (V n).r.full) ((V n).dur.log.length : Int)) (es := e :: es') (c := 0)
      (by rw [hmt]; exact lp1) hll rfl (by rw [hfull]; simp) (by rw [hfull]; simp) (.inl rfl)
    have e1 : (((V n).dur.log.length : Nat) : Int) = uint.Z e.Index' - 1 := by omega
    rw [e1] at h; exact h
  obtain ⟨eqb, heqb⟩ := entriesEqual_logOf (V n).r.full (V n).dur.log
  have hcd : (uint.Z m.commit).toNat ≤ (logOf (V n).dur.log).length := by
    obtain ⟨h1, h2⟩ := hb3 n
    rw [hx.hlog] at h2
    have := le_of_take_eq (k := (S.commitIndex[n.val]!).toNat) (by omega) h2
    rw [← hcm] at this; exact this
  have hpfx : logOf (V n).dur.log <+: logOf (V n).r.full := by
    rw [hfull]; unfold logOf; rw [List.map_append]; exact List.prefix_append _ _
  have hch : S.chain.take (uint.Z m.commit).toNat = (logOf (V n).r.full).take (uint.Z m.commit).toNat := by
    rw [rr_take_prefix hpfx hcd, hcm, (hb3 n).2, hx.hlog]
  obtain ⟨p, hpm, hpc, hpms, hod⟩ := onDisk_lstore n hc m.byE m.term m.vote m.commit e es'
    (MemRec.item (nodeId n) m).m S.role S.leaders S.ledLog S.chain S.termLen S.viol (logOf (V n).r.full) eqb
    hx.hT.symm hx.hV.symm hx.hro (by rw [hx.hlog, logOf_length]; exact hf) hll hsend hcm
    (by rw [hL1, hx.hlog]; exact heqb)
    (by rw [hL1, hLeq]; exact lm_ok hl hLG hgo.2.2.1 hsh.2.2.2.2.1)
    (by rw [hcm]; exact (hb3 n).1) (by rw [hL1]; exact hch)
  rw [hL1, hlen] at hod
  rw [hL1] at hpm
  rw [hlen] at hpms
  have hT := hx.hT
  have hackN : ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z m.term) ((V n).r.full.length : Int) ∈
      lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z m.term)
        ((V n).r.full.length : Int)) := mem_lset_add.mpr (.inr rfl)
  have hq0 : (S.queue.set n.val [])[n.val]! = [] :=
    get!_set_self _ (by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
  have hmc : (wrS S n.val (logOf (V n).r.full) (uint.Z m.commit)
      { term := uint.Z m.term, index := ((V n).r.full.length : Int) }
      (lset.add S.msgs (ackFact (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z m.term)
        ((V n).r.full.length : Int))) p S.chain S.termLen []).memCommit n.val = .ok (uint.Z m.commit) := by
    rw [memCommit_nil hq0]
    exact congrArg Except.ok (get!_set_self _ (by rw [hsh.2.2.2.2.2.1]; exact n.isLt))
  obtain ⟨c0, h0, h1, h2⟩ := hb15.2 n hx.hro
  rw [hx.memCommit] at h0
  obtain rfl : c0 = uint.Z m.commit := (Except.ok.inj h0).symm
  have hcdZ : uint.Z m.commit ≤ ((logOf (V n).dur.log).length : Int) := by
    have := uint_Z_nonneg m.commit; omega
  have htA : termAt (logOf (V n).r.full) (uint.Z m.commit) = termAt (S.log[n.val]!) (uint.Z m.commit) := by
    rw [hx.hlog, hfull]; unfold logOf; rw [List.map_append]; exact rr_termAt_append _ _ _ hcdZ
  refine ⟨p, wr_step hs hx (by rw [he]; exact hod), ?_⟩
  exact {
    lead := hx.hro
    lself := by rw [hT]; exact List.contains_iff_mem.mp (by rw [hmt]; exact lp1)
    cge := Int.le_of_eq hcm.symm
    mcSelf := ⟨_, hmc, fun h => h1 (by rw [← htA]; exact h), h2⟩
    mcGe := fun c0 h => by rw [hx.memCommit] at h; cases h; exact ⟨_, hmc, Int.le_refl _⟩
    pre := hpm
    pconf := hpc
    pmsgs := fun a => by rw [hpms]; exact lset_minus_mem
    msub := fun f hf => mem_lset_add.mpr (.inl hf)
    mnew := fun f hf hn => by
      rcases mem_lset_add.mp hf with h | h
      · exact absurd h hn
      · subst h
        exact ⟨rfl, rfl, ⟨n, rfl⟩, hT.symm, .inl ⟨rfl, Int.le_refl _⟩⟩
    cmono := .inr ⟨hT.symm, TermFn.has_of_get hll, fun ht => by
      obtain ⟨o1, o2, -⟩ := hb5 n (logOf (V n).r.full) (by rw [ht]; exact hll)
      rw [logOf_length] at o2; exact o2⟩
    hconf := fun l hl' => by
      change S.ledLog.get (uint.Z m.term) = .ok l at hl'
      rw [hll] at hl'; cases hl'
      exact ⟨by rw [logOf_length]; exact Int.le_refl _, by rw [logOf_length]; exact Int.le_refl _, rfl⟩
    hchain := List.prefix_refl _
    chainC := ⟨by rw [hcm]; exact (hb3 n).1, hch⟩
    tlLen := hb2
    tlC := by
      rcases hb4 n with h | ⟨q, hq, e1, e2⟩
      · exact .inl (by rw [hcm]; exact h)
      · exact .inr ⟨q, hq, e1, by rw [hcm]; exact e2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    tlSort := hb17
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    chainG := hgo.2.2.2.2.1
    tlG := hgo.2.2.2.2.2.1
    logG := ⟨L, hLG, hLeq⟩ }

set_option maxHeartbeats 4000000 in
/-- **A leader's write with nothing stored and its commit kept** (`onDisk_lsame`): the binding's log,
commit, confirmation, facts, `chain` and `termLen` kept; `WriteOk`. -/
theorem wr_lsame (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G)
    (hx : WrCtx R S n (V n) m) (he : m.ents = []) (hcs : m.commit = (V n).dur.commit) :
    ∃ p, S.step (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap) =
        .ok (some (wrS S n.val (S.log[n.val]!) (uint.Z m.commit) (S.confirmed[n.val]!) S.msgs p S.chain
          S.termLen [])) ∧
      WriteOk R S G n (S.log[n.val]!) (uint.Z m.commit) (S.confirmed[n.val]!) S.msgs p S.chain S.termLen [] := by
  have hsh := hs.1
  have hc : S.cfg = R.cfg := hsh.1
  have hv := hs.2.2.2.2 n
  obtain ⟨⟨-, hb2, hb3, hb4, -, -, -, -, -, -, -, -, -, -, hb15, -, hb17, -⟩, -⟩ := hs.2.1
  obtain ⟨lp1, lp2, -, -, -⟩ := hv.2.2.2.2.2.2.2.2.1 hx.hpl
  have hmt := hx.mt
  have hcm : uint.Z m.commit = S.commitIndex[n.val]! := by rw [hx.hcm, hcs]
  have hll : S.ledLog.get (uint.Z m.term) = .ok (logOf (V n).r.full) := by rw [hmt]; exact lp2
  obtain ⟨L, hLG, hLeq⟩ := wr_fullG hgo hx lp2
  have hsend : sendableIn S.leaders S.ledLog S.chain S.termLen (AppendFact.mk (nameOf (nodeId n))
      (nameOf (nodeId n)) (uint.Z m.term) 0 0 [] 0) = .ok true := by
    have h := sendable_leader (S := S) (src := nameOf (nodeId n)) (dst := nameOf (nodeId n))
      (lg := (V n).r.full) (T := uint.Z m.term) (p := 0) (pt := 0) (es := []) (c := 0)
      (by rw [hmt]; exact lp1) hll (by unfold termAt; simp) (Nat.zero_le _) rfl (.inl rfl)
    exact h
  obtain ⟨p, hpm, hpc, hpms, hod⟩ := onDisk_lsame n hc m.byE m.term m.vote m.commit
    (MemRec.item (nodeId n) m).m S.role S.leaders S.ledLog S.chain S.termLen S.viol
    hx.hT.symm hx.hV.symm hx.hro hsend hcm
  have hT := hx.hT
  have hq0 : (S.queue.set n.val [])[n.val]! = [] :=
    get!_set_self _ (by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
  have hmc : (wrS S n.val (S.log[n.val]!) (uint.Z m.commit) (S.confirmed[n.val]!) S.msgs p S.chain
      S.termLen []).memCommit n.val = .ok (uint.Z m.commit) := by
    rw [memCommit_nil hq0]
    exact congrArg Except.ok (get!_set_self _ (by rw [hsh.2.2.2.2.2.1]; exact n.isLt))
  obtain ⟨c0, h0, h1, h2⟩ := hb15.2 n hx.hro
  rw [hx.memCommit] at h0
  obtain rfl : c0 = uint.Z m.commit := (Except.ok.inj h0).symm
  refine ⟨p, wr_step hs hx (by rw [he]; exact hod), ?_⟩
  exact {
    lead := hx.hro
    lself := by rw [hT]; exact List.contains_iff_mem.mp (by rw [hmt]; exact lp1)
    cge := Int.le_of_eq hcm.symm
    mcSelf := ⟨_, hmc, h1, h2⟩
    mcGe := fun c0 h => by rw [hx.memCommit] at h; cases h; exact ⟨_, hmc, Int.le_refl _⟩
    pre := hpm
    pconf := hpc
    pmsgs := fun a => by rw [hpms]; exact lset_minus_mem
    msub := fun f hf => hf
    mnew := fun f hf hn => absurd hf hn
    cmono := .inl rfl
    hconf := fun l hl' => hs.2.1.1.2.2.2.2.1 n l hl'
    hchain := List.prefix_refl _
    chainC := ⟨by rw [hcm]; exact (hb3 n).1, by rw [hcm]; exact (hb3 n).2⟩
    tlLen := hb2
    tlC := by
      rcases hb4 n with h | ⟨q, hq, e1, e2⟩
      · exact .inl (by rw [hcm]; exact h)
      · exact .inr ⟨q, hq, e1, by rw [hcm]; exact e2⟩
    tlDom := fun q hq => ⟨q, hq, rfl, Int.le_refl _⟩
    tlSort := hb17
    tlMono := fun _ => Int.le_refl _
    tlNew := fun _ h => absurd h (Int.lt_irrefl _)
    chainG := hgo.2.2.2.2.1
    tlG := hgo.2.2.2.2.2.1
    logG := hgo.2.2.1 n }

end writeP2

end AntSim
end EtcdGrove
end Perennial
