/-
Lean-first (no Rocq counterpart).

# Parity B2: the B1 kinds over the B2 relation (`AntSimD`)

The steps every report shares, over `AntSimD` (#33 parity B2, round 3):

- **`GC`** (`antSim_gcD`): the `GC` steps keep `AntSimD`, its `EffTerm` forms included (`Garbage` and
  `OldVotes` read `EffTerm`, `StaleLed` reads `Over`, B 696-711), in a run without batching (a batch's
  pending messages, `PendOkB`, name vote records and vote requests with no bound on their term, which
  `GC` may drop: `notes/antithesis-parity-b2.md`, round 3).
- **The checker's prefix is a function of the events** (`Prefix.unique`): a B1 statement's post-state is
  the one any other proof of the same step computes, so the `AntSimD` bookkeeping is proved of that
  state alone.
- **`recv`**, **`readreq`**, **`read`** (`antSim_recvD_in`, `antSim_readreqD_in`, `antSim_readD_in`) for
  every mask below `mskB2` without batching.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.B1Carry
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Reads

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section carryd
variable [GooseExts] {R : RunCfg}

/-! ## The prefix and the mask -/

/-- The checker's state after a prefix is unique. -/
theorem Prefix.unique {cfg : AntCheck.Config} {evs : List Event} {S S' : State} (h : Prefix cfg evs S)
    (h' : Prefix cfg evs S') : S = S' := by
  obtain ⟨c, hc, -, rfl⟩ := h
  obtain ⟨c', hc', -, rfl⟩ := h'
  rw [hc] at hc'
  injection hc' with h
  rw [h]

/-- B2's mask has no snapshot, no conf change and no forwarding. -/
theorem InMask.b2 {msk : SimMask} (hmsk : msk ≤ mskB2) {net : List Msg} {xnet : List XMsg}
    (h : InMask msk R net xnet) :
    R.md.snapshots = false ∧ R.md.confChanges = false ∧ R.md.forwarding = false := by
  obtain ⟨⟨-, -, -, -, a5, a6, a7, -, -⟩, -⟩ := hmsk
  obtain ⟨⟨-, -, -, -, b5, b6, b7, -, -⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rw [Bool.eq_false_iff] <;> intro hx
  · exact absurd (a6 (b6 hx)) (by simp [mskB2])
  · exact absurd (a7 (b7 hx)) (by simp [mskB2])
  · exact absurd (a5 (b5 hx)) (by simp [mskB2])

/-! ## `GC` over `EffTerm` -/

theorem over_falseE {S : State} (hc : S.cfg = R.cfg) {t : Int} (j : Fin R.N) (h : S.effTerm j.val ≤ t) :
    S.over t = false := by
  unfold State.over
  rw [server_length hc]
  cases h' : (List.range R.N).all (fun j => decide (S.effTerm j > t))
  · rfl
  · rw [List.all_eq_true] at h'
    have h1 := h' j.val (List.mem_range.mpr j.isLt)
    simp only [decide_eq_true_eq] at h1
    omega

theorem over_true_lt {S : State} (hc : S.cfg = R.cfg) {t : Int} (h : S.over t = true) (i : Fin R.N) :
    t < S.effTerm i.val :=
  Int.lt_of_not_ge fun hle => by rw [over_falseE hc i hle] at h; cases h

section keepE
variable {S : State} {g : List Fact} {o : List VoteRec}
variable (hc : S.cfg = R.cfg) (hg : S.garbage = .ok g)
include hc hg

theorem gcRes_grant_keepE {f : Fact} (h : f ∈ S.msgs) (ht : f.type = go!"grant") (j : Fin R.N)
    (hd : f.dst = nameOf (nodeId j)) (hle : S.effTerm j.val ≤ f.term) : f ∈ (gcRes S g o).msgs := by
  refine lset_minus_mem.mpr ⟨h, fun hf => ?_⟩
  have := garbage_grant hc hg hf ht j hd
  omega

theorem gcRes_ack_keepE {src : Str} {t k : Int} (j : Fin R.N) (h : AckIn S src (nameOf (nodeId j)) t k)
    (hle : S.effTerm j.val ≤ t) : AckIn (gcRes S g o) src (nameOf (nodeId j)) t k := by
  obtain ⟨a, ha, hP, hmax⟩ := exists_max (fun a : Fact => a.index)
    (fun a => a.type = go!"ack" ∧ a.src = src ∧ a.dst = nameOf (nodeId j) ∧ a.term = t ∧ k ≤ a.index)
    S.msgs (by obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h; exact ⟨a, ha, h1, h2, h3, h4, h5⟩)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  refine ⟨a, lset_minus_mem.mpr ⟨ha, fun hag => ?_⟩, h1, h2, h3, h4, h5⟩
  rcases garbage_ack hc hg hag h1 j h3 with he | ⟨b, hb, hb1, hb2, hb3, hb4, hb5⟩
  · omega
  · have := hmax b hb ⟨hb1, hb2.trans h2, hb3.trans h3, hb4.trans h4, by omega⟩
    omega

/-- `Garbage`'s domination of an ack is by one outside its sender's undo record (B 700-704). -/
theorem garbage_ackU {f : Fact} (hf : f ∈ g) (ht : f.type = go!"ack") (j : Fin R.N)
    (hd : f.dst = nameOf (nodeId j)) (i : Fin R.N) (hs : f.src = nameOf (nodeId i)) :
    S.effTerm j.val > f.term ∨ ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = f.src ∧ a.dst = f.dst ∧
      a.term = f.term ∧ a.index > f.index ∧ ∀ u, S.undo[i.val]! = some u → a ∉ u.msgs := by
  unfold State.garbage at hg
  have h := (filterM_mem hg hf).2
  simp (config := { decide := true }) only [ht, hd, idx_name hc, ite_true, ite_false, epure, eok_bind,
    Bool.false_eq_true] at h
  by_cases he : S.effTerm j.val > f.term
  · exact .inl he
  · right
    rw [if_neg (by simpa using he)] at h
    obtain ⟨a, ha, h⟩ := anyM_true h
    refine ⟨a, ha, ?_⟩
    by_cases hcond : (a.type == go!"ack" && a.src == f.src && a.dst == nameOf (nodeId j) && a.term == f.term &&
        decide (a.index > f.index)) = true
    · rw [if_pos hcond] at h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
      rw [h2, hs, idx_name hc, eok_bind] at h
      refine ⟨h1, h2, h3.trans hd.symm, h4, h5, fun u hu hm => ?_⟩
      rw [hu] at h
      simp only [epure] at h
      simp at h
      exact h hm
    · rw [if_neg hcond] at h; cases h

/-- `GC` keeps an ack outside its sender's undo record, with any property its being outside gives. -/
theorem gcRes_ackG_keepE {t k : Int} (i j : Fin R.N) (Q : Fact → Prop)
    (hQ : ∀ a, (∀ u, S.undo[i.val]! = some u → a ∉ u.msgs) → Q a)
    (h : ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = nameOf (nodeId i) ∧ a.dst = nameOf (nodeId j) ∧
      a.term = t ∧ k ≤ a.index ∧ Q a)
    (hle : S.effTerm j.val ≤ t) :
    ∃ a ∈ (gcRes S g o).msgs, a.type = go!"ack" ∧ a.src = nameOf (nodeId i) ∧
      a.dst = nameOf (nodeId j) ∧ a.term = t ∧ k ≤ a.index ∧ Q a := by
  obtain ⟨a, ha, hP, hmax⟩ := exists_max (fun a : Fact => a.index)
    (fun a => a.type = go!"ack" ∧ a.src = nameOf (nodeId i) ∧ a.dst = nameOf (nodeId j) ∧ a.term = t ∧
      k ≤ a.index ∧ Q a) S.msgs h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  refine ⟨a, lset_minus_mem.mpr ⟨ha, fun hag => ?_⟩, h1, h2, h3, h4, h5, h6⟩
  rcases garbage_ackU hc hg hag h1 j h3 i h2 with he | ⟨b, hb, hb1, hb2, hb3, hb4, hb5, hb6⟩
  · omega
  · have := hmax b hb ⟨hb1, hb2.trans h2, hb3.trans h3, hb4.trans h4, by omega, hQ b hb6⟩
    omega

theorem gcRes_ackD_keepE {t k : Int} (i j : Fin R.N) (h : AckInD S i (nameOf (nodeId j)) t k)
    (hle : S.effTerm j.val ≤ t) : AckInD (gcRes S g o) i (nameOf (nodeId j)) t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨b, hb, b1, b2, b3, b4, b5, b6⟩ := gcRes_ackG_keepE hc hg i j (AckOut S i)
    (fun a ha' u hu _ => ha' u hu) ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ hle
  exact ⟨b, hb, b1, b2, b3, b4, b5, b6⟩

theorem gcRes_ackX_keep {t k : Int} (n j : Fin R.N) (h : AckInX S n j t k)
    (hle : S.currentTerm[n.val]! ≤ t) : AckInX (gcRes S g o) n j t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨b, hb, b1, b2, b3, b4, b5, b6⟩ := gcRes_ackG_keepE hc hg j n (fun a => j ≠ n → AckOut S j a)
    (fun a ha' _ u hu _ => ha' u hu) ⟨a, ha, h1, h2, h3, h4, h5, h6⟩
    (Int.le_trans (effTerm_le S n.val) hle)
  exact ⟨b, hb, b1, b2, b3, b4, b5, b6⟩

/-- `GC` keeps the restart facts. -/
theorem gc_undoBindOk (h : UndoBindOk R.N S) : UndoBindOk R.N (gcRes S g o) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun T hT => ?_, fun j => ?_, fun j u hu hm => ?_⟩
  · rcases h1 T hT with ⟨l, hl, hlt⟩ | h
    · cases hov : S.over l.term
      · exact .inl ⟨l, gcRes_leaders_keep hl hov, hlt⟩
      · exact .inr fun i => by rw [← hlt]; exact over_true_lt hc hov i
    · exact .inr h
  · rcases h2 j with h | h | h
    · exact .inl h
    · cases hov : S.over (S.confirmed[j.val]!).term
      · exact .inr (.inl ((gcRes_has (g := g) (o := o) hov).trans h))
      · exact .inr (.inr fun i => over_true_lt hc hov i)
    · exact .inr (.inr h)
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 j u hu hm
    exact ⟨a1, a2, a3, a4, a5, a6, fun a ha => a7 a (gcRes_msgs_sub ha),
      fun a ha => a8 a (gcRes_msgs_sub ha)⟩

/-- `GC` keeps C4 over `EffTerm`. -/
theorem gc_netOkD {net : List Msg} (h : NetOkD R S net) : NetOkD R (gcRes S g o) net := by
  obtain ⟨h1, hrest⟩ := h
  refine ⟨fun m hm => ?_, hrest⟩
  obtain ⟨hty, hsrc, j, hdst, hj⟩ := h1 m hm
  refine ⟨hty, hsrc, j, hdst, fun hle => ?_⟩
  obtain ⟨r1, r2, r3, r4⟩ := hj hle
  have hov : S.over (uint.Z m.term) = false := over_falseE hc j hle
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · have := r1 ht
    rw [toAppendFact_msgOf, eok_bind] at this ⊢
    rw [sendable_gc hov]; exact this
  · obtain ⟨f, hf, hfm⟩ := r2 ht
    rw [voteFact_msgOf] at hf; cases hf
    exact ⟨_, voteFact_msgOf m m.dst, gcRes_vote_keep hc hg hfm rfl hov⟩
  · exact gcRes_grant_keepE hc hg (r3 ht) rfl j (by rw [hdst]) hle
  · intro i hi
    have := r4 ht i hi
    rw [hdst] at this ⊢
    exact gcRes_ackD_keepE hc hg i j this hle

/-- `GC` keeps a node's part, without batching. -/
theorem gc_nodeOkD (ho : S.oldVotes = .ok o) {dec : CCDec} {net : List Msg} (hbat : R.drv.batch = false)
    (n : Fin R.N) {v : NodeView} (h : NodeOkD R dec S net n v) : NodeOkD R dec (gcRes S g o) net n v := by
  obtain ⟨hd, hM, hSy, hU, hQu, hR, hCL, hF, hL, hC, hP, -, hX, hQ, hT, hca, hxc, hlo, hvs, hex⟩ := h
  have hct : S.currentTerm[n.val]! ≤ uint.Z v.ps.term := by rw [hd.1]; exact hF.2.2.2.2.2.2.2.1
  have hov : S.over (uint.Z v.ps.term) = false := over_false hc n hct
  refine ⟨hd, hM, hSy, hU, hQu, hR, hCL, hF, ?_, ?_, hP, (fun hb => by rw [hbat] at hb; cases hb), hX, ?_,
    hT, hca, hxc, hlo, hvs, hex⟩
  · intro hlead
    obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := hL hlead
    refine ⟨?_, ?_, ?_, ?_, hl5⟩
    · exact List.contains_iff_mem.mpr (gcRes_leaders_keep (List.contains_iff_mem.mp hl1) hov)
    · rw [gcRes_get hov]; exact hl2
    · intro j k hk hkt
      exact gcRes_ackX_keep hc hg n j (hl3 j k hk hkt) hct
    · intro j hj
      rcases hl4 j hj with h | h
      · exact .inl h
      · exact .inr (gcRes_ackX_keep hc hg n j h hct)
  · intro hcand
    obtain ⟨hC1, hC2⟩ := hC hcand
    refine ⟨fun j hj => ?_, fun hdt => gcRes_vote_keep hc hg (hC2 hdt) rfl (over_false hc n (Int.le_refl _))⟩
    have := hC1 j hj
    have heq : (gcRes S g o).granted n.val = S.granted n.val := by
      refine granted_congr (s1 := gcRes S g o) (s := S) n.val rfl rfl ?_ ?_
      · intro x
        refine contains_eq_of gcRes_msgs_sub (fun h => gcRes_grant_keep hc hg h rfl n
          (server_of hc n) (Int.le_refl _))
      · exact contains_eq_of gcRes_votes_sub (fun h => gcRes_votes_keep hc ho h n
          (server_of hc n) (Int.le_refl _))
    rw [heq]; exact this
  · intro q hq
    refine (hQ q hq).elim (fun hQ' => Or.inl ?_) Or.inr
    obtain ⟨q1, q2, q4, ⟨q3, q5⟩ | q6⟩ := hQ'
    · refine ⟨q1, q2, q4, .inl ⟨q3, ?_⟩⟩
      rcases q5 with ⟨h1, h0, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, h0, gcRes_ack_keep hc hg n h2 hct⟩
      · exact .inr ⟨h1, gcRes_votes_keep hc ho h2 n rfl hct⟩
    · exact ⟨q1, q2, q4, .inr q6⟩

end keepE

/-- **One `GC` step keeps `AntSimD`** (without batching). -/
theorem gc_relD {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg}
    {G : RaftFacts} {g : List Fact} {o : List VoteRec} (hbat : R.drv.batch = false)
    (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G) (hg : S.garbage = .ok g)
    (ho : S.oldVotes = .ok o) : AntSimD R dec (gcRes S g o) V net xnet ∧ GlobalOk R (gcRes S g o) net G := by
  obtain ⟨hsh, ⟨hb, hu⟩, hn, hxn, hno⟩ := hs
  have hc : S.cfg = R.cfg := hsh.1
  refine ⟨⟨hsh, ⟨gc_bindingOkM hc hb hg ho, gc_undoBindOk hc hg hu⟩, gc_netOkD hc hg hn, hxn,
    fun n => gc_nodeOkD hc hg ho hbat n (hno n)⟩, ?_⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hgo
  exact ⟨fun l hl => g1 l (gcRes_leaders_sub hl), fun v hv => g2 v (gcRes_votes_sub hv), g3,
    fun p hp => g4 p (gcRes_ledLog_sub hp).1, g5, g6, g7, g8, g9⟩

theorem gcLoop_relD {dec : CCDec} {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg}
    {G : RaftFacts} (hl : RaftLaws G) (hbat : R.drv.batch = false) :
    ∀ (k : Nat) (S : State), gcM S < k → AntSimD R dec S V net xnet → GlobalOk R S net G →
      ∃ S', gcLoop k S = .ok (S', none) ∧ AntSimD R dec S' V net xnet ∧ GlobalOk R S' net G
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, S, hlt, hs, hgo => by
    have hc : S.cfg = R.cfg := hs.1.1
    obtain ⟨g, hg⟩ := garbage_ok hc (BindingOkM.factsWf hs.2.1.1)
    obtain ⟨o, ho⟩ := oldVotes_ok hc (BindingOkM.factsWf hs.2.1.1)
    cases hd : (decide (g.length + o.length ≥ gcBatch) || S.staleLed.length != 0)
    · refine ⟨S, ?_, hs, hgo⟩
      rw [gcLoop, gcDue_eq hg ho, hd]; rfl
    · obtain ⟨hs1, hgo1⟩ := gc_relD hbat hs hgo hg ho
      have hv := violated_nil hs1.2.1.1.1 hl hgo1
      obtain ⟨S', h', hs', hgo'⟩ :=
        gcLoop_relD hl hbat k (gcRes S g o) (by have := gcM_lt hg ho hd; omega) hs1 hgo1
      refine ⟨S', ?_, hs', hgo'⟩
      rw [gcLoop, gcDue_eq hg ho, hd]
      simp only [eok_bind, Bool.not_true, Bool.false_eq_true, ite_false, gc_eq hg ho, hv, bne_self_eq_false]
      exact h'

/-- **`GC` over `AntSimD`** (without batching): the `GC` steps due end within `gcFuel`, with no
violation, `AntSimD` holding after them. -/
theorem antSim_gcD {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} (hbat : R.drv.batch = false) (hs : AntSimD R dec S V net xnet)
    (hl : RaftLaws G) (hgo : GlobalOk R S net G) :
    ∃ S', gcLoop (gcFuel S) S = .ok (S', none) ∧ AntSimD R dec S' V net xnet ∧ GlobalOk R S' net G :=
  gcLoop_relD hl hbat (gcFuel S) S (by unfold gcFuel gcM; omega) hs hgo

/-! ## `recv` -/

/-- **`recv`** (B 199-204) over `AntSimD`, for every mask below `mskB2` (no snapshot message), without
batching. -/
theorem antSim_recvD_in (msk : SimMask) (hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (m : Msg),
      InMask msk R net xnet → R.drv.batch = false →
      SimPreD R dec S V net xnet evs G → m ∈ net → m.dst = nodeId n → (V n).cause = some m →
      SimStepD R dec evs G (evRecv (nodeId n) m) (setV V n { V n with told := true }) net xnet := by
  intro R dec S V net xnet evs G n m hin hbat ⟨hp, hs, hl, hgo⟩ hm hdst hcause
  have hsn := (hin.b2 hmsk).1
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  obtain ⟨_, _, j, hj, hjk⟩ := hn.1 m hm
  have hjn : j = n := nodeId_inj (hj.symm.trans hdst)
  subst hjn
  have hsnap : m.ty ≠ .snap := (hn.2.2.2.2.1 m hm).2.1 hsn
  have hstep := recv_eq j m hc hsnap (fun ht hle => by
    have := (hjk (Int.le_trans (effTerm_le S1 j.val) hle)).1 ht
    rw [hj] at this; exact this)
  have hrel : AntSimD R dec (recvS S1 j.val (msgOf m (nodeId j))) (setV V j { V j with told := true }) net
      xnet := by
    obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11,
      by simpa [recvS] using sh12, sh13, sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩ :=
      hno k
    by_cases hk : k = j
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, fun _ => .inl ⟨m, hcause, ?_⟩,
        d16, d17, d18, d19, d20⟩
      change (S1.pending.set k.val [msgOf m (nodeId k)])[k.val]! = _
      exact get!_set_self _ (by rw [sh12]; exact k.isLt)
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ j.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, fun ht => ?_, d16, d17, d18,
        d19, d20⟩
      rw [show (recvS S1 j.val (msgOf m (nodeId j))).pending[k.val]! = S1.pending[k.val]! from
        get!_set_ne _ _ hne]
      exact d15 ht
  have hgo2 : GlobalOk R (recvS S1 j.val (msgOf m (nodeId j))) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1.1 hl hgo2), hrel, hgo2⟩

/-! ## `readreq`, `read` -/

/-- **`readreq`** over `AntSimD` (B 657-661), for the runs a mask below `mskB2` admits without batching; the view keeps the binding's
last `MaxReads` requests (`readsAsk`). -/
theorem antSim_readreqD_in (msk : SimMask) (_hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (ctx : List w8),
      InMask msk R net xnet → R.drv.batch = false →
      SimPreD R dec S V net xnet evs G → (V n).Idle →
      SimStepD R dec evs G (evReadReq (nodeId n) ctx)
        (setV V n { V n with reads := readsAsk (V n).reads (ctx, G.committed.length) }) net xnet := by
  intro R dec S V net xnet evs G n ctx _ hbat ⟨hp, hs, hl, hgo⟩ _
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hstep := readreq_eq n ctx hc
  have hch : (S1.chain.length : Int) ≤ (G.committed.length : Int) := by
    obtain ⟨c, hcl, he⟩ := hgo1.2.2.2.2.1
    rw [he]
    have : (logOf (G.committed.take c)).length = (G.committed.take c).length := List.length_map _
    rw [this, List.length_take]; omega
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hrel : AntSimD R dec (askS S1 n.val ctx)
      (setV V n { V n with reads := readsAsk (V n).reads (ctx, G.committed.length) }) net xnet := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13,
      by simpa [askS] using sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩ := hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩
      apply RRel.readsIs
      change RRel ((S1.reads.set k.val _)[k.val]!) _
      rw [get!_set_self _ (by rw [sh14]; exact k.isLt)]
      exact (d6.rrel.append rfl hch).trunc
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩
      unfold ReadsIs
      rw [show (askS S1 n.val ctx).reads[k.val]! = S1.reads[k.val]! from get!_set_ne _ _ hne]
      exact d6
  have hgo2 : GlobalOk R (askS S1 n.val ctx) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1.1 hl hgo2), hrel, hgo2⟩

/-- **`read`** over `AntSimD` (B 663-667), for the runs a mask below `mskB2` admits without batching. -/
theorem antSim_readD_in (msk : SimMask) (_hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (rs : ReadStateM)
      (rest : List ReadStateM),
      InMask msk R net xnet → R.drv.batch = false →
      SimPreD R dec S V net xnet evs G → (V n).rpend = rs :: rest → Told (V n) →
      (∀ f, (rs.RequestCtx', f) ∈ (V n).reads → f ≤ uint.nat rs.Index') →
      SimStepD R dec evs G (evRead (nodeId n) rs.RequestCtx' rs.Index')
        (setV V n { V n with rpend := rest,
                             reads := (V n).reads.filter (fun p => decide (p.1 ≠ rs.RequestCtx')) })
        net xnet := by
  intro R dec S V net xnet evs G n rs rest _ hbat ⟨hp, hs, hl, hgo⟩ _ _ hfl
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hrr := (hno n).2.2.2.2.2.1.rrel
  have hst : ∀ r ∈ S1.reads[n.val]!, r.ctx = rs.RequestCtx' → r.floor ≤ uint.Z rs.Index' := by
    have key : ∀ (a : List ReadRec) (b : List (Str × Nat)), RRel a b →
        (∀ y ∈ b, y.1 = rs.RequestCtx' → (y.2 : Int) ≤ uint.Z rs.Index') →
        ∀ r ∈ a, r.ctx = rs.RequestCtx' → r.floor ≤ uint.Z rs.Index' := by
      intro a b h
      induction h with
      | nil => intro _ r hr; simp at hr
      | @cons x y _ _ h1 h2 _ ih =>
        intro hy r hr hrc
        rcases List.mem_cons.mp hr with e | hr
        · subst e
          have := hy y List.mem_cons_self (h1 ▸ hrc)
          omega
        · exact ih (fun y' hy' => hy y' (List.mem_cons_of_mem _ hy')) r hr hrc
    refine key _ _ hrr (fun y hy hyc => ?_)
    have hy' : (rs.RequestCtx', y.2) ∈ (V n).reads := by rw [← hyc]; exact hy
    have := hfl y.2 hy'
    have e : ((uint.nat rs.Index' : Nat) : Int) = uint.Z rs.Index' := by word
    omega
  have hstep := read_eq n rs.RequestCtx' rs.Index' hc hst
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hrel : AntSimD R dec (givenS S1 n.val rs.RequestCtx')
      (setV V n { V n with rpend := rest,
                           reads := (V n).reads.filter (fun p => decide (p.1 ≠ rs.RequestCtx')) }) net xnet := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13,
      by simpa [givenS] using sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩ := hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩
      apply RRel.readsIs
      change RRel ((S1.reads.set k.val _)[k.val]!) _
      rw [get!_set_self _ (by rw [sh14]; exact k.isLt)]
      exact hrr.filter _
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩
      unfold ReadsIs
      rw [show (givenS S1 n.val rs.RequestCtx').reads[k.val]! = S1.reads[k.val]! from get!_set_ne _ _ hne]
      exact d6
  have hgo2 : GlobalOk R (givenS S1 n.val rs.RequestCtx') net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1.1 hl hgo2), hrel, hgo2⟩

/-! ## `kill`, the end of a batch -/

/-- **A kill** over `AntSimD`: nothing the relation reads moves (`alive` is the harness's). -/
theorem antSim_kill_in : antSim_kill_in.stmt := by
  intro _ _ R dec S V net xnet _ n _ _ hs _ _
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs
  refine ⟨hsh, hb, hn, hxn, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact hno j
  · simp only [hj, ↓reduceIte]; exact hno j

/-- A node part with nothing pending keeps under a change of its drain's `by`. -/
theorem nodeOkD_byE {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {n : Fin R.N} {v : NodeView}
    (b : Str) (hp : v.pend = []) (h : NodeOkD R dec S net n v) : NodeOkD R dec S net n { v with byE := b } := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, -, -, rest⟩ := h
  exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, fun _ q hq => by simp [hp] at hq,
    fun _ _ q hq => by simp [hp] at hq, rest⟩

/-- **The end of a sync batch** over `AntSimD`: between inputs, the next drain is the write's. -/
theorem antSim_batchEnd_in : antSim_batchEnd_in.stmt := by
  intro _ _ R dec S V net xnet n _ hs _ hI
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs
  refine ⟨hsh, hb, hn, hxn, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact nodeOkD_byE _ hI.2.1 (hno j)
  · simp only [hj, ↓reduceIte]; exact hno j

end carryd

end AntSim
end EtcdGrove
end Perennial
