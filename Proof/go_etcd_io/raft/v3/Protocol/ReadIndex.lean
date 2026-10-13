/-
Read-index (2026-10-12): the protocol argument behind a `ReadState`
(notes/decisions.md, "Read-index: a request registry per leader term, acks bounded by
the event history").

* A read context `c` is created by a client, which holds the registry's authority
  (`reReads`), with a committed log `Lc` it knows (`readReq γ c Lc`).
* A `ReadState{Index: i, RequestCtx: c}` carries `readOk γ c i`: `|Lc| ≤ i`.
* At a request's arrival the leader of `T` records `((c, i), d)` (`RqRec`): `d = none`
  with `readOk γ c i` already, or `d = some (t', q)`, the request *doomed*: a quorum `q`
  acknowledged at a term `t' > T` (`doomed`). `ownRaftGhost_read_arrive` decides which,
  from the global committed log's justification.
* A follower `v` answering a heartbeat at `T` is in no doomed record's quorum
  (`ownRaftGhost_not_doomed`: its event history has every acknowledgement at or below its
  term).
* A quorum of such followers confirms a record: it is not doomed (`rqRecOk_confirm`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF]

/-! ### Read contexts -/

/-- The read context `c` was created knowing the committed log `Lc`. -/
def readReq (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) : IProp GF :=
  iprop(c ↪[γ.reReads]□ Lc ∗ isCommitted γ Lc)

instance readReq_persistent (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) :
    Persistent (readReq (GF := GF) γ c Lc) := by
  unfold readReq; infer_instance
instance readReq_timeless (γ : RaftNames) (c : List w8) (Lc : List raftpb.Entry) :
    Timeless (readReq (GF := GF) γ c Lc) := by
  unfold readReq; infer_instance

theorem readReq_agree (γ : RaftNames) (c : List w8) (L1 L2 : List raftpb.Entry) :
    ⊢ readReq (GF := GF) γ c L1 -∗ readReq γ c L2 -∗ ⌜L1 = L2⌝ := by
  unfold readReq
  iintro ⟨#H1, -⟩ ⟨#H2, -⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- Creating a fresh read context, by the holder of the registry's authority. -/
theorem readReq_alloc (γ : RaftNames) (R : GMap (List w8) (List raftpb.Entry)) (c : List w8)
    (Lc : List raftpb.Entry) :
    R !! c = none →
    ⊢ ghostMapAuth (GF := GF) γ.reReads 1 R -∗ isCommitted γ Lc ==∗
      ghostMapAuth γ.reReads 1 (<[c := Lc]> R) ∗ readReq γ c Lc := by
  intro Hfree
  iintro Ha #Hc
  imod ghost_map_insert_persist c Lc Hfree $$ Ha with ⟨Ha, #Hel⟩
  imodintro
  iframe Ha
  unfold readReq
  iframe Hel Hc

/-- What a `ReadState{Index: i, RequestCtx: c}` promises: the log `c` was created with is no
longer than `i`. -/
def readOk (γ : RaftNames) (c : List w8) (i : w64) : IProp GF :=
  iprop(∃ Lc, readReq γ c Lc ∗ ⌜(Lc.length : Int) ≤ uint.Z i⌝)

instance readOk_persistent (γ : RaftNames) (c : List w8) (i : w64) :
    Persistent (readOk (GF := GF) γ c i) := by
  unfold readOk; infer_instance
instance readOk_timeless (γ : RaftNames) (c : List w8) (i : w64) :
    Timeless (readOk (GF := GF) γ c i) := by
  unfold readOk; infer_instance

/-- A client's reading of `readOk`: any committed log at least `i` long extends `Lc`. -/
theorem readOk_prefix (γ : RaftNames) (c : List w8) (i : w64) (Lc D : List raftpb.Entry) :
    uint.Z i ≤ (D.length : Int) →
    ⊢ readOk (GF := GF) γ c i -∗ readReq γ c Lc -∗ isCommitted γ D -∗ ⌜Lc <+: D⌝ := by
  intro Hle
  unfold readOk
  iintro ⟨%L, #Hr, %HL⟩ #Hr' #HD
  icases readReq_agree γ c L Lc $$ Hr Hr' with %Heq
  subst Heq
  unfold readReq
  icases Hr with ⟨-, #Hc⟩
  icases isCommitted_agree γ L D $$ Hc HD with %Hp
  ipureintro
  rcases Hp with Hp | Hp
  · exact Hp
  · have := Hp.length_le
    have : L.length = D.length := by omega
    exact (Hp.eq_of_length this.symm) ▸ List.prefix_refl _

/-! ### Request records -/

/-- A leader's record of a request: its context and read index, and whether it was doomed
at arrival (the term and quorum of the acknowledgements that doomed it). -/
abbrev RqRec := (List w8 × w64) × Option (w64 × GSet w64)

/-- A quorum `q` acknowledged at a term `t'` above `T` (each a real acknowledgement, at a
nonzero index). -/
def doomed (γ : RaftNames) (T t' : w64) (q : GSet w64) : IProp GF :=
  iprop(⌜uint.Z T < uint.Z t' ∧ IsQuorum γ.reCfg q⌝ ∗
    [∗map] v ↦ _u ∈ toMap q, ∃ i', ⌜0 < uint.Z i'⌝ ∗ isAcked γ v t' i')

instance doomed_persistent (γ : RaftNames) (T t' : w64) (q : GSet w64) :
    Persistent (doomed (GF := GF) γ T t' q) := by
  unfold doomed; infer_instance

def rqRecOk (γ : RaftNames) (T : w64) (r : RqRec) : IProp GF :=
  match r.2 with
  | none => readOk γ r.1.1 r.1.2
  | some p => doomed γ T p.1 p.2

instance rqRecOk_persistent (γ : RaftNames) (T : w64) (r : RqRec) :
    Persistent (rqRecOk (GF := GF) γ T r) := by
  unfold rqRecOk; split <;> infer_instance

/-- A record whose doom quorum (if any) misses every member of a quorum `Q` is not
doomed. -/
theorem rqRecOk_confirm (γ : RaftNames) (T : w64) (r : RqRec) (Q : GSet w64) :
    IsQuorum γ.reCfg Q →
    (∀ v ∈ Q, ∀ t' q, r.2 = some (t', q) → v ∉ q) →
    ⊢ rqRecOk (GF := GF) γ T r -∗ readOk γ r.1.1 r.1.2 := by
  intro HQ Hw
  rcases h : r.2 with _ | ⟨t', q⟩ <;> simp only [rqRecOk, h]
  · iintro H; iexact H
  · unfold doomed
    iintro ⟨%Hpq, -⟩
    obtain ⟨x, Hx1, Hx2, -⟩ := quorums_intersect_cfg _ _ _ HQ Hpq.2
    exact absurd Hx2 (Hw x Hx1 t' q h)

section inv
variable [InvGS GF]

/-! ### Followers: no acknowledgement above their term -/

theorem ownRaftGhost_ack_le (γ : RaftNames) (v : w64) (s : PState) (t i : w64) :
    ⊢ ownRaftGhost (GF := GF) γ v s -∗ ackEv γ v t i -∗ ⌜uint.Z t ≤ uint.Z s.term⌝ := by
  unfold ownRaftGhost ownLogGhost ownEvs ackEv
  iintro ⟨%γv, %voted, %kl, H⟩ ⟨%γe', %L, %HL, #Hlb⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  icases Hevs with ⟨%γe, %evs, %Hγe, Ha, %Hevs⟩
  obtain ⟨Hγe', Hin, -⟩ := HL
  rw [Hγe] at Hγe'; cases Hγe'
  icases mono_list_auth_lb_valid $$ Ha Hlb with %Hp
  ipureintro
  have := Hevs.2.1 _ (Hp.2.subset Hin)
  simpa [aevTerm] using this

/-- A node at term `T` is in no quorum that dooms a record of `T`. -/
theorem ownRaftGhost_not_doomed (γ : RaftNames) (v : w64) (s : PState) (r : RqRec) :
    ⊢ ownRaftGhost (GF := GF) γ v s -∗ rqRecOk γ s.term r -∗
      ⌜∀ t' q, r.2 = some (t', q) → v ∉ q⌝ := by
  iintro Hown #Hr
  rcases h : r.2 with _ | ⟨t', q⟩ <;> simp only [rqRecOk, h]
  · ipureintro; intro t' q h'; cases h'
  · unfold doomed
    icases Hr with ⟨%Hpq, #Hacks⟩
    have Hlt := Hpq.1
    by_cases hv : v ∈ q
    · ihave ⟨%i', %Hi', #Ha⟩ := BigSepM.bigSepM_lookup
        (Φ := fun v _ => iprop(∃ i', ⌜0 < uint.Z i'⌝ ∗ isAcked (GF := GF) γ v t' i'))
        ((GMap.elem_of_gset _ _).mp hv) $$ Hacks
      unfold isAcked
      icases Ha with (%H0 | ⟨-, #Hev⟩)
      · exfalso; omega
      · ihave %Hle := ownRaftGhost_ack_le γ v s t' i' $$ Hown Hev
        exfalso; omega
    · ipureintro
      intro t'' q' hh
      cases hh
      exact hv

/-! ### Arrival at the leader -/

/-- The persistent facts of a node's log state the arrival needs. -/
theorem ownLogGhost_commitIn (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64) :
    ⊢ ownLogGhost (GF := GF) γ id s kl -∗
      ∃ fp, ⌜FullOk s.base fp ∧ LogOk s⌝ ∗ logRecs γ base0 fp ∗ logRecs γ s.base s.log ∗
        commitIn γ (fp ++ s.log) s.commit s.term := by
  unfold ownLogGhost
  iintro ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  iexists fp
  isplitr; · ipureintro; exact ⟨Hfull.1, Hlog_ok⟩
  iframe Hfrecs Hrecs Hcommit

/-- The case split at the leader's arrival: the global committed log `P` is justified by a
commit at a term `t`; above `T` it dooms the request, at `T` it is the leader's own (at most
its commit index), below `T` it is behind the leader's own committed entry of `T`. -/
theorem read_arrive_core (γ : RaftNames) (id : w64) (s : PState) (c : List w8)
    (Lc P fp : List raftpb.Entry) :
    s.role = .leader →
    s.term ≠ W64 0 →
    plogTermAt s.base s.log s.commit = some s.term →
    Lc <+: P →
    FullOk s.base fp → LogOk s →
    ⊢ committedJust (GF := GF) γ P -∗ votesTbl γ -∗ lcmOwn γ id s -∗ isLeader γ id s.term -∗
      commitIn γ (fp ++ s.log) s.commit s.term -∗ readReq γ c Lc -∗
      votesTbl γ ∗ lcmOwn γ id s ∗ ∃ d, rqRecOk γ s.term ((c, s.commit), d) := by
  intro Hr Htnz Hct HLP Hfull Hlok
  iintro #Hj Htbl Hlcm #Hl #Hcmt #Hrq
  -- a short enough committed log: the request is read at once
  have Hok : ∀ (len : Int), (P.length : Int) ≤ len → len ≤ uint.Z s.commit →
      (Lc.length : Int) ≤ uint.Z s.commit := by
    intro len H1 H2
    have := HLP.length_le
    omega
  have Hnone : (Lc.length : Int) ≤ uint.Z s.commit →
      ⊢ readReq (GF := GF) γ c Lc -∗ ∃ d, rqRecOk γ s.term ((c, s.commit), d) := by
    intro Hle
    iintro #Hrq
    iexists none
    unfold rqRecOk readOk
    iexists Lc
    iframe Hrq
    ipureintro; exact Hle
  unfold committedJust
  icases Hj with (%HP0 | ⟨%t, %n, %G, %ldr, #Hcq, %HP0, #Hldr, #Hclb⟩)
  · subst HP0
    iframe Htbl Hlcm
    iapply Hnone (Hok 0 (by simp) (uint_Z_nonneg _)) $$ Hrq
  · have HPn : (P.length : Int) ≤ uint.Z n := by
      rw [HP0, List.length_take]; have := uint_Z_nonneg n; omega
    rcases Int.lt_trichotomy (uint.Z s.term) (uint.Z t) with HtT | HtT | HtT
    · -- doomed, unless the log is empty
      by_cases Hn0 : uint.Z n = 0
      · iframe Htbl Hlcm
        iapply Hnone (Hok (uint.Z n) HPn (by rw [Hn0]; exact uint_Z_nonneg _)) $$ Hrq
      · iframe Htbl Hlcm
        unfold cq
        icases Hcq with ⟨-, -, %q, %Hq, #Hacks⟩
        iexists (some (t, q))
        unfold rqRecOk doomed
        isplitr; · ipureintro; exact ⟨HtT, Hq⟩
        iapply BigSepM.bigSepM_impl $$ Hacks
        imodintro
        iintro %v %u %_ ⟨%i', %Hi', #Ha⟩
        iexists i'
        iframe Ha
        ipureintro; have := uint_Z_nonneg n; omega
    · -- the leader's own commit
      have Ht : t = s.term := uint_Z_inj.mp HtT.symm
      subst Ht
      icases isLeader_unique γ ldr id s.term $$ Hldr Hl with %Heq
      subst Heq
      icases lcmOwn_bound_keep γ ldr s n Hr $$ Hlcm Hclb with ⟨Hlcm, %Hb⟩
      iframe Htbl Hlcm
      iapply Hnone (Hok (uint.Z n) HPn Hb) $$ Hrq
    · -- an earlier term's commit is behind the leader's entry of its own term
      have Hbi : uint.Z s.base.index' ≤ uint.Z s.commit := Hlok.2.1
      have HFi : plogTermAt base0 (fp ++ s.log) s.commit = some s.term := by
        rw [full_term_at s.base fp s.log s.commit Hfull Hbi]; exact Hct
      icases cq_full γ t n G $$ Hcq with ⟨%HwG, #HrG⟩
      icases recs_mono γ G HwG $$ HrG with %Hmono
      ihave #Hcq' := Hcq
      ieval (unfold cq) at Hcq'
      icases Hcq' with ⟨%HGn, -⟩
      ihave #Hcmt' := Hcmt
      ieval (unfold commitIn) at Hcmt'
      icases Hcmt' with (%Hc0 | ⟨%t2, %n2, %G2, #Hcq2, %Hc2⟩)
      · -- commit index `0`: the entry there is the sentinel of term `0`
        exfalso
        have Hc : s.commit = W64 0 := uint_Z_inj.mp (by rw [Hc0]; rfl)
        rw [Hc, show (W64 0 : w64) = (base0 : entryID).index' from rfl, plogTermAt_base] at HFi
        exact Htnz (Option.some.inj HFi).symm
      · by_cases Hle : uint.Z n ≤ uint.Z s.commit
        · iframe Htbl Hlcm
          iapply Hnone (Hok (uint.Z n) HPn Hle) $$ Hrq
        · icases cq_agree γ t n t2 n2 s.commit G G2 (by omega) Hc2.1 $$ Htbl Hcq Hcq2 with %Hag
          have HGi : plogTermAt base0 G s.commit = some s.term :=
            (Hag s.commit (Int.le_refl _)).trans (Hc2.2.2.trans HFi)
          have := Hmono s.commit n s.term t (by omega) HGi HGn
          exfalso; omega

theorem leaderWit_leader (γ : RaftNames) (id : w64) (s : PState) (h : s.role = .leader) :
    leaderWit (GF := GF) γ id s = isLeader γ id s.term := by
  unfold leaderWit; rw [h]

/-- A request arriving at the leader of `T`, whose commit index is at an entry of `T`: it
is recorded, read at the commit index, doomed or not. -/
theorem ownRaftGhost_read_arrive (γ : RaftNames) (id : w64) (s : PState) (c : List w8)
    (Lc : List raftpb.Entry) :
    s.role = .leader →
    plogTermAt s.base s.log s.commit = some s.term →
    ⊢ ownRaftGhost (GF := GF) γ id s -∗ readReq γ c Lc ={⊤}=∗
      ownRaftGhost γ id s ∗ ∃ d, rqRecOk γ s.term ((c, s.commit), d) := by
  intro Hr Hct
  iintro Hown #Hrq
  icases persistent_entails_right
    (wand_entails (ownRaftGhost_term_nz (GF := GF) γ id s (by rw [Hr]; decide))) $$ Hown
    with ⟨%Htnz, Hown⟩
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave #Hl : isLeader γ id s.term $$ []
  · rw [← leaderWit_leader γ id s Hr]; iexact Hlead
  ihave ⟨%fp, %Hfl, #Hfr, #Hrecs, #Hcmt⟩ := ownLogGhost_commitIn γ id s kl $$ Hlg
  ihave #Hinv := ownLogGhost_inv $$ Hlg
  ihave #Hrq' := Hrq
  ieval (unfold readReq) at Hrq'
  icases Hrq' with ⟨-, #HLc⟩
  unfold raftCommitInv
  iinv Hinv with ⟨%P, %R, >HP, >#Hj, >Htbl, Hpo⟩ Hclose
  ihave %HLP := isCommitted_prefix γ Lc P $$ HLc HP
  icases read_arrive_core γ id s c Lc P fp Hr Htnz Hct HLP Hfl.1 Hfl.2
    $$ Hj Htbl Hlcm Hl Hcmt Hrq with ⟨Htbl, Hlcm, #Hres⟩
  imod Hclose $$ [HP Htbl Hpo] with -
  · inext
    iexists P, R
    iframe
    iexact Hj
  imodintro
  iframe Hres
  unfold ownRaftGhost
  iexists γv, voted, kl
  iframe % # ∗

end inv

end ghost

end EtcdGrove
end Perennial
