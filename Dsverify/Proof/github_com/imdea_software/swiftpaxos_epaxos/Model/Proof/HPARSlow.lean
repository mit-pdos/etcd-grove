/-
`handlePreAcceptReply`: The slow path: `RecAcceptProof.inv_accept_start` at the bookkeeping's ballot.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPARBase
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Decide

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PARProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof LbCountProof RecCommitProof RecAcceptProof

/-! ## Helpers of the slow path -/

theorem slow_own {S : Sys} (hS : Inv S) : Inv.ballotOwner S :=
  let ⟨_, _, _, _, _, h, _⟩ := hS.1; h
theorem slow_op {S : Sys} (hS : Inv S) : Inv.oneProposal S :=
  let ⟨_, _, _, _, _, _, h, _⟩ := hS.1; h
theorem slow_vf {S : Sys} (hS : Inv S) : Inv.votesFollowProposals S :=
  let ⟨_, _, _, _, _, _, _, h, _⟩ := hS.1; h
theorem slow_rr {S : Sys} (hS : Inv S) : Inv.repliesReportVotes S :=
  let ⟨_, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
theorem slow_lb {S : Sys} (hS : Inv S) : Inv.lbInv S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
theorem slow_safe {S : Sys} (hS : Inv S) : Inv.safe S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
theorem slow_reps {S : Sys} (hS : Inv S) : Inv.reports S :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hS.1; h

theorem slow_notCom {s : w8} (h : stGe s stCOMMITTED = false) : ¬ isCommitted s := by
  unfold isCommitted stGe at *; rintro (rfl | rfl) <;> revert h <;> decide

theorem slow_dlv_new (S : Sys) (fr i n : Nat) (m : Msg) (hm : (S.sent fr i)[n]? = some m) :
    (S.deliver fr i n m).deliveredMsg fr i m :=
  ⟨n, by
    have hd : S.deliver fr i n m =
        ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).applyStep i
          ((hMsg (S.rep i) m).1, (hMsg (S.rep i) m).2) := rfl
    rw [hd, Sys.applyStep_sent]; exact hm, deliver_delivered S fr i n m⟩

theorem slow_depsLe_trans {a b c : List w32} (h1 : depsLe a b) (h2 : depsLe b c) : depsLe a c :=
  ⟨h1.1, h2.2.1, fun q hq => Int.le_trans (h1.2.2 q hq) (h2.2.2 q hq)⟩

theorem slow_sent_msgs {S : Sys} {fr to : Nat} {m : Msg} (h : m ∈ S.sent fr to) :
    m ∈ S.msgs fr to := by
  simp only [Sys.msgs, List.mem_append]; exact Or.inl (Or.inl h)

theorem slow_dlv_msgs {S : Sys} {fr to : Nat} {m : Msg} (h : S.deliveredMsg fr to m) :
    m ∈ S.msgs fr to := by
  obtain ⟨n, h1, -⟩ := h; exact slow_sent_msgs (List.mem_of_getElem? h1)

theorem slow_sle (a o : w64) (ha : a.toNat ≤ 10) (ho : o.toNat ≤ 10) :
    a.sle o = true ↔ a.toNat ≤ o.toNat := by
  rw [BitVec.sle, BitVec.toInt_eq_toNat_of_lt, BitVec.toInt_eq_toNat_of_lt]
  · simp
  all_goals omega

/-- Avoiding a list and a replica: at least `N - 1 - |R|` replicas remain. -/
theorem slow_avoid (R : List Nat) (q : Nat) :
    ∃ Z : List Nat, Z.Nodup ∧ nR ≤ Z.length + R.length + 1 ∧
      ∀ z ∈ Z, z < nR ∧ z ≠ q ∧ z ∉ R := by
  refine ⟨(List.range nR).filter (fun z => decide (z ≠ q ∧ z ∉ R)), List.nodup_range.filter _,
    ?_, fun z hz => ?_⟩
  · have h1 := List.length_eq_countP_add_countP (l := List.range nR)
      (fun z => decide (z ≠ q ∧ z ∉ R))
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at h1
    have hY : ((List.range nR).filter (fun z => decide ¬ (decide (z ≠ q ∧ z ∉ R)) = true)).length ≤
        (q :: R).length := by
      apply List.Subperm.length_le
      apply List.subperm_of_subset (List.nodup_range.filter _)
      intro z hz
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hz
      simp only [List.mem_cons]
      by_cases h : z = q
      · exact Or.inl h
      · exact Or.inr (Classical.byContradiction fun h' => hz.2 ⟨h, h'⟩)
    simp only [List.length_cons, List.length_range] at hY h1
    omega
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hz
    exact ⟨hz.1, hz.2.1, hz.2.2⟩

/-- `noPA` of a replica other than the stepping one survives a step that sends no PreAccept. -/
theorem slow_noPA_lift {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event} {pend : Option Bcast}
    (hH : HS S S' i σ' E (fun _ => []) pend)
    (hpend : ∀ to m', m' ∈ intendedOf pend to → ∀ pa, m' ≠ .preAccept pa)
    {x : InstId} {a : Nat} {u : Val} (ha : a ≠ i) (h : S.noPA x a u) : S'.noPA x a u := by
  have hev : ∀ e, S'.ev a e → S.ev a e := fun e he => hH.ev_back he (fun h => absurd h ha)
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun st hst hv => h1 st hst (hev _ hv), ?_⟩
  rcases h2 with ⟨wa, hwa, hc⟩ | ⟨st, u', hst, hne, hv⟩ | ⟨⟨v0, hp⟩, hno⟩
  · exact Or.inl ⟨wa, by rw [hH.rep_other ha]; exact hwa, hc⟩
  · exact Or.inr (Or.inl ⟨st, u', hst, hne, hH.ev_old hv⟩)
  · refine Or.inr (Or.inr ⟨⟨v0, hH.ev_old hp⟩, fun m hm hx hb => ?_⟩)
    rcases hH.mem_msgs.mp hm with h | ⟨-, h | h⟩
    · exact hno m h hx hb
    · cases h
    · exact hpend _ _ h m rfl

/-- A replica that answered the leader's PreAccept at the initial ballot (the leader still
pre-accepting there): it never pre-accepts at the initial ballot any value but the one with its
reply's attributes. -/
theorem slow_noPA_reply (S : Sys) (hS : Inv S) {x : InstId} (hxq : x.q < nR) {a : Nat}
    (ha : a < nR) (w : InstRec) (lb : LbRec) (hw : (S.rep x.q).inst x = some w)
    (hlb : w.lb = some lb) (hpa : isPA lb.status) (hlt : lb.lastTriedBallot = initBal x)
    (m : PreAcceptReply) (hm : Msg.preAcceptReply m ∈ S.msgs a x.q) (hx : parX m = x)
    (hb : m.ballot = initBal x) :
    ∃ v : Val, v.seq = m.seq ∧ v.deps = m.deps ∧ ∀ u, u ≠ v → S.noPA x a u := by
  subst hx
  have hP := hS.2.pm
  obtain ⟨hst, hv0, hvb, -⟩ := hP.parSt a _ m hm
  have hrr := (slow_rr hS).2.1 a _ m hm
  by_cases hpa' : isPA m.status
  · obtain ⟨-, v, hv, hs, hd⟩ := hrr.2.1 hpa'
    rw [hb] at hv
    refine ⟨v, hs, hd, fun u hu => ⟨fun st hst hv' =>
      hu ((slow_reps hS).2.2.2.2.2.1 a _ _ _ _ _ _ hst hpa' hv' hv),
      Or.inr (Or.inl ⟨_, v, hpa', fun h => hu h.symm, hv⟩)⟩⟩
  · refine ⟨⟨[], m.seq, m.deps⟩, rfl, rfl, fun u _ => ⟨fun st hst hv' =>
      hP.parNoPA a _ m hm hpa' st u hst (by rw [hb]; exact hv'), ?_⟩⟩
    rcases hst with h | h | h
    · exact absurd h hpa'
    · exfalso
      obtain ⟨v, hv, -⟩ := hrr.2.2.1 h
      obtain ⟨ℓ, hl⟩ := (slow_vf hS).2 _ _ _ _ hv
      have hmk := (slow_own hS).2.2.1 _ _ _ _ hl
      have hz := zz_initBal (parX m) hxq
      rw [hb] at hvb
      rcases ((slow_own hS).1 _ _ _ hmk).1 with ⟨h1, h2⟩ | ⟨h1, -⟩
      · have : m.vballot = initBal (parX m) := zz_inj (by rw [hz]; exact h1)
        rw [this, h2, ← hlt] at hl
        exact hS.2.paNoAcc _ hxq _ w lb hw hlb hpa v hl
      · simp only [nR] at hxq h1 hz; omega
    · obtain ⟨c, u', hc, -⟩ := hP.parCom a _ m hm h
      obtain ⟨wa, hwa, hcw⟩ := hS.2.commitRec a _ c u' ha hc
      exact Or.inl ⟨wa, hwa, Or.inr (by rcases hcw with h | h <;> rw [h] <;> decide)⟩

theorem slow_paRcpt_mem (S : Sys) (x : InstId) {z : Nat} (hz : z < nR) (m : PreAccept)
    (hm : Msg.preAccept m ∈ S.sent x.q z ++ S.outbox x.q z)
    (hx : (⟨toN m.replica, toN m.inst⟩ : InstId) = x) (hb : m.ballot = initBal x) :
    z ∈ S.paRcpt x := by
  simp only [Sys.paRcpt, List.mem_filter, List.mem_range, List.any_eq_true]
  exact ⟨hz, _, hm, by simp [Msg.isPAat, hx, hb]⟩

/-- The thrifty count at the initial ballot: no value can be fast-chosen any more (two
non-leaders never pre-accept it) when the leader sent at most two PreAccepts or received two
different replies. -/
theorem slow_fb (S : Sys) (hS : Inv S) (x : InstId) (hxq : x.q < nR)
    (hidle : S.pending x.q = none)
    (w : InstRec) (lb : LbRec) (hw : (S.rep x.q).inst x = some w) (hlb : w.lb = some lb)
    (hpa : isPA lb.status) (hlt : lb.lastTriedBallot = initBal x) (v0 : Val)
    (hph : S.ev x.q (.phase1 x (initBal x) v0))
    (hcase : lb.preAcceptsSent.toNat ≤ 2 ∨ ∃ (a a' : Nat) (m1 m2 : PreAcceptReply),
      Msg.preAcceptReply m1 ∈ S.sent a x.q ∧ Msg.preAcceptReply m2 ∈ S.sent a' x.q ∧
      parX m1 = x ∧ parX m2 = x ∧ m1.ballot = initBal x ∧ m2.ballot = initBal x ∧
      (m1.seq ≠ m2.seq ∨ m1.deps ≠ m2.deps)) (u : Val) :
    ∃ B : List Nat, B.Nodup ∧ 2 ≤ B.length ∧ ∀ a ∈ B, a < nR ∧ a ≠ x.q ∧ S.noPA x a u := by
  have hP := hS.2.pm
  obtain ⟨hs3, -, hR⟩ := hP.paSent x w lb hxq hw hlb hlt
  have hnot : ∀ z, z < nR → z ≠ x.q → z ∉ S.paRcpt x → ∀ u, S.noPA x z u := by
    intro z hz hzq hzR u
    refine ⟨fun st hst hv => ?_, Or.inr (Or.inr ⟨⟨v0, hph⟩, fun m hm hx hb => ?_⟩)⟩
    · obtain ⟨pa, hpa, hx, hb⟩ := hP.paVoteMsg z x st u hst hzq hv
      exact hzR (slow_paRcpt_mem S x hz pa (List.mem_append_left _ hpa) hx hb)
    · simp only [Msg.instOf, Option.some.injEq] at hx
      have hm' : Msg.preAccept m ∈ S.sent x.q z ++ S.outbox x.q z := by
        simp only [Sys.msgs, Sys.intended, hidle, List.append_nil] at hm; exact hm
      exact hzR (slow_paRcpt_mem S x hz m hm' hx hb)
  obtain ⟨Z, hZn, hZl, hZ⟩ := slow_avoid (S.paRcpt x) x.q
  rcases hcase with h2 | ⟨a, a', m1, m2, hm1, hm2, hx1, hx2, hb1, hb2, hne⟩
  · match Z, hZn, hZl, hZ with
    | z1 :: z2 :: _, hZn, _, hZ =>
      have e1 := hZ z1 (by simp)
      have e2 := hZ z2 (by simp)
      refine ⟨[z1, z2], ?_, by simp, fun a ha => ?_⟩
      · simp only [List.nodup_cons, List.mem_cons, not_or] at hZn
        simp [hZn.1.1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact ⟨e1.1, e1.2.1, hnot _ e1.1 e1.2.1 e1.2.2 u⟩
        · exact ⟨e2.1, e2.2.1, hnot _ e2.1 e2.2.1 e2.2.2 u⟩
    | [], _, hZl, _ => simp [nR] at hZl; omega
    | [_], _, hZl, _ => simp [nR] at hZl; omega
  · have hwf := (hS.1.1).2.2.2.2.2.1
    have rcp : ∀ a (m : PreAcceptReply), Msg.preAcceptReply m ∈ S.sent a x.q → parX m = x →
        m.ballot = initBal x → a < nR ∧ a ≠ x.q ∧ a ∈ S.paRcpt x ∧
        ∃ v : Val, v.seq = m.seq ∧ v.deps = m.deps ∧ ∀ u, u ≠ v → S.noPA x a u := by
      intro a m hm hx hb
      have hm' := slow_sent_msgs hm
      have hw' := hwf a x.q (List.ne_nil_of_mem hm')
      obtain ⟨-, -, -, pa, hpa', hpx, hpb⟩ := hP.parSt a x.q m hm'
      refine ⟨hw'.1, hw'.2.2, slow_paRcpt_mem S x hw'.1 pa (List.mem_append_left _ hpa')
        (by rw [hpx]; exact hx) (by rw [hpb]; exact hb),
        slow_noPA_reply S hS hxq hw'.1 w lb hw hlb hpa hlt m hm' hx hb⟩
    obtain ⟨r1, r1q, r1R, v1, hs1, hd1, hn1⟩ := rcp a m1 hm1 hx1 hb1
    obtain ⟨r2, r2q, r2R, v2, hs2, hd2, hn2⟩ := rcp a' m2 hm2 hx2 hb2
    have hv12 : v1 ≠ v2 := by
      intro h; rw [h] at hs1 hd1
      rcases hne with h' | h'
      · exact h' (hs1.symm.trans hs2)
      · exact h' (hd1.symm.trans hd2)
    match Z, hZn, hZl, hZ with
    | z :: _, _, _, hZ =>
      have e := hZ z (by simp)
      have hz := hnot z e.1 e.2.1 e.2.2 u
      by_cases hu : u = v1
      · refine ⟨[z, a'], by simp; rintro rfl; exact e.2.2 r2R, by simp, fun b hb => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact ⟨e.1, e.2.1, hz⟩
        · exact ⟨r2, r2q, hn2 u (by rw [hu]; exact hv12)⟩
      · refine ⟨[z, a], by simp; rintro rfl; exact e.2.2 r1R, by simp, fun b hb => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact ⟨e.1, e.2.1, hz⟩
        · exact ⟨r1, r1q, hn1 u hu⟩
    | [], _, hZl, _ =>
      simp only [fR] at hs3; simp [nR] at hZl; omega

/-- The slow path's value is witnessed (or the instance is decided): two counted pre-accept
replies and the leader computed attributes below the merge; a counted ACCEPTED reply's value is
witnessed. -/
theorem slow_wit (S : Sys) (hS : Inv S) (i : Nat) (hi : i < nR) (x : InstId) (b : w32) (v0 : Val)
    (hph : S.ev i (.phase1 x b v0)) (seq' : w32) (deps' : List w32)
    (Q : List (Nat × PreAcceptReply)) (hQn : (Q.map (·.1)).Nodup) (hQl : 2 ≤ Q.length)
    (hQ : ∀ a m, (a, m) ∈ Q → a ≠ i ∧ Msg.preAcceptReply m ∈ S.msgs a i ∧ parX m = x ∧
      m.ballot = b ∧ depsLe m.deps deps')
    (hne : v0.cmds ≠ noop) :
    S.witnessed x ⟨v0.cmds, seq', deps'⟩ ∨ ∃ u, S.committedVal x u := by
  have hP := hS.2.pm
  have hwf := (hS.1.1).2.2.2.2.2.1
  have hst : ∀ a m, (a, m) ∈ Q → a < nR ∧
      (isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status) := by
    intro a m hq
    obtain ⟨-, hm, -⟩ := hQ a m hq
    exact ⟨(hwf a i (List.ne_nil_of_mem hm)).1, (hP.parSt a i m hm).1⟩
  have hcom : ∀ a m, (a, m) ∈ Q → isCommitted m.status → ∃ u, S.committedVal x u := by
    intro a m hq h
    obtain ⟨-, hm, hx, -⟩ := hQ a m hq
    obtain ⟨c, u, hc, -⟩ := hP.parCom a i m hm h
    exact ⟨u, Or.inl ⟨a, c, by rw [← hx]; exact hc⟩⟩
  have hacc : ∀ a m, (a, m) ∈ Q → m.status = stACCEPTED →
      S.witnessed x ⟨v0.cmds, seq', deps'⟩ ∨ ∃ u, S.committedVal x u := by
    intro a m hq h
    obtain ⟨-, hm, hx, hmb, hdl⟩ := hQ a m hq
    obtain ⟨u', hv, -, hd⟩ := ((slow_rr hS).2.1 a i m hm).2.2.1 h
    obtain ⟨ℓ, hl⟩ := (slow_vf hS).2 _ _ _ _ hv
    rw [show (⟨toN m.replica, toN m.inst⟩ : InstId) = x from hx] at hl
    by_cases hun : u'.cmds = noop
    · -- SLOW-WIT: the reply's Accept is below `b` (at `b` it would carry the Phase 1's batch) and
      -- forces every Phase 1 above it to a no-op (`accSup` + `cmdSafe`), unless committed
      have hle := (hP.parSt a i m hm).2.2.1
      rw [hmb] at hle
      have hlt : zz m.vballot < zz b := by
        rcases Int.lt_or_eq_of_le hle with h' | h'
        · exact h'
        · rw [zz_inj h'] at hl
          exact absurd (((slow_op hS).2.2 i ℓ x b v0 u' hph hl).symm.trans hun) hne
      rcases CmdSafeProof.accept_forces hP hl hph hlt with h' | ⟨r', b', w', hc⟩
      · exact absurd (h'.trans hun) hne
      · exact Or.inr ⟨w', Or.inl ⟨r', b', hc⟩⟩
    · rcases hP.accWit ℓ x _ u' hl hun with ⟨W, hWn, hWl, hW⟩ | hc
      · have heq : u'.cmds = v0.cmds := by
          rcases hS.2.valOk ℓ x _ u' (Or.inr hl) with h1 | ⟨ps, hps, h1⟩
          · exact absurd h1 hun
          rcases hS.2.valOk i x b v0 (Or.inl hph) with h2 | ⟨ps', hps', h2⟩
          · exact absurd h2 hne
          rw [hps] at hps'; cases hps'; rw [h1, h2]
        refine Or.inl ⟨W, hWn, hWl, fun r hr => ?_⟩
        obtain ⟨hr1, d, hd1, hd2⟩ := hW r hr
        exact ⟨hr1, d, by rw [← heq]; exact hd1, slow_depsLe_trans hd2 (by rw [hd]; exact hdl)⟩
      · exact Or.inr hc
  have hpa : ∀ a m, (a, m) ∈ Q → isPA m.status → ∃ st v, isPA st ∧ S.ev a (.vote x b st v) ∧
      v.cmds = v0.cmds ∧ v.deps = m.deps := by
    intro a m hq h
    obtain ⟨-, hm, hx, hb, -⟩ := hQ a m hq
    obtain ⟨-, v, hv, -, hd⟩ := ((slow_rr hS).2.1 a i m hm).2.1 h
    rw [show (⟨toN m.replica, toN m.inst⟩ : InstId) = x from hx, hb] at hv
    obtain ⟨ℓ, v₀, hp, hc⟩ := (slow_vf hS).1 _ _ _ _ _ hv h
    obtain ⟨-, rfl, -⟩ := (slow_op hS).1 _ _ _ _ _ _ hp hph
    exact ⟨_, v, h, hv, hc, hd⟩
  match Q, hQn, hQl, hQ, hst, hcom, hacc, hpa with
  | [], _, hQl, _, _, _, _, _ => simp at hQl
  | [_], _, hQl, _, _, _, _, _ => simp at hQl
  | (a1, m1) :: (a2, m2) :: t, hQn, _, hQ, hst, hcom, hacc, hpa =>
    have q1 : (a1, m1) ∈ (a1, m1) :: (a2, m2) :: t := by simp
    have q2 : (a2, m2) ∈ (a1, m1) :: (a2, m2) :: t := by simp
    rcases (hst _ _ q1).2 with p1 | p1 | p1
    · rcases (hst _ _ q2).2 with p2 | p2 | p2
      · obtain ⟨st1, v1, hs1, hv1, hc1, hd1⟩ := hpa _ _ q1 p1
        obtain ⟨st2, v2, hs2, hv2, hc2, hd2⟩ := hpa _ _ q2 p2
        obtain ⟨i1, -, -, -, l1⟩ := hQ _ _ q1
        obtain ⟨i2, -, -, -, l2⟩ := hQ _ _ q2
        have h12 : a1 ≠ a2 := by
          simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hQn
          exact hQn.1.1
        refine Or.inl ⟨[i, a1, a2], ?_, by simp [fR], fun r hr => ?_⟩
        · have : i ≠ a1 := fun h => i1 h.symm
          have : i ≠ a2 := fun h => i2 h.symm
          simp [*]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · refine ⟨hi, v0.deps, hP.phAttrs _ _ _ _ hph, ?_⟩
            exact slow_depsLe_trans (hP.paGe _ _ _ _ _ _ _ hs1 hv1 hph) (by rw [hd1]; exact l1)
          · have := hS.2.paAttrs _ _ _ _ _ hs1 hv1
            rw [hc1, hd1] at this
            exact ⟨(hst _ _ q1).1, m1.deps, this, l1⟩
          · have := hS.2.paAttrs _ _ _ _ _ hs2 hv2
            rw [hc2, hd2] at this
            exact ⟨(hst _ _ q2).1, m2.deps, this, l2⟩
      · exact hacc _ _ q2 p2
      · exact Or.inr (hcom _ _ q2 p2)
    · exact hacc _ _ q1 p1
    · exact Or.inr (hcom _ _ q1 p1)

/-- (SLOW-WIT) The slow path's Accept is supported (`InvPM.accSup`): two counted pre-accept
votes and the leader's own vote at the ballot are a command-level majority; a counted ACCEPTED
reply's Accept is supported at a ballot whose chosen commands are the Phase 1's (`cmdSafe`); a
counted COMMITTED reply follows a commit. -/
theorem slow_sup (S : Sys) (hS : Inv S) (i : Nat) (hi : i < nR) (x : InstId) (b : w32) (v0 : Val)
    (hph : S.ev i (.phase1 x b v0))
    (Q : List (Nat × PreAcceptReply)) (hQn : (Q.map (·.1)).Nodup) (hQl : 2 ≤ Q.length)
    (hQ : ∀ a m, (a, m) ∈ Q → a ≠ i ∧ Msg.preAcceptReply m ∈ S.msgs a i ∧ parX m = x ∧
      m.ballot = b) :
    (∃ r' b' u, S.ev r' (.commit x b' u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz b ∧ S.cmdChosen x c0 v0.cmds := by
  have hP := hS.2.pm
  have hwf := (hS.1.1).2.2.2.2.2.1
  have hown := slow_own hS
  have hxq : x.q < nR := (hS.2.crtEv i _ x hph rfl).1
  have hreal : realBal x b := by
    obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 i x b v0 hph
    exact DecideProof.real_of_make hown hxq (List.mem_of_getElem? hp1)
  have hst : ∀ a m, (a, m) ∈ Q → a < nR ∧
      (isPA m.status ∨ m.status = stACCEPTED ∨ isCommitted m.status) := by
    intro a m hq
    obtain ⟨-, hm, -⟩ := hQ a m hq
    exact ⟨(hwf a i (List.ne_nil_of_mem hm)).1, (hP.parSt a i m hm).1⟩
  have hcom : ∀ a m, (a, m) ∈ Q → isCommitted m.status → ∃ r' b' u, S.ev r' (.commit x b' u) := by
    intro a m hq h
    obtain ⟨-, hm, hx, -⟩ := hQ a m hq
    obtain ⟨c, u, hc, -⟩ := hP.parCom a i m hm h
    exact ⟨a, c, u, by rw [← hx]; exact hc⟩
  have hacc : ∀ a m, (a, m) ∈ Q → m.status = stACCEPTED →
      (∃ r' b' u, S.ev r' (.commit x b' u)) ∨
        ∃ c0, realBal x c0 ∧ zz c0 ≤ zz b ∧ S.cmdChosen x c0 v0.cmds := by
    intro a m hq h
    obtain ⟨-, hm, hx, hmb⟩ := hQ a m hq
    obtain ⟨u', hv, -, -⟩ := ((slow_rr hS).2.1 a i m hm).2.2.1 h
    obtain ⟨ℓ, hl⟩ := (slow_vf hS).2 _ _ _ _ hv
    rw [show (⟨toN m.replica, toN m.inst⟩ : InstId) = x from hx] at hl
    have hle := (hP.parSt a i m hm).2.2.1
    rw [hmb] at hle
    rcases hP.accSup ℓ x _ u' hl with hc | ⟨c0, hc0, hc0le, hch⟩
    · exact Or.inl hc
    · have heq : u'.cmds = v0.cmds := by
        rcases Int.lt_or_eq_of_le (Int.le_trans hc0le hle) with h' | h'
        · exact (CmdSafeProof.chosen_forces hP hc0 hch hph h').symm
        · have : zz m.vballot = zz b := by omega
          rw [zz_inj this] at hl
          exact (slow_op hS).2.2 i ℓ x b v0 u' hph hl
      exact Or.inr ⟨c0, hc0, Int.le_trans hc0le hle, heq ▸ hch⟩
  have hpa : ∀ a m, (a, m) ∈ Q → isPA m.status → ∃ st v, isPA st ∧ S.ev a (.vote x b st v) ∧
      v.cmds = v0.cmds := by
    intro a m hq h
    obtain ⟨-, hm, hx, hb⟩ := hQ a m hq
    obtain ⟨-, v, hv, -, -⟩ := ((slow_rr hS).2.1 a i m hm).2.1 h
    rw [show (⟨toN m.replica, toN m.inst⟩ : InstId) = x from hx, hb] at hv
    obtain ⟨ℓ, v₀, hp, hc⟩ := (slow_vf hS).1 _ _ _ _ _ hv h
    obtain ⟨-, rfl, -⟩ := (slow_op hS).1 _ _ _ _ _ _ hp hph
    exact ⟨_, v, h, hv, hc⟩
  match Q, hQn, hQl, hQ, hst, hcom, hacc, hpa with
  | [], _, hQl, _, _, _, _, _ => simp at hQl
  | [_], _, hQl, _, _, _, _, _ => simp at hQl
  | (a1, m1) :: (a2, m2) :: t, hQn, _, hQ, hst, hcom, hacc, hpa =>
    have q1 : (a1, m1) ∈ (a1, m1) :: (a2, m2) :: t := by simp
    have q2 : (a2, m2) ∈ (a1, m1) :: (a2, m2) :: t := by simp
    rcases (hst _ _ q1).2 with p1 | p1 | p1
    · rcases (hst _ _ q2).2 with p2 | p2 | p2
      · obtain ⟨st1, v1, hs1, hv1, hc1⟩ := hpa _ _ q1 p1
        obtain ⟨st2, v2, hs2, hv2, hc2⟩ := hpa _ _ q2 p2
        obtain ⟨st0, u0, hs0, hv0, hc0⟩ := (hP.cmdSafe i x b v0 hph).1
        obtain ⟨i1, -⟩ := hQ _ _ q1
        obtain ⟨i2, -⟩ := hQ _ _ q2
        have h12 : a1 ≠ a2 := by
          simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hQn
          exact hQn.1.1
        refine Or.inr ⟨b, hreal, Int.le_refl _, [i, a1, a2], ?_, by simp [nR], fun r hr => ?_⟩
        · have : i ≠ a1 := fun h => i1 h.symm
          have : i ≠ a2 := fun h => i2 h.symm
          simp [*]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨hi, st0, u0, Or.inl hs0, hv0, hc0⟩
          · exact ⟨(hst _ _ q1).1, st1, v1, Or.inl hs1, hv1, hc1⟩
          · exact ⟨(hst _ _ q2).1, st2, v2, Or.inl hs2, hv2, hc2⟩
      · exact hacc _ _ q2 p2
      · exact Or.inl (hcom _ _ q2 p2)
    · exact hacc _ _ q1 p1
    · exact Or.inl (hcom _ _ q1 p1)

/-- The slow path: `RecAcceptProof.inv_accept_start` at the bookkeeping's ballot. -/
theorem par_slow (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (parX p) = some w) (hlb : w.lb = some lb)
    (hnc : stGe w.status stCOMMITTED = false) (hlt : lb.lastTriedBallot.slt w.bal = false)
    (hb : p.ballot = lb.lastTriedBallot) (hpa : isPA lb.status)
    (hfast : parFast lb p = false) (hslow : parSlow lb p = true)
    (h : hPreAcceptReply (S.rep i) p = parSlowOut (S.rep i) w lb p) :
    Inv (S.deliver fr i n (.preAcceptReply p)) := by
  have hpm := mem_msgs_of_sent S hm
  have hA := hS.2
  obtain ⟨hfi, ⟨v0, hph0, hcmd0⟩, hprep, hwbal, hle4, c_lt, c_cmds, c_cp, c_tpa, c_prep, -, -,
    c_pas, c_aok, c_oks, -, c_stEq, c_bal, c_ballt, c_deps, ⟨Q, hQn, hQl, hQ⟩, c_aeF⟩ :=
    par_common S fr i n hS hi hfr hidle hn p hm w lb hw hlb hnc hlt hb hpa
  have hoks5 : (parLb lb p).preAcceptOKs.toNat ≤ 5 := by omega
  have hoks : 2 ≤ (parLb lb p).preAcceptOKs.toNat := by
    have h1 : (W64 (nR / 2)).sle (parLb lb p).preAcceptOKs = true := by
      unfold parSlow at hslow; simp only [Bool.and_eq_true] at hslow; exact hslow.1
    have h2 : (W64 (nR / 2)).toNat = 2 := by decide
    rw [slow_sle _ _ (by omega) (by omega), h2] at h1
    exact h1
  have hst5 : (parLb lb p).status = lb.status := c_stEq (by omega)
  have hpa5 : isPA (parLb lb p).status := by rw [hst5]; exact hpa
  have hbal5 : (parLb lb p).ballot = lb.lastTriedBallot := c_bal hpa5
  obtain ⟨hvb, -⟩ := hA.paLeader i hi _ w lb hw hlb hpa ⟨v0, hph0⟩ hnc hwbal
  -- the step
  have hout : hMsg (S.rep i) (.preAcceptReply p) =
      ((bumpRecvBallot (S.rep i) p.ballot).setInst (parX p)
          (accKnown w { parLb lb p with status := stACCEPTED } lb.lastTriedBallot
            ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩),
        [Out.ev (.vote (parX p) lb.lastTriedBallot stACCEPTED
            ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩),
         Out.ev (.accept (parX p) lb.lastTriedBallot ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩),
         Out.bcast (bcastAcceptOf ((bumpRecvBallot (S.rep i) p.ballot).setInst (parX p)
            (accKnown w { parLb lb p with status := stACCEPTED } lb.lastTriedBallot
              ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩)) (parX p)
            (acceptOf ((bumpRecvBallot (S.rep i) p.ballot).setInst (parX p)
              (accKnown w { parLb lb p with status := stACCEPTED } lb.lastTriedBallot
                ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩)) p.replica p.inst
              { parLb lb p with status := stACCEPTED }))]) := by
    show hPreAcceptReply (S.rep i) p = _
    rw [h]
    simp only [parSlowOut, accKnown, lbVal, c_cmds, hcmd0, hbal5, c_lt, hvb, Option.getD_some]
  have hH := hs_deliver S fr i n (.preAcceptReply p) hidle hm
  rw [hout] at hH
  generalize hσ1 : (bumpRecvBallot (S.rep i) p.ballot).setInst (parX p)
    (accKnown w { parLb lb p with status := stACCEPTED } lb.lastTriedBallot
      ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩) = σ1 at hH
  have hH' : HS S (S.deliver fr i n (.preAcceptReply p)) i σ1
      [.vote (parX p) lb.lastTriedBallot stACCEPTED ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩,
       .accept (parX p) lb.lastTriedBallot ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩]
      (fun _ => [])
      (bcastAcceptOf σ1 (parX p)
        (acceptOf σ1 p.replica p.inst { parLb lb p with status := stACCEPTED })).norm := by
    have e1 : ∀ (a b : Event) (c : Bcast), evsOf [Out.ev a, Out.ev b, Out.bcast c] = [a, b] :=
      fun _ _ _ => rfl
    have e2 : ∀ (a b : Event) (c : Bcast), sendsOf [Out.ev a, Out.ev b, Out.bcast c] =
      fun _ => [] := fun _ _ _ => by funext to; rfl
    have e3 : ∀ (a b : Event) (c : Bcast), pendFold [Out.ev a, Out.ev b, Out.bcast c] none =
      c.norm := fun _ _ _ => rfl
    rw [e1, e2, e3] at hH; exact hH
  have hid : σ1.id = i := by rw [← hσ1]; simp [RState.setInst]; exact (hS.1.1).1 i hi
  have hxq : (parX p).q < nR := ((hS.1.1).2.1 i hi _ w hw).2.1
  have hlbI := slow_lb hS i hi _ w lb hw hlb
  have hown := slow_own hS
  obtain ⟨r1, r2, r3, r4⟩ := ((hS.1.2.1) fr i _ hpm).1 p.replica p.inst rfl
  have hpend : ∀ to m', m' ∈ intendedOf (bcastAcceptOf σ1 (parX p)
      (acceptOf σ1 p.replica p.inst { parLb lb p with status := stACCEPTED })).norm to →
      ∀ pa, m' ≠ .preAccept pa := by
    intro to m' hm' pa
    rw [(mem_intended_norm hm').1]; simp [bcastAcceptOf]
  -- the leader of the initial ballot
  have hinit : lb.lastTriedBallot = initBal (parX p) →
      ∀ u, (S.deliver fr i n (.preAcceptReply p)).fastBlocked (parX p) u := by
    intro hbI u
    have hiq : i = (parX p).q := by
      have hz := zz_initBal (parX p) hxq
      rcases (hown.1 _ _ _ hlbI.1).1 with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hbI, hz] at h1; simp only [nR] at h1 hxq; omega
    have hcase : lb.preAcceptsSent.toNat ≤ 2 ∨ ∃ (a a' : Nat) (m1 m2 : PreAcceptReply),
        Msg.preAcceptReply m1 ∈ S.sent a (parX p).q ∧ Msg.preAcceptReply m2 ∈ S.sent a' (parX p).q ∧
        parX m1 = parX p ∧ parX m2 = parX p ∧ m1.ballot = initBal (parX p) ∧
        m2.ballot = initBal (parX p) ∧ (m1.seq ≠ m2.seq ∨ m1.deps ≠ m2.deps) := by
      by_cases hae : (parLb lb p).allEqual = false
      · obtain ⟨a, a', m1, m2, h1, h2, hx1, hx2, hb1, hb2, hne⟩ := c_aeF hpa5 hae
        rw [hiq] at h1 h2; rw [hbI] at hb1 hb2
        exact Or.inr ⟨a, a', m1, m2, h1, h2, hx1, hx2, hb1, hb2, hne⟩
      · left
        have hae' : (parLb lb p).allEqual = true := by simpa using hae
        have hpre : parPre lb p = true := by
          have hl2 : (parLb2 lb p).lastTriedBallot = lb.lastTriedBallot := by
            unfold parLb2 parLb1; split <;> rfl
          simp only [parPre, hae', Bool.true_and, isInitialBallot, beq_iff_eq, hl2, hbI]
          apply zz_inj
          rw [zz_initBal _ hxq, ← toN_of_zz _ r1]
        have hps := (hA.pm.paSent (parX p) w lb hxq (by rw [← hiq]; exact hw) hlb hbI).1
        simp only [fR] at hps
        have hf : ¬ (3 ≤ (parLb lb p).preAcceptOKs.toNat) := by
          intro h3
          have : (W64 (2 * fR - 1)).sle (parLb lb p).preAcceptOKs = true := by
            rw [slow_sle _ _ (by decide) (by omega)]
            have : (W64 (2 * fR - 1)).toNat = 3 := by decide
            omega
          unfold parFast at hfast; rw [this, hpre] at hfast; cases hfast
        have hs : (parLb lb p).preAcceptsSent.sle (parLb lb p).preAcceptOKs = true := by
          unfold parSlow at hslow; rw [hpre] at hslow
          simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or] at hslow; exact hslow.2
        rw [slow_sle _ _ (by rw [c_pas]; omega) (by omega), c_pas] at hs
        omega
    obtain ⟨B, hBn, hBl, hB⟩ := slow_fb S hS (parX p) hxq (by rw [← hiq]; exact hidle.1) w lb
      (by rw [← hiq]; exact hw) hlb hpa hbI v0 (by rw [← hiq, ← hbI]; exact hph0) hcase u
    refine Or.inl ⟨B, hBn, hBl, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hB a ha
    exact ⟨h1, h2, slow_noPA_lift hH' hpend (by rw [hiq]; exact h2) h3⟩
  have hdlvN := slow_dlv_new S fr i n (.preAcceptReply p) hm
  have hval0 := hA.valOk i _ _ v0 (Or.inl hph0)
  refine inv_accept_start S _ i σ1 (parX p) w lb { parLb lb p with status := stACCEPTED }
    lb.lastTriedBallot ⟨v0.cmds, (parLb lb p).seq, (parLb lb p).deps⟩ _ _ hS hi hidle hH'
    (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))
    ⟨rfl, rfl, by rw [← hσ1]; simp [RState.setInst, bcastAcceptOf], rfl, rfl, rfl⟩
    ⟨by simp [acceptOf, hid], rfl, r1, r2, r3, r4, by simp [acceptOf, c_lt],
      by simp only [acceptOf, c_cmds, hcmd0, Option.getD_some]⟩
    (by rw [← hσ1]; simp [RState.setInst]) (by rw [← hσ1]; simp [RState.setInst])
    (by rw [← hσ1]; exact AuxProof.bumpRB_cls _ _)
    hw hlb (slow_notCom hnc) (by rw [hwbal]; exact Int.le_refl _) rfl
    (zz_nonneg_of_make S hown hlbI.1) ?_ ?_ ?_ hinit ?_
    (hA.cmdsNe.2.2.1 i hi _ w lb v0.cmds hw hlb hcmd0) hval0 ?_ ?_ (Or.inl hbal5) c_pas ?_ ?_
  · -- no Accept at the ballot
    intro r u hacc
    have hmk := hown.2.2.1 r _ _ _ hacc
    obtain rfl := maker_eq S hown hxq hmk hlbI.1
    exact hA.paNoAcc r hi _ w lb hw hlb hpa u hacc
  · intro r u hu
    obtain ⟨-, rfl, -⟩ := (slow_op hS).1 _ _ _ _ _ _ hu hph0
    rfl
  · have hsp := (slow_safe hS).2 i _ _ v0 hph0
    exact ⟨fun b' hr hlt' w' _ => hsp.1 b' hr hlt' w', fun hlt' w' _ => hsp.2 hlt' w'⟩
  · exact c_deps (by rw [hst5]; rcases hpa with h' | h' <;> rw [h'] <;> decide)
  · exact ⟨c_lt, c_ballt, rfl, c_prep, by rw [c_tpa]; exact hlbI.2.2.1, c_cp,
      c_deps (by rw [hst5]; rcases hpa with h' | h' <;> rw [h'] <;> decide),
      by simp only [c_cmds, hcmd0], rfl, rfl⟩
  · obtain ⟨Q', q1', q2', q3'⟩ := hlbI.2.2.2.2.2.2.1
    refine ⟨⟨Q, hQn, hQl, fun a m' hq => ?_⟩, ⟨Q', q1', by rw [c_aok]; exact q2', fun a hq => ?_⟩⟩
    · obtain ⟨h1, h2, h3, h4, h5, -⟩ := hQ a m' hq
      refine ⟨h1, h2, ?_, h4, by simp only [c_lt]; exact h5⟩
      rcases h3 with h3 | ⟨rfl, rfl⟩
      · exact hH'.deliveredMsg_old h3
      · exact hdlvN
    · obtain ⟨h1, h2, m', h3, h4, h5⟩ := q3' a hq
      exact ⟨h1, h2, m', hH'.deliveredMsg_old h3, h4, by simp only [c_lt]; exact h5⟩
  · intro hne
    refine slow_wit S hS i hi (parX p) lb.lastTriedBallot v0 hph0 _ _ Q hQn (by omega)
      (fun a m' hq => ?_) hne
    obtain ⟨-, h2, h3, h4, h5, h6⟩ := hQ a m' hq
    refine ⟨h2, ?_, Option.some.inj h4, h5, (h6 hpa5).1⟩
    rcases h3 with h3 | ⟨rfl, rfl⟩
    · exact slow_dlv_msgs h3
    · exact hpm
  · refine slow_sup S hS i hi (parX p) lb.lastTriedBallot v0 hph0 Q hQn (by omega)
      (fun a m' hq => ?_)
    obtain ⟨-, h2, h3, h4, h5, -⟩ := hQ a m' hq
    refine ⟨h2, ?_, Option.some.inj h4, h5⟩
    rcases h3 with h3 | ⟨rfl, rfl⟩
    · exact slow_dlv_msgs h3
    · exact hpm

end PARProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
