/-
`handlePreAcceptReply`: The fast path: `RecCommitNewProof.inv_commit_new` with `FastProof.fast_agree`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPARBase
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.RecCommitNew
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.FastPath
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HAcceptReply

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PARProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof LbCountProof RecCommitProof RecAcceptProof

/-- The fast quorum on a counter. -/
theorem par_sle3 (o : w64) (h : o.toNat ≤ 5) (hs : (W64 (2 * fR - 1)).sle o = true) :
    3 ≤ o.toNat := by
  rw [BitVec.sle, BitVec.toInt_eq_toNat_of_lt, BitVec.toInt_eq_toNat_of_lt] at hs
  · simp [fR, W64] at hs; omega
  · omega
  · simp [fR, W64]

/-- A proposal at or below the initial ballot is the initial Phase 1's. -/
theorem par_propAt_init {S : Sys} (hS : Inv S) {x : InstId} (hxq : x.q < nR) {q : Nat}
    {v0 : Val} (hph : S.ev q (.phase1 x (initBal x) v0)) {c : w32} {cs : List WCmd}
    (hp : S.propAt x c cs) (hc : zz c ≤ zz (initBal x)) : c = initBal x ∧ cs = v0.cmds := by
  have hown := AcceptReplyProof.inv_own' hS
  have hop := AcceptReplyProof.inv_op hS
  have hmk : ∀ r, S.ev r (.makeBallot x c) → c = initBal x := by
    intro r h
    rcases (hown.1 r x c h).1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact SafeProof.zz_inj (by rw [h1, zz_initBal x hxq])
    · rw [zz_initBal x hxq] at hc; simp [nR] at hxq h1; omega
  have hphc : ∀ r u, S.ev r (.phase1 x c u) → c = initBal x ∧ u.cmds = v0.cmds := by
    intro r u h
    obtain ⟨p1, p2, -, hp1, -⟩ := hown.2.1 _ _ _ _ h
    have hc' := hmk r (List.mem_of_getElem? hp1)
    subst hc'
    exact ⟨rfl, by rw [(hop.1 _ _ _ _ _ _ h hph).2.1]⟩
  have hacc : ∀ r u, S.ev r (.accept x c u) → c = initBal x ∧ u.cmds = v0.cmds := by
    intro r u h
    have hc' := hmk r (hown.2.2.1 _ _ _ _ h)
    subst hc'
    exact ⟨rfl, hop.2.2 _ _ _ _ _ _ hph h⟩
  rcases hp with ⟨q', st, u, hst, hv, rfl⟩ | ⟨q', u, hq, rfl⟩
  · rcases hst with hst | rfl
    · obtain ⟨l, v1, hl, hc1⟩ := (AcceptReplyProof.inv_vfp hS).1 _ _ _ _ _ hv hst
      obtain ⟨e1, e2⟩ := hphc _ _ hl
      exact ⟨e1, by rw [hc1, e2]⟩
    · obtain ⟨l, hl⟩ := (AcceptReplyProof.inv_vfp hS).2 _ _ _ _ hv
      exact hacc _ _ hl
  · exact hphc _ _ hq

theorem par_inv_rrv {S : Sys} (hS : Inv S) : Inv.repliesReportVotes S :=
  let ⟨_, _, _, _, _, _, _, _, h, _⟩ := hS.1; h

/-- A reply at the initial ballot to its pre-accepting leader is not ACCEPTED. -/
theorem par_not_acc {S : Sys} (hS : Inv S) {a r : Nat} (hr : r < nR) {x : InstId}
    (hxq : x.q < nR) (hrq : r = x.q) {m : PreAcceptReply}
    (hmsg : Msg.preAcceptReply m ∈ S.msgs a r) (hx : parX m = x) (hb : m.ballot = initBal x)
    {w : InstRec} {lb : LbRec} (hw : (S.rep r).inst x = some w) (hlb : w.lb = some lb)
    (hpa : isPA lb.status) (hlt : lb.lastTriedBallot = initBal x) : m.status ≠ stACCEPTED := by
  intro hst
  obtain ⟨-, -, hacc, -⟩ := (par_inv_rrv hS).2.1 a r m hmsg
  obtain ⟨v', hv', -, -⟩ := hacc hst
  obtain ⟨ℓ, hl⟩ := (AcceptReplyProof.inv_vfp hS).2 _ _ _ _ hv'
  obtain ⟨-, h0, hle, -⟩ := hS.2.pm.parSt a r m hmsg
  have hmk := (AcceptReplyProof.inv_own' hS).2.2.1 _ _ _ _ hl
  have hx' : (⟨toN m.replica, toN m.inst⟩ : InstId) = x := hx
  rw [hx'] at hl hmk
  rcases ((AcceptReplyProof.inv_own' hS).1 _ _ _ hmk).1 with ⟨h1, h2⟩ | ⟨h1, -⟩
  · have : m.vballot = lb.lastTriedBallot :=
      SafeProof.zz_inj (by rw [h1, hlt, zz_initBal _ hxq])
    rw [this, h2, ← hrq] at hl
    exact hS.2.paNoAcc r hr _ w lb hw hlb hpa _ hl
  · rw [hb, zz_initBal _ hxq] at hle; simp [nR] at hxq h1; omega

/-- The fast path: `RecCommitNewProof.inv_commit_new` with `FastProof.fast_agree`. -/
theorem par_fast (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (parX p) = some w) (hlb : w.lb = some lb)
    (hnc : stGe w.status stCOMMITTED = false) (hlt : lb.lastTriedBallot.slt w.bal = false)
    (hb : p.ballot = lb.lastTriedBallot) (hpa : isPA lb.status)
    (hfast : parFast lb p = true)
    (h : hPreAcceptReply (S.rep i) p = parFastOut (S.rep i) w lb p) :
    Inv (S.deliver fr i n (.preAcceptReply p)) := by
  have hpm := mem_msgs_of_sent S hm
  have hA := hS.2
  obtain ⟨hfi, ⟨v0, hph, hlbc⟩, hprep, hbal, hle4, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10,
    -, kst1, kbl, kball, kdeps, ⟨Q, q1, q2, q3⟩, -⟩ :=
    par_common S fr i n hS hi hfr hidle hn p hm w lb hw hlb hnc hlt hb hpa
  obtain ⟨hmkI, -, htpa, -, -, -, ⟨QA, qa1, qa2, qa3⟩, -, -⟩ :=
    AcceptReplyProof.inv_lbI hS i hi _ w lb hw hlb
  -- the fast path's condition
  have hf1 : (W64 (2 * fR - 1)).sle (parLb lb p).preAcceptOKs = true ∧
      (parLb lb p).allEqual = true ∧
      isInitialBallot (parLb2 lb p).lastTriedBallot p.replica = true := by
    simp only [parFast, parPre, Bool.and_eq_true] at hfast
    exact ⟨hfast.1, hfast.2.1, hfast.2.2⟩
  have hl2 : (parLb2 lb p).lastTriedBallot = lb.lastTriedBallot := by
    unfold parLb2; split <;> rfl
  have hltR : lb.lastTriedBallot = p.replica := by
    have := hf1.2.2; rw [hl2] at this; simpa [isInitialBallot] using this
  have hae := hf1.2.1
  have h3 : 3 ≤ (parLb lb p).preAcceptOKs.toNat := par_sle3 _ (by omega) hf1.1
  have hst' : (parLb lb p).status = lb.status := kst1 (by omega)
  have hpa' : isPA (parLb lb p).status := by rw [hst']; exact hpa
  have hball : (parLb lb p).ballot = lb.lastTriedBallot := kbl hpa'
  -- the initial ballot
  obtain ⟨r1, r2, r3, r4⟩ := (AcceptReplyProof.inv_msgWf hS fr i _ hpm).1 p.replica p.inst rfl
  have hxq : (parX p).q < nR := by have := toN_of_zz _ r1; show toN p.replica < nR; omega
  have hlt0 : lb.lastTriedBallot = initBal (parX p) := by
    rw [hltR]; exact SafeProof.zz_inj (by rw [zz_initBal _ hxq]; exact (toN_of_zz _ r1).symm)
  have hiq : i = (parX p).q := by
    rcases ((AcceptReplyProof.inv_own' hS).1 _ _ _ hmkI).1 with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · rw [hlt0, zz_initBal _ hxq] at h1; simp [nR] at hxq h1; omega
  -- the step
  unfold parFastOut at h
  generalize hL : ({ parLb lb p with status := stCOMMITTED } : LbRec) = lb6 at h
  dsimp only at h
  generalize hv : lbVal lb6 = v at h
  generalize hσ1 : updateCommitted ((bumpRecvBallot (S.rep i) p.ballot).setInst (parX p)
    { w with status := stCOMMITTED, bal := lb6.ballot, cmds := lb6.cmds, deps := lb6.deps,
             seq := lb6.seq, lb := some lb6 }) (parX p).q = σ1 at h
  generalize hmc : commitOf σ1 p.replica p.inst lb6 = mc at h
  generalize hB : bcastCommitOf σ1 (parX p) mc = B at h
  have hH := hs_deliver S fr i n (.preAcceptReply p) hidle hm
  have hout : hMsg (S.rep i) (.preAcceptReply p) = (σ1, [Out.ev (.commit (parX p) lb6.ballot v),
      Out.ev (.fastCommit (parX p) v), Out.bcast B]) := by simp only [hMsg]; exact h
  rw [hout] at hH
  have hH' : HS S (S.deliver fr i n (.preAcceptReply p)) i σ1
      (.commit (parX p) lb6.ballot v :: (if true then [.fastCommit (parX p) v] else []))
      (fun _ => []) B.norm := by
    have e1 : evsOf [Out.ev (.commit (parX p) lb6.ballot v), Out.ev (.fastCommit (parX p) v),
        Out.bcast B] =
        .commit (parX p) lb6.ballot v :: (if true then [.fastCommit (parX p) v] else []) := rfl
    have e2 : sendsOf [Out.ev (.commit (parX p) lb6.ballot v), Out.ev (.fastCommit (parX p) v),
        Out.bcast B] = fun _ => [] := by
      funext to; rfl
    have e3 : pendFold [Out.ev (.commit (parX p) lb6.ballot v), Out.ev (.fastCommit (parX p) v),
        Out.bcast B] none = B.norm := rfl
    rw [e1, e2, e3] at hH; exact hH
  have hb6 : lb6.ballot = initBal (parX p) := by rw [← hL, ← hlt0]; exact hball
  have hc6 : lb6.cmds = some v0.cmds := by rw [← hL, ← hlbc]; exact k2
  have hvc : v.cmds = v0.cmds := by rw [← hv]; simp only [lbVal, hc6, Option.getD_some]
  have hvs : v.seq = (parLb lb p).seq := by rw [← hv, ← hL]; rfl
  have hvd : v.deps = (parLb lb p).deps := by rw [← hv, ← hL]; rfl
  have hpaN : (parLb lb p).status ≠ stNONE := by
    rw [hst']; rcases hpa with h1 | h1 <;> rw [h1] <;> decide
  have hph0 : S.ev i (.phase1 (parX p) (initBal (parX p)) v0) := hlt0 ▸ hph
  -- the counted replies
  have hrQ : ∀ a m', (a, m') ∈ Q → Msg.preAcceptReply m' ∈ S.msgs a i ∧ parX m' = parX p ∧
      m'.ballot = initBal (parX p) := by
    intro a m' hq
    obtain ⟨-, -, c3, c4, c5, -⟩ := q3 a m' hq
    refine ⟨?_, by simpa [Msg.instOf] using c4, c5.trans hlt0⟩
    rcases c3 with ⟨n', hn', -⟩ | ⟨rfl, rfl⟩
    · exact mem_msgs_of_sent S hn'
    · exact hpm
  have hQf : ∀ a m', (a, m') ∈ Q → a < nR ∧ a ≠ (parX p).q ∧
      Msg.preAcceptReply m' ∈ S.msgs a (parX p).q ∧
      (Msg.preAcceptReply m').instOf = some (parX p) ∧ m'.ballot = initBal (parX p) ∧
      m'.seq = v.seq ∧ m'.deps = v.deps ∧ (isPA m'.status ∨ isCommitted m'.status) := by
    intro a m' hq
    obtain ⟨c1, c2, -, c4, -, c6⟩ := q3 a m' hq
    obtain ⟨hmsg, hx', hb'⟩ := hrQ a m' hq
    obtain ⟨e1, e2⟩ := (c6 hpa').2.2 hae
    refine ⟨c1, by rw [← hiq]; exact c2, by rw [← hiq]; exact hmsg, c4, hb', e1.trans hvs.symm,
      e2.trans hvd.symm, ?_⟩
    rcases (hA.pm.parSt a i m' hmsg).1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 (par_not_acc hS hi hxq hiq hmsg hx' hb' hw hlb hpa hlt0)
    · exact Or.inr h1
  have hcomm : ∀ a m', (a, m') ∈ Q → isCommitted m'.status →
      ∃ u, S.committedVal (parX p) u ∧ u.seq = m'.seq ∧ u.deps = m'.deps ∧ u.cmds = v0.cmds := by
    intro a m' hq hcm
    obtain ⟨hmsg, hx', hb'⟩ := hrQ a m' hq
    obtain ⟨c, u, hev, hle, hs, hd⟩ := hA.pm.parCom a i m' hmsg hcm
    rw [hx'] at hev
    have hle' : zz c ≤ zz (initBal (parX p)) := by rw [← hb']; exact hle
    obtain ⟨-, hcu⟩ := par_propAt_init hS hxq hph0 (hA.pm.commitProp _ _ _ _ hev hle') hle'
    exact ⟨u, Or.inl ⟨a, c, hev⟩, hs, hd, hcu⟩
  have hfa := FastProof.fast_agree S hS.1 (parX p) hxq v v0 (by rw [← hiq]; exact hph0) hvc
    ⟨w, by rw [← hiq]; exact hw, by rw [hbal, hlt0]⟩ Q q1 (by rw [q2]; simp only [fR]; omega)
    hQf hcomm
  have hdeps : depsOk v.deps := by rw [hvd]; exact kdeps hpaN
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := AcceptReplyProof.bump_fields (S.rep i) p.ballot
  have hσf : σ1.id = (S.rep i).id ∧ σ1.peerOrder = (S.rep i).peerOrder ∧
      σ1.crtInstance = (S.rep i).crtInstance ∧ σ1.conflicts = (S.rep i).conflicts ∧
      σ1.execedUpTo = (S.rep i).execedUpTo ∧ σ1.store = (S.rep i).store := by
    rw [← hσ1]
    exact ⟨by simp [updateCommitted, RState.setInst, e1], by simp [updateCommitted, RState.setInst, e2],
      by simp [updateCommitted, RState.setInst, e3], by simp [updateCommitted, RState.setInst, e4],
      by simp [updateCommitted, RState.setInst, e5], by simp [updateCommitted, RState.setInst, e6]⟩
  have hwb := (AcceptReplyProof.inv_bal hS).1 i hi _ w hw
  obtain ⟨hvbl, -⟩ := hA.paLeader i hi _ w lb hw hlb hpa ⟨v0, hph⟩ hnc hbal
  refine RecCommitNewProof.inv_commit_new S _ i σ1 (parX p) w lb lb6 lb6.ballot v true B mc hS hi
    hidle hH' (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))
    ⟨by rw [← hB]; rfl, by rw [← hB]; rfl,
      by rw [← hB]; simp only [bcastCommitOf]; rw [hσf.2.1], by rw [← hB]; rfl,
      by rw [← hB]; rfl, by rw [← hB]; rfl⟩
    ⟨by rw [← hmc]; rfl, by rw [← hmc]; exact r1, by rw [← hmc]; exact r2, by rw [← hmc]; exact r3,
      by rw [← hmc]; exact r4, by rw [← hmc, ← hv]; rfl,
      by rw [← hmc]; simp only [commitOf]; rw [hb6, zz_initBal _ hxq]; omega⟩
    ?_ hσf (by rw [← hσ1]; exact AuxProof.bumpRB_cls _ _) hw hlb (not_comm_of hnc) (Int.le_of_eq (by rw [hbal, hb6, hlt0]))
    (Int.le_of_eq (by rw [hb6, hlt0])) (by rw [hb6, ← hlt0, ← hbal]; exact hwb)
    (by rw [hvbl, hlt0, zz_initBal _ hxq]; omega) hfa.1
    (hfa.2.elim Or.inl (fun h' => Or.inr (Or.inr ⟨h', rfl⟩))) ?_
    (by rw [hvc]; exact hA.valOk _ _ _ _ (Or.inl hph)) hdeps
    (by rw [hvc]; exact hA.cmdsNe.2.2.2.2.2 _ _ _ _ (Or.inl hph))
    (fun _ => Or.inr ⟨i, v0, by rw [hb6]; exact hph0, hvc.symm⟩)
    (by rw [← hmc]; simp only [commitOf]; exact Or.inr ⟨i, v0, by rw [hb6]; exact hph0, hvc.symm⟩)
    (fun _ => ⟨hiq, Int.le_of_eq (by rw [hbal, hlt0])⟩)
    ⟨by rw [← hL]; exact k1, by rw [← hL]; exact kball, by rw [← hL], by rw [← hL]; exact k5,
      by rw [← hL]; exact k4.trans htpa, by rw [← hL]; exact k3, by rw [← hL]; exact k8,
      by rw [← hL]; exact kdeps hpaN, by rw [hc6, hvc]⟩ ?_
  · -- the record
    rw [← hσ1]
    simp only [updateCommitted, RState.setInst, AcceptReplyProof.bump_inst]
    congr 1; congr 1
    simp only [RecCommitNewProof.comNew]
    rw [← hv]; simp only [lbVal, hc6, Option.getD_some]
  · -- witnesses
    rcases hfa.2 with h' | ⟨W, hW, hlW, hWm⟩
    · exact Or.inl h'
    · refine Or.inr (Or.inr ⟨W, hW, by simp only [fR] at hlW ⊢; omega, fun r hr => ?_⟩)
      obtain ⟨c1, -, st, hst, hvote⟩ := hWm r hr
      exact ⟨c1, v.deps, hA.paAttrs _ _ _ _ _ hst hvote, hdeps.1, hdeps.1, fun _ _ => Int.le_refl _⟩
  · -- the counted replies
    have hdn := AcceptReplyProof.deliveredMsg_new S fr i n (.preAcceptReply p) hm
    refine ⟨⟨Q, q1, by rw [← hL]; exact q2, fun a m' hq => ?_⟩,
      ⟨QA, qa1, by rw [← hL]; show QA.length = (parLb lb p).acceptOKs.toNat; rw [k9]; exact qa2,
        fun a ha => ?_⟩⟩
    · obtain ⟨c1, c2, c3, c4, c5, -⟩ := q3 a m' hq
      refine ⟨c1, c2, ?_, c4, by rw [← hL]; exact c5.trans k1.symm⟩
      rcases c3 with c3 | ⟨rfl, rfl⟩
      · exact hH'.deliveredMsg_old c3
      · exact hdn
    · obtain ⟨c1, c2, m', c3, c4, c5⟩ := qa3 a ha
      exact ⟨c1, c2, m', hH'.deliveredMsg_old c3, c4, by rw [← hL]; exact c5.trans k1.symm⟩

end PARProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
