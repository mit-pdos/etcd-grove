/-
`handlePrepare` (`hPrepare`): the law `inv_deliver_prepare`. The record's `bal` is raised to the
Prepare's ballot (if higher) and the replica reports its record (a `prepReport`: the vote it holds,
the committed value, or NONE) at the record's new `bal`, its promise.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecHS

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PrepareProof

open HStepProof HLocal SafeProof

/-- The record `hPrepare` writes. -/
def prepRec (w : InstRec) (p : Prepare) : InstRec :=
  if w.bal.slt p.ballot then { w with bal := p.ballot } else w

/-- The report `hPrepare` sends. -/
def prepRep (σ : RState) (w : InstRec) (p : Prepare) : PrepareReply :=
  { acceptorId := W32 σ.id, replica := p.replica, inst := p.inst, ballot := w.bal,
    vballot := w.vbal, status := w.status, command := w.cmds.getD [], seq := w.seq,
    deps := w.deps }

theorem hPrepare_eq (σ : RState) (p : Prepare) :
    hPrepare σ p =
      ((bumpRecvBallot σ p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
          (prepRec (recOr σ ⟨toN p.replica, toN p.inst⟩) p),
        [.send (toN p.leaderId)
          (.prepareReply (prepRep σ (prepRec (recOr σ ⟨toN p.replica, toN p.inst⟩) p) p))]) := by
  have hr : recOr (bumpRecvBallot σ p.ballot) ⟨toN p.replica, toN p.inst⟩ =
      recOr σ ⟨toN p.replica, toN p.inst⟩ := by simp [recOr]
  unfold hPrepare
  simp only [getOrDefault_eq, hr, setInst_setInst]
  simp [prepRec, prepRep, RState.setInst]

theorem prepRec_fields (w : InstRec) (p : Prepare) :
    (prepRec w p).cmds = w.cmds ∧ (prepRec w p).vbal = w.vbal ∧ (prepRec w p).status = w.status ∧
    (prepRec w p).seq = w.seq ∧ (prepRec w p).deps = w.deps ∧ (prepRec w p).lb = w.lb ∧
    (prepRec w p).id = w.id ∧ zz w.bal ≤ zz (prepRec w p).bal ∧
    zz p.ballot ≤ zz (prepRec w p).bal ∧
    ((prepRec w p).bal = w.bal ∨ (prepRec w p).bal = p.ballot) := by
  unfold prepRec
  split
  · rename_i h; have := (slt_iff _ _).mp h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp; omega, by simp, Or.inr rfl⟩
  · rename_i h
    have : zz p.ballot ≤ zz w.bal := (slt_false _ _).mp (by simpa using h)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _, this, Or.inl rfl⟩

theorem prepare_step (S : Sys) (fr i n : Nat) (p : Prepare) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some (.prepare p)) (hfr : fr < nR)
    (hldr : p.leaderId = W32 fr) :
    HS S (S.deliver fr i n (.prepare p)) i
      ((bumpRecvBallot (S.rep i) p.ballot).setInst ⟨toN p.replica, toN p.inst⟩
          (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p))
      [.sent fr (.prepareReply
        (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p))]
      (fun to => if to = fr then [.prepareReply
        (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p)] else [])
      none := by
  have hH := hs_deliver S fr i n (.prepare p) hidle hm
  simp only [hMsg] at hH
  rw [hPrepare_eq] at hH
  have hl : toN p.leaderId = fr := by rw [hldr]; exact toN_W32 fr hfr
  dsimp only at hH
  have h1 : evsOf [Out.send (toN p.leaderId) (Msg.prepareReply
      (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p))] =
      [.sent fr (.prepareReply
        (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p))] := by
    simp [evsOf, Out.hev, hl]
  have h2 : sendsOf [Out.send (toN p.leaderId) (Msg.prepareReply
      (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p))] =
      (fun to => if to = fr then [.prepareReply
        (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p)] else []) := by
    funext to
    simp only [sendsOf, List.filterMap_cons, List.filterMap_nil, Out.sendTo, hl]
    by_cases h : fr = to
    · subst h; simp
    · simp [h, Ne.symm h]
  have h3 : pendFold [Out.send (toN p.leaderId) (Msg.prepareReply
      (prepRep (S.rep i) (prepRec (recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩) p) p))] none =
      none := rfl
  rw [h1, h2, h3] at hH; exact hH

/-! ## The step's context -/

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

theorem ctx_basic :
    Msg.prepare p ∈ S.msgs fr i ∧ p.leaderId = W32 fr ∧ S.ev fr (.makeBallot x p.ballot) ∧
    x.q < nR ∧ x.i + 1 < MAX_INSTANCE ∧ 0 ≤ zz p.inst ∧ (x.i : Int) = zz p.inst ∧
    0 ≤ zz p.ballot ∧ fr ≠ i := by
  have hpm : Msg.prepare p ∈ S.msgs fr i := mem_msgs_of_sent S hm
  obtain ⟨hldr, hmk⟩ := hS.1.2.2.2.2.2.1.2.2.2.1 fr i p hpm
  rw [← hx] at hmk
  obtain ⟨r1, r2, r3, r4⟩ := (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
  refine ⟨hpm, hldr, hmk, ?_, ?_, r3, ?_, zz_nonneg_of_make S hS.1.2.2.2.2.2.1 hmk,
    (hS.1.1.2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2⟩
  · subst hx; simp only [toN, zz] at r1 r2 ⊢; omega
  · subst hx; exact r4
  · subst hx; exact toN_of_zz _ r3

theorem ctx_rec : (∀ r y w, (S'.rep r).inst y = some w →
      (r = i ∧ y = x ∧ w = w') ∨ (S.rep r).inst y = some w) ∧
    (∀ r y w, (S.rep r).inst y = some w →
      (r = i ∧ y = x ∧ w = w0) ∨ (S'.rep r).inst y = some w) ∧
    (S'.rep i).inst x = some w' ∧
    (∀ r y, (r ≠ i ∨ y ≠ x) → (S'.rep r).inst y = (S.rep r).inst y) := by
  have hr : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases h : r = i
    · subst h; simp only [upd_same, setInst_inst, bumpRB_inst, true_and]
    · simp [upd_other _ _ _ _ h, h]
  refine ⟨fun r y w h => ?_, fun r y w h => ?_, by rw [hr]; simp, fun r y h => ?_⟩
  · rw [hr] at h; split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, rfl, h.symm⟩
    · exact Or.inr h
  · by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      rcases hro with h' | ⟨h', -⟩
      · rw [h'] at h; simp only [Option.some.injEq] at h; exact Or.inl ⟨rfl, rfl, h.symm⟩
      · rw [h'] at h; cases h
    · right; rw [hr, if_neg hc]; exact h
  · rw [hr, if_neg (by rintro ⟨rfl, rfl⟩; rcases h with h | h <;> exact h rfl)]

theorem ctx_fields : ∀ r, (S'.rep r).id = (S.rep r).id ∧
    (S'.rep r).peerOrder = (S.rep r).peerOrder ∧ (S'.rep r).conflicts = (S.rep r).conflicts ∧
    (S'.rep r).execedUpTo = (S.rep r).execedUpTo ∧ (S'.rep r).store = (S.rep r).store ∧
    (S'.rep r).crtInstance = (S.rep r).crtInstance := by
  intro r
  rw [hH.rep]
  by_cases h : r = i
  · subst h; simp only [upd_same]
    exact ⟨by simp [RState.setInst], by simp [RState.setInst], by simp [RState.setInst],
      by simp [RState.setInst], by simp [RState.setInst], by simp [RState.setInst]⟩
  · simp [h]

theorem ctx_w : zz w0.bal ≤ zz w'.bal ∧ zz p.ballot ≤ zz w'.bal ∧ w'.lb = w0.lb ∧
    w'.id = w0.id ∧ w'.cmds = w0.cmds ∧ w'.vbal = w0.vbal ∧ w'.status = w0.status ∧
    w'.seq = w0.seq ∧ w'.deps = w0.deps ∧ (w'.bal = w0.bal ∨ w'.bal = p.ballot) ∧
    instVal w' = instVal w0 := by
  subst hw'
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := prepRec_fields w0 p
  exact ⟨f8, f9, f6, f7, f1, f2, f3, f4, f5, f10, by simp [instVal, f1, f4, f5]⟩

theorem ctx_ev : ∀ r e, S'.ev r e → S.ev r e ∨ (r = i ∧ e = .sent fr (.prepareReply rp)) := by
  intro r e he
  rcases (hH.ev_iff r e).mp he with h | ⟨hr, h⟩
  · exact Or.inl h
  · simp only [List.mem_singleton] at h; exact Or.inr ⟨hr, h⟩

theorem ctx_ev_old (r : Nat) (e : Event) (he : S'.ev r e)
    (hk : e ≠ .sent fr (.prepareReply rp)) : S.ev r e := by
  rcases ctx_ev S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r e he with h | ⟨-, h⟩
  · exact h
  · exact absurd h hk

theorem ctx_notE (e : Event) (hk : e ≠ .sent fr (.prepareReply rp)) :
    i = i → e ∉ [Event.sent fr (.prepareReply rp)] := by
  intro _ he; simp only [List.mem_singleton] at he; exact hk he

theorem ctx_msgs : ∀ fr' to m, m ∈ S'.msgs fr' to → m ∈ S.msgs fr' to ∨
    (fr' = i ∧ to = fr ∧ m = .prepareReply rp) := by
  intro fr' to m hm'
  rcases hH.mem_msgs.mp hm' with h | ⟨hf, h | h⟩
  · exact Or.inl h
  · split at h
    · rename_i ht; simp only [List.mem_singleton] at h; exact Or.inr ⟨hf, ht, h⟩
    · cases h
  · simp [intendedOf] at h

/-- `w0` is a real record or the default. -/
theorem ctx_w0 : (w0.status = stNONE ∨ isPA w0.status ∨ w0.status = stACCEPTED ∨
      isCommitted w0.status) ∧ zz w0.vbal ≤ zz w0.bal ∧ (w0.status ≠ stNONE → depsOk w0.deps) ∧
    w0.id = x := by
  rcases hro with h | ⟨-, rfl⟩
  · exact ⟨hS.2.stRange i hi x w0 h, hS.1.2.2.2.2.1.1 i hi x w0 h,
      (hS.1.1.2.1 i hi x w0 h).2.2.2.1, (hS.1.1.2.1 i hi x w0 h).1⟩
  · exact ⟨Or.inl rfl, by simp [newInstanceDefault], fun h => absurd rfl h, rfl⟩

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

theorem ctx_rp : rp.acceptorId = W32 i ∧ (⟨toN rp.replica, toN rp.inst⟩ : InstId) = x ∧
    rp.ballot = w'.bal ∧ rp.vballot = w0.vbal ∧ rp.status = w0.status ∧
    (⟨rp.command, rp.seq, rp.deps⟩ : Val) = instVal w0 ∧ rp.deps = w0.deps ∧
    rp.replica = p.replica ∧ rp.inst = p.inst := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8, h9, -, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  subst hrp
  refine ⟨by simp [prepRep, hS.1.1.1 i hi], by simp [prepRep, hx], rfl, by simp [prepRep, h6],
    by simp [prepRep, h7], by simp [prepRep, instVal, h5, h8, h9], by simp [prepRep, h9], rfl, rfl⟩

theorem ctx_wf : Inv.wf S' := by
  obtain ⟨hpm, hldr, hmk, hxq, hxi, hpi0, hpi, hb0, hfi⟩ := ctx_basic S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have F := ctx_fields S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, hlbeq, hid, -, -, hst, -, hdeq, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, hd0, hid0⟩ := ctx_w0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hS.1.1
  have hA := hS.2
  have hw0 : (∀ lb, w0.lb = some lb → lb.status ≠ stNONE → depsOk lb.deps) ∧
      (x.q = i → w0.lb ≠ none) ∧
      (∀ lb ps, w0.lb = some lb → lb.clientProposals = some ps → S.owner x = some ps) := by
    rcases hro with h | ⟨h, rfl⟩
    · obtain ⟨-, -, -, -, g5, g6, g7⟩ := w2 i hi x w0 h
      exact ⟨g5, g6, g7⟩
    · refine ⟨fun lb h' => by simp [newInstanceDefault] at h', fun hq => ?_,
        fun lb ps h' => by simp [newInstanceDefault] at h'⟩
      exfalso
      have hc := hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)
      rw [← hq] at h
      obtain ⟨w, lb, hw, -⟩ := hA.ownRow x.q hxq x.i hc
      rw [show (⟨x.q, x.i⟩ : InstId) = x from rfl, h] at hw; cases hw
  refine ⟨fun r hr => by rw [(F r).1]; exact w1 r hr, fun r hr y w hw => ?_,
    fun r hr q hq => by rw [(F r).2.2.2.2.2]; exact w3 r hr q hq,
    fun r hr q k p0 hk => ?_, fun r hr q hq m' hm' => ?_,
    fun fr' to hne => ?_, fun fr' to n' hn' => ?_, fun r b hb => ?_⟩
  · rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w
      obtain ⟨g3, g4, g5⟩ := hw0
      refine ⟨hid ▸ hid0, hxq, hxi, fun hs => ?_, fun lb hlb => g3 lb (hlbeq ▸ hlb),
        fun hq => hlbeq ▸ g4 hq, fun lb ps hlb => ?_⟩
      · rw [hdeq]; exact hd0 (hst ▸ hs)
      · rw [hH.owner]; exact g5 lb ps (hlbeq ▸ hlb)
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := w2 r hr y w h
      exact ⟨g1, g2, g3, g4, g5, g6, fun lb ps hlb hps => by rw [hH.owner]; exact g7 lb ps hlb hps⟩
  · rw [(F r).2.2.1] at hk
    obtain ⟨k1, k2, k3⟩ := w4 r hr q k p0 hk
    refine ⟨k1, fun h => ?_, fun h => ?_⟩
    · intro hn'
      cases h' : (S.rep r).inst ⟨q, toN p0.last⟩ with
      | none => exact k2 h h'
      | some w =>
        rcases R2 r _ w h' with ⟨hr', hy, -⟩ | h''
        · subst hr'; rw [hy] at hn'; rw [R3] at hn'; cases hn'
        · rw [h''] at hn'; cases hn'
    · intro hn'
      cases h' : (S.rep r).inst ⟨q, toN p0.lastWrite⟩ with
      | none => exact k3 h h'
      | some w =>
        rcases R2 r _ w h' with ⟨hr', hy, -⟩ | h''
        · subst hr'; rw [hy] at hn'; rw [R3] at hn'; cases hn'
        · rw [h''] at hn'; cases hn'
  · rw [(F r).2.2.2.1] at hm'
    obtain ⟨w, hw, hs⟩ := w5 r hr q hq m' hm'
    rcases R2 r _ w hw with ⟨hr', hy, hw''⟩ | h''
    · subst hr'; subst hw''; refine ⟨w', by rw [hy]; exact R3, ?_⟩
      rw [hst]; exact hs
    · exact ⟨w, h'', hs⟩
  · rw [hH.msgs] at hne
    by_cases h0 : S.msgs fr' to = []
    · rw [h0, List.nil_append] at hne
      split at hne
      · rename_i hf; rw [hf]
        simp only [intendedOf, List.append_nil] at hne
        split at hne
        · rename_i ht; rw [ht]; exact ⟨hi, hfr, Ne.symm hfi⟩
        · exact absurd rfl hne
      · exact absurd rfl hne
    · exact w6 fr' to h0
  · rcases hH.delOk fr' to n' hn' with h | h
    · rw [hH.sent]; exact w7 fr' to n' h
    · rw [hH.sent]; exact h
  · rw [hH.pending] at hb
    by_cases hr : r = i
    · subst hr; simp at hb
    · rw [upd_other _ _ _ _ hr] at hb
      obtain ⟨d1, d2, d3, d4, d5, d6, w, lb, hw, hlb⟩ := w8 r b hb
      refine ⟨d1, by rw [hH.execCur]; exact d2, d3, d4, d5, d6, w, lb, ?_, hlb⟩
      rw [R4 r _ (Or.inl hr)]; exact hw

theorem ctx_msgWf : Inv.msgWf S' := by
  obtain ⟨hpm, -⟩ := ctx_basic S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, -, -, hst, -, hdeq, hrr, hri⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, hd0, -⟩ := ctx_w0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to m hm' with h | ⟨-, -, rfl⟩
  · exact hS.1.2.1 fr' to m h
  · refine ⟨fun q n' h => ?_, fun ds hds => ?_⟩
    · simp only [Msg.rawId, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hrr, hri]; exact (hS.1.2.1 fr i _ hpm).1 p.replica p.inst rfl
    · simp only [Msg.depsFields] at hds
      split at hds
      · cases hds
      · rename_i hs; simp only [List.mem_singleton] at hds; subst hds
        rw [hdeq]; exact hd0 (hst ▸ hs)

theorem ctx_rt : Inv.replyTargets S' := by
  obtain ⟨-, -, hmk, -, -, -, -, -, hfi⟩ := ctx_basic S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, hlbeq, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, hrx, -⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro fr' to m y hm' hy hk
  rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to m hm' with h | ⟨-, hto, rfl⟩
  · obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr' to m y h hy hk
    rcases R2 to y w hw with ⟨h1, h2, h3⟩ | h'
    · subst to y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb⟩
    · exact ⟨w, lb, h', hlb⟩
  · simp only [Msg.instOf, Option.some.injEq] at hy
    rw [hrx] at hy; subst hy
    obtain ⟨w, lb, hw, hlb, -⟩ := hS.2.makerLb fr _ p.ballot hfr hmk
    refine ⟨w, lb, ?_, hlb⟩
    rw [hto, R4 _ _ (Or.inl hfi)]; exact hw

theorem ctx_ntpa : Inv.noTPA S' := by
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to m hm' with h | ⟨-, -, rfl⟩
  · exact hS.1.2.2.2.1 fr' to m h
  · exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem ctx_ballots : Inv.ballots S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hwb, -, -, -, -, hvb, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, hvb0, -⟩ := ctx_w0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r hr y w hw => ?_, fun r hr y b st v he => ?_⟩
  · rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; rw [hvb]; exact Int.le_trans hvb0 hwb
    · exact hS.1.2.2.2.2.1.1 r hr y w h
  · obtain ⟨w, hw, hle⟩ := hS.1.2.2.2.2.1.2 r hr y b st v
      (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he (fun h => by cases h))
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h'
    · subst r y w; exact ⟨w', R3, Int.le_trans hle hwb⟩
    · exact ⟨w, h', hle⟩

theorem ctx_own : Inv.ballotOwner S' := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hS.1.2.2.2.2.2.1
  have hold := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r y b he => ?_, fun r y b v he => ?_, fun r y b v he => ?_, fun r to m hm' => ?_,
    fun r to m hm' => ?_, fun r to m hm' => ?_⟩
  · have h := hold r _ he (fun h => by cases h)
    refine ⟨(o1 r y b h).1, ?_⟩
    rw [hH.count_eq (fun _ => ctx_notE S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ (fun h => by cases h) rfl)]
    exact (o1 r y b h).2
  · exact hH.evBefore_old (o2 r y b v (hold r _ he (fun h => by cases h)))
  · exact hH.ev_old (o3 r y b v (hold r _ he (fun h => by cases h)))
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r to _ hm' with h | ⟨-, -, h⟩
    · obtain ⟨c1, c2⟩ := o4 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r to _ hm' with h | ⟨-, -, h⟩
    · obtain ⟨c1, c2⟩ := o5 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r to _ hm' with h | ⟨-, -, h⟩
    · obtain ⟨c1, c2⟩ := o6 r to m h; exact ⟨c1, hH.ev_old c2⟩
    · cases h

theorem ctx_op : Inv.oneProposal S' := by
  obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.1
  have hold := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r r' y b v v' he he' => ?_, fun r r' y b v v' he he' => ?_,
    fun r r' y b v v' he he' => ?_⟩
  · have h := hold r _ he (fun h => by cases h)
    have h' := hold r' _ he' (fun h => by cases h)
    obtain ⟨c1, c2, c3⟩ := p1 r r' y b v v' h h'
    refine ⟨c1, c2, ?_⟩
    rw [hH.count_eq (fun _ => ctx_notE S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ (fun h => by cases h) rfl)]; exact c3
  · exact p2 r r' y b v v' (hold r _ he (fun h => by cases h)) (hold r' _ he' (fun h => by cases h))
  · exact p3 r r' y b v v' (hold r _ he (fun h => by cases h)) (hold r' _ he' (fun h => by cases h))

theorem ctx_vf : Inv.votesFollowProposals S' := by
  obtain ⟨v1, v2⟩ := hS.1.2.2.2.2.2.2.2.1
  refine ⟨fun r y b st v he hst => ?_, fun r y b v he => ?_⟩
  · obtain ⟨l, v0, h1, h2⟩ := v1 r y b st v (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he (fun h => by cases h)) hst
    exact ⟨l, v0, hH.ev_old h1, h2⟩
  · obtain ⟨l, h1⟩ := v2 r y b v (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he (fun h => by cases h))
    exact ⟨l, hH.ev_old h1⟩

theorem ctx_cv : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
  intro y v
  constructor
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ h (fun h => by cases h)⟩
    · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to _ hm' with h | ⟨-, -, h⟩
      · exact Or.inr ⟨fr', to, m, h, hy, rfl⟩
      · cases h
  · rintro (⟨r, b, h⟩ | ⟨fr', to, m, hm', hy, rfl⟩)
    · exact Or.inl ⟨r, b, hH.ev_old h⟩
    · exact Or.inr ⟨fr', to, m, hH.msgs_old hm', hy, rfl⟩

/-- A report after the step is old, or the new one. -/
theorem ctx_prep : ∀ r m e, S'.prepReport r m e → (S.prepReport r m e ∧
      (r = i → e ∉ [Event.sent fr (.prepareReply rp)])) ∨
    (r = i ∧ m = rp ∧ e = .sent fr (.prepareReply rp)) := by
  rintro r m e ⟨he, ⟨to, hm', rfl⟩ | rfl⟩
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r to _ hm' with h | ⟨hr, hto, hmr⟩
    · by_cases hc : r = i ∧ Event.sent to (.prepareReply m) = .sent fr (.prepareReply rp)
      · obtain ⟨hr, hc⟩ := hc
        simp only [Event.sent.injEq, Msg.prepareReply.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Or.inr ⟨hr, rfl, rfl⟩
      · refine Or.inl ⟨⟨?_, Or.inl ⟨to, h, rfl⟩⟩, fun hr he' => hc ⟨hr, by simpa using he'⟩⟩
        rcases ctx_ev S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he with h1 | ⟨hr, h1⟩
        · exact h1
        · exact absurd ⟨hr, h1⟩ hc
    · simp only [Msg.prepareReply.injEq] at hmr; subst hmr hto
      exact Or.inr ⟨hr, rfl, rfl⟩
  · exact Or.inl ⟨⟨ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he (fun h => by cases h), Or.inr rfl⟩,
      fun _ => ctx_notE S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ (fun h => by cases h) rfl⟩

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

/-- No vote is new. -/
theorem ctx_vote_old : ∀ r y b st v, S'.ev r (.vote y b st v) → S.ev r (.vote y b st v) :=
  fun r y b st v h => ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ h (fun h => by cases h)

/-- The old votes of `i` for `x`: none if NONE, else at most `vbal`, one of them `w0`'s vote. -/
theorem ctx_votes0 : (w0.status = stNONE → ∀ b st v, ¬ S.ev i (.vote x b st v)) ∧
    (∀ b st v, S.ev i (.vote x b st v) → zz b ≤ zz w0.vbal) ∧
    ((isPA w0.status ∨ w0.status = stACCEPTED) → S.ev i (.vote x w0.vbal w0.status (instVal w0))) ∧
    (∀ b u, S.ev i (.vote x b stACCEPTED u) → zz w0.vbal ≤ zz b →
      w0.status = stACCEPTED ∨ isCommitted w0.status) ∧
    (isCommitted w0.status → S.committedVal x (instVal w0)) ∧
    (w0.status = stNONE → zz w0.vbal = -1) := by
  rcases hro with h | ⟨h, rfl⟩
  · exact ⟨fun hs => (hS.2.noneRec i hi x w0 h hs).2, hS.2.votesLe i hi x w0 h,
      hS.2.recVote i hi x w0 h, hS.2.accKeep i hi x w0 h,
      fun hc => (hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 i hi x w0 h hc).2,
      fun hs => (hS.2.noneRec i hi x w0 h hs).1⟩
  · have hnv : ∀ b st v, ¬ S.ev i (.vote x b st v) := by
      intro b st v hv
      obtain ⟨w, hw, -⟩ := hS.1.2.2.2.2.1.2 i hi x b st v hv
      rw [h] at hw; cases hw
    refine ⟨fun _ => hnv, fun b st v hv => absurd hv (hnv b st v), fun hs => ?_,
      fun b u hv => absurd hv (hnv b _ u), fun hc => ?_, fun _ => by simp [newInstanceDefault]⟩
    · simp [newInstanceDefault, isPA, stNONE, stPREACCEPTED, stPREACCEPTED_EQ, stACCEPTED] at hs
    · exact absurd hc (by simp [newInstanceDefault]; exact none_not_comm)

theorem ctx_rr : Inv.repliesReportVotes S' := by
  obtain ⟨q1, q2, q3⟩ := hS.1.2.2.2.2.2.2.2.2.1
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hwb, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨ha, hrx, hrb, hrv, hrs, hval, -⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := ctx_votes0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r m e hp => ?_, fun a r m hm' => ?_, fun a r m hm' => ?_⟩
  · rcases ctx_prep S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r m e hp with ⟨hp0, hne⟩ | ⟨hr, hmr, her⟩
    · obtain ⟨c1, c2, c3, c4, c5⟩ := q1 r m e hp0
      refine ⟨c1, fun hs => hH.evBefore_old (c2 hs), fun hs => (hcv _ _).mpr (c3 hs),
        fun hs b st v hb => c4 hs b st v (hH.evBefore_back hb hp0.1 hne),
        fun b st v hb => c5 b st v (hH.evBefore_back hb (hvo _ _ _ _ _ (by
          obtain ⟨pp, pp', -, -, h⟩ := hb; exact List.mem_of_getElem? h)) (fun _ h => by
            simp only [List.mem_singleton] at h; cases h))⟩
    · subst r m e
      rw [hrx]
      refine ⟨ha, fun hs => ?_, fun hs => ?_, fun hs b st v hb => ?_, fun b st v hb => ?_⟩
      · rw [hrv, hrs, hval]
        exact (hH.evBefore_iff _ _ _ _).mpr (Or.inr (Or.inl ⟨n3 (hrs ▸ hs), rfl, by simp⟩))
      · rw [hval]; exact (hcv _ _).mpr (n5 (hrs ▸ hs))
      · obtain ⟨pp, pp', -, h, -⟩ := hb
        exact n1 (hrs ▸ hs) b st v (hvo _ _ _ _ _ (List.mem_of_getElem? h))
      · -- the new report's event: a vote after it is after an old identical send
        rcases (hH.evBefore_iff _ _ _ _).mp hb with h | ⟨-, -, h⟩ | ⟨-, -, pp, pp', -, -, h⟩
        · rw [← hrx] at h
          have hev0 : S.ev i (.sent fr (.prepareReply rp)) := by
            obtain ⟨pp, pp', -, h1, -⟩ := h; exact List.mem_of_getElem? h1
          exact (hS.2.sentPR i fr rp hev0).2.1 b st v h
        · simp only [List.mem_singleton] at h; cases h
        · have := List.mem_of_getElem? h; simp only [List.mem_singleton] at this; cases this
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn a r _ hm' with h | ⟨-, -, h⟩
    · obtain ⟨c1, c2, c3, c4⟩ := q2 a r m h
      refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨v, hv⟩ := c1; exact ⟨v, hH.ev_old hv⟩
      · obtain ⟨d1, v, d2, d3⟩ := c2 hs; exact ⟨d1, v, hH.ev_old d2, d3⟩
      · obtain ⟨v, d2, d3⟩ := c3 hs; exact ⟨v, hH.ev_old d2, d3⟩
      · obtain ⟨v, d2, d3⟩ := c4 hs; exact ⟨v, (hcv _ _).mpr d2, d3⟩
    · cases h
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn a r _ hm' with h | ⟨-, -, h⟩
    · rcases q3 a r m h with ⟨v, hv⟩ | ⟨⟨b, v, hv⟩, c2⟩
      · exact Or.inl ⟨v, hH.evBefore_old hv⟩
      · refine Or.inr ⟨⟨b, v, hH.evBefore_old hv⟩, fun m' e' hp hy hb => ?_⟩
        have hsent : S.ev a (.sent r (.acceptReply m)) := by
          obtain ⟨pp, pp', -, -, h1⟩ := hv; exact List.mem_of_getElem? h1
        rcases ctx_prep S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn a m' e' hp with ⟨hp0, hne⟩ | ⟨ha', hmr, her⟩
        · exact c2 m' e' hp0 hy (hH.evBefore_back hb hsent (fun _ h => by
            simp only [List.mem_singleton] at h; cases h))
        · subst a m' e'
          rcases (hH.evBefore_iff _ _ _ _).mp hb with h1 | ⟨-, -, h1⟩ | ⟨-, -, pp, pp', -, -, h1⟩
          · have hy' : (⟨toN m.replica, toN m.inst⟩ : InstId) = ⟨toN rp.replica, toN rp.inst⟩ := by
              simp only [Msg.instOf, Option.some.injEq] at hy; exact hy.symm
            have hev0 : S.ev i (.sent fr (.prepareReply rp)) := by
              obtain ⟨pp, pp', -, h2, -⟩ := h1; exact List.mem_of_getElem? h2
            exact (hS.2.sentPR i fr rp hev0).2.2 r m h1 hy'
          · simp only [List.mem_singleton] at h1; cases h1
          · have := List.mem_of_getElem? h1; simp only [List.mem_singleton] at this; cases this
    · cases h

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

theorem ctx_hi : Inv.prepReplyHighest S' := by
  obtain ⟨-, hrx, -, hrv, -⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, n2, -⟩ := ctx_votes0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro r m e hp b st v hb
  have hvo : S.ev r (.vote ⟨toN m.replica, toN m.inst⟩ b st v) := by
    obtain ⟨pp, pp', -, h, -⟩ := hb
    exact ctx_vote_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ _ _ _ _ (List.mem_of_getElem? h)
  rcases ctx_prep S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r m e hp with ⟨hp0, hne⟩ | ⟨hr, hmr, her⟩
  · exact hS.1.2.2.2.2.2.2.2.2.2.1 r m e hp0 b st v (hH.evBefore_back hb hp0.1 hne)
  · subst r m e; rw [hrx] at hvo; rw [hrv]; exact n2 b st v hvo

/-- The record at `(i, x)` after the step: the old one (up to `bal`) or a fresh default. -/
theorem ctx_rel : ∀ r y w, (S'.rep r).inst y = some w →
    (S.rep r).inst y = some w ∨ (r = i ∧ y = x ∧ (S.rep i).inst x = some w0 ∧ w = w') ∨
    (r = i ∧ y = x ∧ (S.rep i).inst x = none ∧ w = prepRec (newInstanceDefault x) p) := by
  obtain ⟨R1, -⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro r y w hw
  rcases R1 r y w hw with ⟨h1, h2, h3⟩ | h
  · subst h3
    rcases hro with h | ⟨h, h0⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h, rfl⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, h, by rw [hw', h0]⟩)
  · exact Or.inl h

theorem ctx_lb : Inv.lbInv S' := by
  obtain ⟨-, -, hmk, hxq, -, -, -, -, hfi⟩ := ctx_basic S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, hlbeq, -, -, -, hst, -, -, hbal, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hold := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro r hr y w lb hw hlb
  obtain ⟨w0', hw0', hrel⟩ : ∃ w0', (S.rep r).inst y = some w0' ∧
      (w0' = w ∨ (r = i ∧ y = x ∧ w0' = w0 ∧ w = w')) := by
    rcases ctx_rel S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y w hw with h | ⟨h1, h2, h3, h4⟩ | ⟨-, -, -, h4⟩
    · exact ⟨w, h, Or.inl rfl⟩
    · exact ⟨w0, by rw [h1, h2]; exact h3, Or.inr ⟨h1, h2, rfl, h4⟩⟩
    · rw [h4, (prepRec_fields _ p).2.2.2.2.2.1] at hlb; simp [newInstanceDefault] at hlb
  have hlb0 : w0'.lb = some lb := by
    rcases hrel with rfl | ⟨-, -, rfl, rfl⟩
    · exact hlb
    · rw [← hlbeq]; exact hlb
  obtain ⟨a1, a2, a3, a4, a5, ⟨Q, q1, q2, q3⟩, ⟨Q', q1', q2', q3'⟩, a8, a9⟩ :=
    hS.1.2.2.2.2.2.2.2.2.2.2.1 r hr y w0' lb hw0' hlb0
  refine ⟨hH.ev_old a1, a2, a3, fun b v hv => a4 b v ?_, fun c1 c2 => ?_, ⟨Q, q1, q2, ?_⟩,
    ⟨Q', q1', q2', ?_⟩, fun c1 c2 c3 c4 => ?_, fun hp => ?_⟩
  · rcases hv with hv | hv
    · exact Or.inl (hold r _ hv (fun h => by cases h))
    · exact Or.inr (hold r _ hv (fun h => by cases h))
  · obtain ⟨d1, d2, v, d3, d4⟩ := a5 c1 c2; exact ⟨d1, d2, v, hH.ev_old d3, d4⟩
  · intro a m' h; obtain ⟨b1, b2, b3, b4⟩ := q3 a m' h; exact ⟨b1, b2, hH.deliveredMsg_old b3, b4⟩
  · intro a h; obtain ⟨b1, b2, m', b3, b4⟩ := q3' a h
    exact ⟨b1, b2, m', hH.deliveredMsg_old b3, b4⟩
  · rcases hrel with rfl | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
    · rcases hbal with hb | hb
      · rw [hst] at c2; rw [hb] at c3
        obtain ⟨d1, d2⟩ := a8 c1 c2 c3 c4; exact ⟨hH.ev_old d1, hH.ev_old d2⟩
      · exfalso
        rw [hb] at c3; rw [← c3] at a1
        exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk a1)
  · obtain ⟨c1, c2⟩ := a9 hp
    refine ⟨c1, fun e he => ?_⟩
    obtain ⟨d1, d2, d3⟩ := c2 e he
    refine ⟨d1, d2, ?_⟩
    rcases d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, hH.deliveredMsg_old e2⟩
    · exact Or.inr ⟨e1, hH.ev_old e2⟩

theorem ctx_agr : Inv.agreement S' := by
  obtain ⟨-, -, -, -, hcm, -, hst, hseq, hdeps, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun y v v' h h' => hS.1.2.2.2.2.2.2.2.2.2.2.2.1.1 y v v' ((hcv _ _).mp h)
    ((hcv _ _).mp h'), fun r hr y w hw hc => ?_⟩
  rcases ctx_rel S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y w hw with h | ⟨-, hy, h, rfl⟩ | ⟨-, -, -, rfl⟩
  · obtain ⟨c1, c2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 r hr y w h hc
    exact ⟨c1, (hcv _ _).mpr c2⟩
  · rw [hst] at hc
    subst hy
    obtain ⟨c1, c2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.1.2 i hi y w0 h hc
    refine ⟨hcm ▸ c1, (hcv _ _).mpr ?_⟩
    simp only [instVal, hcm, hseq, hdeps]; exact c2
  · exfalso; rw [(prepRec_fields _ p).2.2.1] at hc; exact none_not_comm hc

theorem ctx_dc : Inv.decidedChosen S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro y v hv
  rcases hS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) with ⟨b, Q, h1, h2, h3⟩ | ⟨⟨Q, h1, h2, h3⟩, hf⟩
  · exact Or.inl ⟨b, Q, h1, h2, fun r hr => ⟨(h3 r hr).1, hH.ev_old (h3 r hr).2⟩⟩
  · refine Or.inr ⟨⟨Q, h1, h2, fun r hr => ?_⟩, hH.ev_old hf⟩
    obtain ⟨c1, c2, st, c3, c4⟩ := h3 r hr
    exact ⟨c1, c2, st, c3, hH.ev_old c4⟩

theorem ctx_dcv : Inv.depsCover S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro y z vy vz hyz hy hz hi'
  exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y z vy vz hyz ((hcv _ _).mp hy) ((hcv _ _).mp hz) hi'

theorem ctx_wit : Inv.witnesses S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro y v hv hn'
  obtain ⟨W, w1, w2, w3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y v ((hcv _ _).mp hv) hn'
  exact ⟨W, w1, w2, fun r hr => by
    obtain ⟨c1, d, c2, c3⟩ := w3 r hr; exact ⟨c1, d, hH.ev_old c2, c3⟩⟩

theorem ctx_ac : Inv.attrsCover S' := by
  intro r e y cy z cz d hrec hyz hb hint
  have h2 := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ (by obtain ⟨p1, p2, -, -, h⟩ := hb; exact List.mem_of_getElem? h)
    (fun h => by cases h)
  exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r e y cy z cz d hrec hyz
    (hH.evBefore_back hb h2 (fun _ => ctx_notE S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ (fun h => by cases h) rfl)) hint

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

/-- The views the executor reads are unchanged. -/
theorem ctx_view : ∀ r y, ((S'.rep r).inst y).map (fun w => (w.status, w.cmds, w.deps)) =
    ((S.rep r).inst y).map (fun w => (w.status, w.cmds, w.deps)) ∨
    ((S.rep r).inst y = none ∧ ((S'.rep r).inst y).map (fun w => (w.status, w.cmds, w.deps)) =
      some (stNONE, none, [])) := by
  obtain ⟨-, -, -, -, hcm, -, hst, -, hdeps, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  intro r y
  by_cases hc : r = i ∧ y = x
  · obtain ⟨rfl, rfl⟩ := hc
    rw [R3]
    rcases hro with h | ⟨h, h0⟩
    · left; rw [h]; simp [hcm, hst, hdeps]
    · right; refine ⟨h, ?_⟩; simp [hcm, hst, hdeps, h0, newInstanceDefault]
  · left; rw [R4 r y (by
      by_cases h1 : r = i
      · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
      · exact Or.inl h1)]

theorem ctx_executed : ∀ r y, (S'.rep r).executed y ↔ (S.rep r).executed y := by
  intro r y
  have hv := ctx_view S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y
  simp only [RState.executed]
  cases h1 : (S'.rep r).inst y <;> cases h2 : (S.rep r).inst y <;> rw [h1, h2] at hv <;>
    simp_all [stNONE, stEXECUTED]

theorem ctx_depEdge : ∀ r y z, (S'.rep r).depEdge y z ↔ (S.rep r).depEdge y z := by
  intro r y z
  have hv := ctx_view S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y
  constructor
  · rintro ⟨w, hw, hq, hz⟩
    rcases hv with hv | ⟨-, hv⟩
    · rw [hw] at hv
      cases h2 : (S.rep r).inst y with
      | none => rw [h2] at hv; cases hv
      | some w2 =>
        rw [h2] at hv; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
        exact ⟨w2, h2, hq, by rw [← hv.2.2]; exact hz⟩
    · rw [hw] at hv
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
      rw [hv.2.2] at hz
      have : zz (([] : List w32).getD z.q (W32 (-1))) = -1 := by simp
      simp only [zz] at this hz; omega
  · rintro ⟨w, hw, hq, hz⟩
    rcases hv with hv | ⟨hnone, -⟩
    · rw [hw] at hv
      cases h1 : (S'.rep r).inst y with
      | none => rw [h1] at hv; cases hv
      | some w1 =>
        rw [h1] at hv; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
        exact ⟨w1, h1, hq, by rw [hv.2.2]; exact hz⟩
    · rw [hw] at hnone; cases hnone

theorem ctx_cmds : ∀ r y, ((S'.rep r).inst y).bind (·.cmds) = ((S.rep r).inst y).bind (·.cmds) := by
  intro r y
  have hv := ctx_view S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y
  cases h1 : (S'.rep r).inst y <;> cases h2 : (S.rep r).inst y <;> rw [h1, h2] at hv <;>
    simp_all

theorem ctx_exec : Inv.execClosed S' ∧ Inv.execCursor S' ∧ Inv.execOrder S' ∧ Inv.execPrefix S' := by
  have hex := ctx_executed S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hde := ctx_depEdge S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, -, -, hcm, -, hst, hseq, hdeps, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
    refine ⟨by rw [hH.execLog]; exact e1, fun y => by rw [hH.execLog, hex]; exact e2 y,
      fun y w hw hs => ?_⟩
    rcases ctx_rel S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y w hw with h | ⟨hr', hy, h, hw2⟩ | ⟨-, -, -, hw2⟩
    · obtain ⟨c1, c2⟩ := e3 y w h hs
      exact ⟨(hcv _ _).mpr c1, fun z hz => by
        rw [hex, hH.execCur]; exact c2 z ((hde r y z).mp (by
          obtain ⟨w2, hw2, h3⟩ := hz; exact ⟨w2, hw2, h3⟩))⟩
    · subst hy hw2 hr'; rw [hst] at hs
      obtain ⟨c1, c2⟩ := e3 _ w0 h hs
      refine ⟨(hcv _ _).mpr (by simp only [instVal, hcm, hseq, hdeps]; exact c1), fun z hz => ?_⟩
      rw [hex, hH.execCur]; exact c2 z ((hde _ _ z).mp hz)
    · exfalso; rw [hw2, (prepRec_fields _ p).2.2.1] at hs
      simp [newInstanceDefault, stNONE, stEXECUTED] at hs
  · by_cases hri : r = i
    · subst r
      have hc0 : S.execCur i = [] := hidle.2
      have hi0 := (hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hr).1 hc0
      rw [hH.execCur, hH.execIdx]
      exact ⟨fun _ => hi0, fun h => absurd hc0 h⟩
    · have := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr
      rw [hH.rep_other hri, hH.execCur, hH.execIdx]; exact this
  · have hdE : S'.dEdge = S.dEdge := by funext y z; simp only [Sys.dEdge, hcv]
    have hsO : S'.sccOrd = S.sccOrd := by funext y z; simp only [Sys.sccOrd, hcv]
    intro r hr i0 j y z hij hy hz ht
    rw [hH.execLog] at hy hz; rw [hdE, hsO] at *
    exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r hr i0 j y z hij hy hz ht
  · have hlx : ∀ r k, S'.lexec r k = S.lexec r k := by
      intro r k
      have hso : Sys.slotsOn (S'.rep r) = Sys.slotsOn (S.rep r) := by
        funext xs k'; simp only [Sys.slotsOn, ctx_cmds S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn]
      simp only [Sys.lexec, Sys.curSlots, hH.execCur, hH.execLog, hH.execIdx, hso]
    obtain ⟨p1, p2, p3⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post h => ?_⟩
    · rw [hlx, hH.gexec]; exact p1 r hr k
    · rw [hlx, (ctx_fields S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r).2.2.2.2.1]; exact p2 r hr k
    · rw [hlx] at h; rw [hH.gexec]; exact p3 r hr k pre e post h

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

theorem ctx_slots : Inv.slots S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨s1, s2⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun y v hv => ?_, fun y ps h => ?_⟩
  · rw [hH.owner]; exact s1 y v ((hcv _ _).mp hv)
  · rw [hH.owner] at h; rw [hH.ops]; exact s2 y ps h

theorem ctx_co : Inv.clientOps S' := by
  have hcv := ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hso : S'.slotOp = S.slotOp := by funext sl; simp only [Sys.slotOp, hH.owner]
  have := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Inv.clientOps, hso, hH.gexec, hH.fired, hH.ops, hcv] at this ⊢
  exact this

theorem ctx_cm : Inv.commitMsgs S' := by
  intro fr' to m hm'
  rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to _ hm' with h | ⟨-, -, h⟩
  · obtain ⟨r, b, h1⟩ := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 fr' to m h
    exact ⟨r, b, hH.ev_old h1⟩
  · cases h

theorem ctx_pk : Inv.pendingKind S' := by
  intro r b hb
  rw [hH.pending] at hb
  by_cases hri : r = i
  · subst r; simp at hb
  · rw [upd_other _ _ _ _ hri] at hb
    exact hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 r b hb

theorem ctx_mono : SafeMono S S' := by
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hwb, -, -, -, -, -, hst, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r y w hw => ?_, fun r e he => hH.ev_old he,
    fun r y b st v he => Or.inl (ctx_vote_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r y b st v he),
    fun y v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ _ he (fun h => by cases h)),
    fun a y m hm' _ _ => ?_⟩
  · rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w
      exact ⟨w', R3, hwb, fun hs => Or.inl (by rw [hst]; exact hs)⟩
    · exact ⟨w, h, Int.le_refl _, fun hs => Or.inl hs⟩
  · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn y.q a _ hm' with h | ⟨-, -, h⟩
    · exact Or.inl h
    · cases h

theorem ctx_safe : Inv.safe S' :=
  safe_step (ctx_mono S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn) hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun r y b v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he (fun h => by cases h)))
    (fun r y b v he => Or.inl (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he (fun h => by cases h)))

theorem ctx_reports : Inv.reports S' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrepo⟩ :=
    hS.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hrepo
  have hmo := ctx_mono S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hP := ctx_prep S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, hrx, hrb, hrv, hrs, -, hrd, -⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hst0, hvb0, hd0, -⟩ := ctx_w0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := ctx_votes0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, -, R3, -⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hwb, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  refine ⟨fun r m e hp => ?_, fun r m e hp => ?_, fun r m e hp => ?_, fun r m e hp b u hb => ?_,
    fun r m e hr hp => ?_, fun r y b st st' v v' h1 h2 h3 h4 => c6 r y b st st' v v' h1 h2
      (hvo _ _ _ _ _ h3) (hvo _ _ _ _ _ h4), fun y v m e h1 h2 h3 => ?_,
    fun r y v h1 w => fastBlocked_mono hmo
      (c8 r y v (ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ h1 (fun h => by cases h)) w), fun r m e hp => ?_⟩
  · rcases hP r m e hp with ⟨hp0, -⟩ | ⟨-, rfl, -⟩
    · exact c1 r m e hp0
    · rw [hrs]; exact hst0
  · rcases hP r m e hp with ⟨hp0, -⟩ | ⟨-, rfl, -⟩
    · exact c2 r m e hp0
    · rw [hrs, hrv]; exact n6
  · rcases hP r m e hp with ⟨hp0, -⟩ | ⟨-, rfl, -⟩
    · exact c3 r m e hp0
    · rw [hrs, hrd]; intro h; exact (hd0 h).1
  · rcases hP r m e hp with ⟨hp0, hne⟩ | ⟨hr, hmr, her⟩
    · exact c4 r m e hp0 b u (hH.evBefore_back hb hp0.1 hne)
    · subst r m e
      rw [hrx] at hb; rw [hrv]; rw [hrs]
      intro hle
      obtain ⟨pp, pp', -, h, -⟩ := hb
      exact n4 b u (hvo _ _ _ _ _ (List.mem_of_getElem? h)) hle
  · rcases hP r m e hp with ⟨hp0, -⟩ | ⟨hr', hmr, -⟩
    · obtain ⟨w, hw, hle⟩ := c5 r m e hr hp0
      obtain ⟨w', hw', hle', -⟩ := hmo.bal r _ w hw
      exact ⟨w', hw', Int.le_trans hle hle'⟩
    · subst r m; rw [hrx, hrb]; exact ⟨w', R3, Int.le_refl _⟩
  · have h1' := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn _ _ h1 (fun h => by cases h)
    rcases hP _ m e h2 with ⟨hp0, -⟩ | ⟨hr, hmr, -⟩
    · exact c7 y v m e h1' hp0 h3
    · subst hmr; rw [hrs]
      obtain ⟨hq, b, hc⟩ := hS.2.fastCommitEv _ y v h1'
      rw [hrx] at h3; subst h3
      obtain ⟨w, hw, hcw⟩ := hS.2.commitRec _ _ b v (hr ▸ hi) hc
      rw [hr] at hw
      rcases hro with h' | ⟨h', -⟩
      · rw [h'] at hw; cases hw; exact hcw
      · rw [h'] at hw; cases hw
  · rcases hP r m e hp with ⟨hp0, -⟩ | ⟨-, rfl, -⟩
    · exact c9 r m e hp0
    · rw [hrv, hrb]; exact Int.le_trans hvb0 hwb

end

/-- Under a handler step with no pending broadcast, what is sent or in an outbox after it was
sent or in an outbox before, or is a new direct send. -/
private theorem sob_hs {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {snd : Nat → List Msg} (hH : HS S S' i σ' E snd none) (hp : S.pending i = none)
    (fr to : Nat) (m : Msg) (h : m ∈ S'.sent fr to ++ S'.outbox fr to) :
    m ∈ S.sent fr to ++ S.outbox fr to ∨ (fr = i ∧ m ∈ snd to) := by
  have hI : S'.intended fr to = S.intended fr to := by
    unfold Sys.intended; rw [hH.pending]
    by_cases hf : fr = i
    · subst hf; simp [upd_same, hp]
    · simp [upd_other _ _ _ _ hf]
  have hm := hH.msgs fr to
  simp only [Sys.msgs, hI, hH.sent] at hm
  rw [hH.sent] at h
  by_cases hf : fr = i
  · subst hf
    have h0 : S.intended fr to = [] := by unfold Sys.intended; rw [hp]
    simp only [h0, if_true, intendedOf, List.append_nil] at hm
    rw [hm] at h
    simp only [List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨by trivial, h⟩
  · simp only [hf, if_false, List.append_nil] at hm
    rw [List.append_cancel_right hm] at h
    exact Or.inl h

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

/-- `InvPM` after `handlePrepare`. -/
theorem ctx_pm : InvPM S' := by
  obtain ⟨-, -, hmk, hxq, -, -, -, -, hfi⟩ := ctx_basic S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨R1, R2, R3, -⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hwb, hpb, hlbeq, -⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, hrx, -⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hP := hS.2.pm
  have hold := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hmono : ∀ r e, S.ev r e → S'.ev r e := fun r e h => hH.ev_old h
  have hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) :=
    fun r y b v h => hold r _ h (fun h => by cases h)
  have hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) :=
    fun r y b v h => hold r _ h (fun h => by cases h)
  have hcm : ∀ r y c u, S'.ev r (.commit y c u) → S.ev r (.commit y c u) :=
    fun r y c u h => hold r _ h (fun h => by cases h)
  have hsent : ∀ fr' to m, m ∈ S.sent fr' to → m ∈ S'.sent fr' to :=
    fun _ _ _ h => by rw [hH.sent]; exact h
  have hcv : ∀ y u, S.committedVal y u → S'.committedVal y u :=
    fun y u h => (ctx_cv S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn y u).mpr h
  have hmsgO : ∀ fr' to m, m ∈ S'.msgs fr' to → (∀ q, m ≠ .prepareReply q) → m ∈ S.msgs fr' to := by
    intro fr' to m h hne
    rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to m h with
      h | ⟨-, -, h⟩
    · exact h
    · exact absurd h (hne rp)
  have hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w2, (S'.rep r).inst y = some w2 ∧ zz w.bal ≤ zz w2.bal := by
    intro r y w h
    rcases R2 r y w h with ⟨rfl, rfl, rfl⟩ | h'
    · exact ⟨w', R3, hwb⟩
    · exact ⟨w, h', Int.le_refl _⟩
  have hlb1 : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      ∃ w1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb2 := by
    intro r y w2 lb2 h hl
    rcases R1 r y w2 h with ⟨rfl, rfl, rfl⟩ | h'
    · rw [hlbeq] at hl
      rcases hro with h0 | ⟨-, h0⟩
      · exact ⟨w0, h0, hl⟩
      · subst h0; simp [newInstanceDefault] at hl
    · exact ⟨w2, h', hl⟩
  have hlb : ∀ r y w2 lb2, (S'.rep r).inst y = some w2 → w2.lb = some lb2 →
      ∃ w1 lb1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb1 ∧ PMProof.LbPM lb1 lb2 := by
    intro r y w2 lb2 h hl
    obtain ⟨w1, h1, h2⟩ := hlb1 r y w2 lb2 h hl
    exact ⟨w1, lb2, h1, h2, PMProof.LbPM.refl _⟩
  have hpend : ∀ r b, S'.pending r = some b → S.pending r = some b := by
    intro r b h
    rw [hH.pending] at h
    by_cases hr : r = i
    · subst hr; simp at h
    · rw [upd_other _ _ _ _ hr] at h; exact h
  exact {
    arOk := PMProof.arOk_frame hP (fun a r m h => hmsgO _ _ _ h (fun _ h => by cases h)) hacc
      (fun q y b v h => Or.inl (hvo _ _ _ _ _ h)) hmono hcv hbal
    commitProp := PMProof.commitProp_frame hP hcm hmono
    commitMsgProp := PMProof.commitMsgProp_frame hP
      (fun fr' to m h => hmsgO _ _ _ h (fun _ h => by cases h)) hmono
    lbProp := PMProof.lbProp_frame hP hlb hacc hmono
    parCom := PMProof.parCom_frame hP (fun a r m h => hmsgO _ _ _ h (fun _ h => by cases h)) hmono
    parSt := PMProof.parSt_frame hP (fun a r m h => hmsgO _ _ _ h (fun _ h => by cases h)) hsent
    paFresh := PMProof.paFresh_frame hP hlb hph
    paCmds := PMProof.paCmds_frame hP hlb hph
    paSent := PMProof.ps_frame hP
      (fun y w2 lb2 h hl => by
        obtain ⟨w1, h1, h2⟩ := hlb1 _ y w2 lb2 h hl
        exact ⟨w1, lb2, h1, h2, rfl, rfl⟩)
      (fun r b h _ => hpend r b h)
      (fun y a h => by
        obtain ⟨m, hm1, hm2⟩ := List.any_eq_true.mp h
        rcases sob_hs hH hidle.1 _ _ m hm1 with h' | ⟨-, h'⟩
        · exact List.any_eq_true.mpr ⟨m, h', hm2⟩
        · split at h'
          · simp only [List.mem_singleton] at h'; subst h'; simp [Msg.isPAat] at hm2
          · cases h')
    pendPA := fun r b hb y c hc => hP.pendPA r b (hpend r b hb) y c hc
    paVoteMsg := PMProof.paVoteMsg_frame hP hvo hsent
    parNoPA := PMProof.parNoPA_frame hP (fun a r m h => hmsgO _ _ _ h (fun _ h => by cases h)) hvo
    aeF := PMProof.aeF_frame hP hlb hsent
    repLead := by
      intro r m e hp hr
      rcases ctx_prep S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r m e hp with
        ⟨hp0, -⟩ | ⟨rfl, hmr, rfl⟩
      · obtain ⟨w, hw, hlt⟩ := hP.repLead r m e hp0 hr
        obtain ⟨w2, hw2, hle⟩ := hbal r _ w hw
        exact ⟨w2, hw2, Int.lt_of_lt_of_le hlt hle⟩
      · rw [hmr] at hr ⊢; rw [hrx]
        refine ⟨w', R3, ?_⟩
        have hq : toN rp.replica = x.q := by rw [← hrx]
        rw [hq] at hr
        rw [zz_initBal x hxq]
        rcases (hS.1.2.2.2.2.2.1.1 fr x p.ballot hmk).1 with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact absurd (h2.trans hr.symm) hfi
        · simp only [nR] at h1 hxq ⊢; omega
    paGe := PMProof.paGe_frame hP hvo hph
    phAttrs := PMProof.phAttrs_frame hP hph hmono
    accWit := PMProof.accWit_frame hP hacc hmono hcv
    accVote := PMProof.accVote_frame hP hacc hmono
    cmdSafe := CmdSafeProof.cmdSafe_frame hP (ctx_mono S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn) hph
    accSup := CmdSafeProof.accSup_frame hP hmono hacc }

end

section
variable (S S' : Sys) (fr i n : Nat) (p : Prepare) (x : InstId) (w0 w' : InstRec)
  (rp : PrepareReply)
  (hS : Inv S) (hi : i < nR) (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered)
  (hm : (S.sent fr i)[n]? = some (.prepare p)) (hx : x = ⟨toN p.replica, toN p.inst⟩)
  (hH : HS S S' i ((bumpRecvBallot (S.rep i) p.ballot).setInst x w') [.sent fr (.prepareReply rp)]
    (fun to => if to = fr then [.prepareReply rp] else []) none)
  (hro : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x))
  (hw' : w' = prepRec w0 p) (hrp : rp = prepRep (S.rep i) w' p)
  (hdn : (fr, i, n) ∈ S'.delivered)
include hS hi hfr hidle hn hm hx hH hro hw' hrp hdn

theorem ctx_aux (hchan : S'.proposeChan = S.proposeChan) : InvAux S' := by
  obtain ⟨hpm, hldr, hmk, hxq, hxi, hpi0, hpi, hb0, hfi⟩ := ctx_basic S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨R1, R2, R3, R4⟩ := ctx_rec S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hwb, -, hlbeq, -, hcm, hvb, hst, -, -, hbal0, hival⟩ := ctx_w S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨hst0, hvb0, -, -⟩ := ctx_w0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := ctx_votes0 S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  obtain ⟨-, hrx, hrb, -⟩ := ctx_rp S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hA := hS.2
  have hold := ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hvo := ctx_vote_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have F := ctx_fields S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  have hcrt : ∀ r q, (S'.rep r).crtInstance q = (S.rep r).crtInstance q := by
    intro r q; rw [(F r).2.2.2.2.2]
  have hoth : ∀ r y w, (S'.rep r).inst y = some w → ¬ (r = i ∧ y = x) →
      (S.rep r).inst y = some w := by
    intro r y w hw hc
    rcases R1 r y w hw with ⟨h1, h2, -⟩ | h
    · exact absurd ⟨h1, h2⟩ hc
    · exact h
  -- the record at `(i, x)` is `w0`'s fields with a higher `bal`
  have hX : (S.rep i).inst x = some w0 ∨ ((S.rep i).inst x = none ∧ w0 = newInstanceDefault x) :=
    hro
  have hnoP : ∀ (P : Msg → Bool), P (.prepareReply rp) = false →
      ∀ to m, m ∈ (if to = fr then [Msg.prepareReply rp] else []) ++ intendedOf none to →
        P m = false := by
    intro P hP to m hm'
    simp only [intendedOf, List.append_nil] at hm'
    split at hm'
    · simp only [List.mem_singleton] at hm'; subst hm'; exact hP
    · cases hm'
  have hcnt0 : ∀ fr' to (P : Msg → Bool), P (.prepareReply rp) = false →
      S'.cnt fr' to P = S.cnt fr' to P := by
    intro fr' to P hP
    rw [hH.cnt_eq]
    split
    · rw [List.filter_eq_nil_iff.mpr (fun m hm' => by simp [hnoP P hP to m hm'])]; rfl
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr y w hw
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst]; exact hst0
    · exact hA.stRange r hr y w (hoth r y w hw hc)
  · intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst] at hs; rw [hcm]
      rcases hX with h | ⟨-, h⟩
      · exact hA.cmdsSome r hr y w0 h hs
      · rw [h] at hs; exact absurd rfl hs
    · exact hA.cmdsSome r hr y w (hoth r y w hw hc) hs
  · intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst] at hs; rw [hvb]
      exact ⟨n6 hs, fun b st v hv => n1 hs b st v (hvo _ _ _ _ _ hv)⟩
    · obtain ⟨c1, c2⟩ := hA.noneRec r hr y w (hoth r y w hw hc) hs
      exact ⟨c1, fun b st v hv => c2 b st v (hvo _ _ _ _ _ hv)⟩
  · intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst] at hs; rw [hvb]
      rcases hX with h | ⟨-, h⟩
      · exact hA.vbalNonneg r hr y w0 h hs
      · rw [h] at hs; exact absurd rfl hs
    · exact hA.vbalNonneg r hr y w (hoth r y w hw hc) hs
  · intro r hr y w hw b st v hv
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hvb]
      exact n2 b st v (hvo _ _ _ _ _ hv)
    · exact hA.votesLe r hr y w (hoth r y w hw hc) b st v (hvo _ _ _ _ _ hv)
  · intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst] at hs ⊢; rw [hvb, hival]
      exact hH.ev_old (n3 hs)
    · exact hH.ev_old (hA.recVote r hr y w (hoth r y w hw hc) hs)
  · intro r hr y w hw b u hv hle
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst]; rw [hvb] at hle
      exact n4 b u (hvo _ _ _ _ _ hv) hle
    · exact hA.accKeep r hr y w (hoth r y w hw hc) b u (hvo _ _ _ _ _ hv) hle
  · intro r hr y w hw hs
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw; rw [hst] at hs
      rcases hX with h | ⟨-, h⟩
      · obtain ⟨b, v, h1, h2⟩ := hA.recCommit r hr y w0 h hs
        exact ⟨b, v, hH.ev_old h1, Int.le_trans h2 hwb⟩
      · rw [h] at hs; exact absurd hs none_not_comm
    · obtain ⟨b, v, h1, h2⟩ := hA.recCommit r hr y w (hoth r y w hw hc) hs
      exact ⟨b, v, hH.ev_old h1, h2⟩
  · intro r y b v hr he
    obtain ⟨w, hw, hs⟩ := hA.commitRec r y b v hr (hold r _ he (fun h => by cases h))
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact ⟨w', R3, by rw [hst]; exact hs⟩
    · exact ⟨w, h, hs⟩
  · intro r y v he
    obtain ⟨h1, b, h2⟩ := hA.fastCommitEv r y v (hold r _ he (fun h => by cases h))
    exact ⟨h1, b, hH.ev_old h2⟩
  · intro r y b hr he
    obtain ⟨w, lb, hw, hlb, hle⟩ := hA.makerLb r y b hr (hold r _ he (fun h => by cases h))
    rcases R2 r y w hw with ⟨h1, h2, h3⟩ | h
    · subst r y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb, hle⟩
    · exact ⟨w, lb, h, hlb, hle⟩
  · intro r hr y w lb hw hlb
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rw [hlbeq] at hlb
      rcases hX with h | ⟨-, h⟩
      · exact Int.le_trans (hA.lastLeBal r hr y w0 lb h hlb) hwb
      · rw [h] at hlb; simp [newInstanceDefault] at hlb
    · exact hA.lastLeBal r hr y w lb (hoth r y w hw hc) hlb
  · intro r hr; rw [(F r).2.1]; exact hA.peerOk r hr
  · intro r hr q hq; rw [hcrt, hcrt]; exact hA.crtOwn r hr q hq
  · intro r hr y w hw
    rw [hcrt]
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      exact hA.crtMsg fr r _ y hpm (by rw [hx]; rfl)
    · exact hA.crtRec r hr y w (hoth r y w hw hc)
  · intro fr' to m y hm' hy
    rw [hcrt]
    rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to m hm' with h | ⟨-, -, rfl⟩
    · exact hA.crtMsg fr' to m y h hy
    · simp only [Msg.instOf, Option.some.injEq] at hy
      rw [hrx] at hy; subst hy
      exact hA.crtMsg fr i _ x hpm (by rw [hx]; rfl)
  · intro r e y he hy
    rw [hcrt]
    rcases ctx_ev S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r e he with h | ⟨-, rfl⟩
    · exact hA.crtEv r e y h hy
    · simp [Event.instOf] at hy
  · intro q hq j hj
    rw [hcrt] at hj
    obtain ⟨w, lb, hw, hlb⟩ := hA.ownRow q hq j hj
    rcases R2 q _ w hw with ⟨h1, h2, h3⟩ | h
    · rw [h2, h1]; subst h3; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb⟩
    · exact ⟨w, lb, h, hlb⟩
  · intro r hr y w lb hw hlb hs v hv
    have hv' := hold r _ hv (fun h => by cases h)
    by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
      rw [hlbeq] at hlb
      rcases hX with h | ⟨-, h⟩
      · exact hA.paNoAcc r hr y w0 lb h hlb hs v hv'
      · rw [h] at hlb; simp [newInstanceDefault] at hlb
    · exact hA.paNoAcc r hr y w lb (hoth r y w hw hc) hlb hs v hv'
  · intro r hr y w lb hw hlb hs hp hc hb
    obtain ⟨v, hv⟩ := hp
    have hv' := hold r _ hv (fun h => by cases h)
    by_cases hcc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
      rw [hlbeq] at hlb; rw [hst] at hc ⊢; rw [hvb]
      rcases hX with h | ⟨-, h⟩
      · rcases hbal0 with hb' | hb'
        · rw [hb'] at hb; exact hA.paLeader r hr y w0 lb h hlb hs ⟨v, hv'⟩ hc hb
        · exfalso
          rw [hb'] at hb
          have a1 := (hS.1.2.2.2.2.2.2.2.2.2.2.1 r hr y w0 lb h hlb).1
          rw [← hb] at a1
          exact hfi (maker_eq S hS.1.2.2.2.2.2.1 hxq hmk a1)
      · rw [h] at hlb; simp [newInstanceDefault] at hlb
    · exact hA.paLeader r hr y w lb (hoth r y w hw hcc) hlb hs ⟨v, hv'⟩ hc hb
  · intro r hr y w lb hw hlb hp
    obtain ⟨w1, hw1, hlb1⟩ : ∃ w1, (S.rep r).inst y = some w1 ∧ w1.lb = some lb := by
      by_cases hc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hc; rw [R3] at hw; cases hw
        rw [hlbeq] at hlb
        rcases hX with h | ⟨-, h⟩
        · exact ⟨w0, h, hlb⟩
        · rw [h] at hlb; simp [newInstanceDefault] at hlb
      · exact ⟨w, hoth r y w hw hc, hlb⟩
    obtain ⟨c1, c2, c3, c4, c5⟩ := hA.prepNoProp r hr y w1 lb hw1 hlb1 hp
    exact ⟨c1, fun v hv => c2 v (hold r _ hv (fun h => by cases h)),
      fun v hv => c3 v (hold r _ hv (fun h => by cases h)), c4, c5⟩
  · intro fr' to y b; rw [hcnt0 fr' to _ rfl]; exact hA.paMsgOnce fr' to y b
  · intro fr' to y b; rw [hcnt0 fr' to _ rfl]; exact hA.accMsgOnce fr' to y b
  · intro r y b st v hst' hv
    rcases hA.paVoteDeliv r y b st v hst' (hvo _ _ _ _ _ hv) with ⟨v0, h1⟩ | h1
    · exact Or.inl ⟨v0, hH.ev_old h1⟩
    · exact Or.inr (fun fr' => hH.allDeliv_old (h1 fr') (fun _ m hm' => hnoP _ rfl _ m hm'))
  · intro a r y b h1
    rw [hcnt0 a r _ rfl] at h1 ⊢
    obtain ⟨c1, c2⟩ := hA.parOnce a r y b h1
    exact ⟨c1, hH.allDeliv_old c2 (fun _ m hm' => hnoP _ rfl _ m hm')⟩
  · intro a r m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn a r _ hm' with h | ⟨-, -, h⟩
    · obtain ⟨b', v, h1, h2⟩ := hA.arFrom a r m h; exact ⟨b', v, h1, hH.ev_old h2⟩
    · cases h
  · intro a r y b h1
    rw [hcnt0 a r _ rfl] at h1 ⊢
    rcases hA.arOnce a r y b h1 with h | ⟨h2, h3⟩
    · left
      obtain ⟨w, lb, hw, hlb, hlt⟩ := h
      rcases R2 r y w hw with ⟨e1, e2, e3⟩ | h
      · subst r y w; exact ⟨w', lb, R3, by rw [hlbeq]; exact hlb, hlt⟩
      · exact ⟨w, lb, h, hlb, hlt⟩
    · exact Or.inr ⟨h2, hH.allDeliv_old h3 (fun _ m hm' => hnoP _ rfl _ m hm')⟩
  · intro fr' to m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to _ hm' with h | ⟨-, -, h⟩
    · exact hA.commitBal fr' to m h
    · cases h
  · intro r to m he
    have hnotE : ∀ e', (∀ to' m', e' = .sent to' m' → m' ≠ .prepareReply rp) →
        S'.evBefore r (.sent to (.prepareReply m)) r e' → S.ev r e' →
        S.evBefore r (.sent to (.prepareReply m)) r e' := by
      intro e' hk hb he'
      exact hH.evBefore_back hb he' (fun _ h => by
        simp only [List.mem_singleton] at h; exact hk _ _ h rfl)
    refine ⟨fun hr => ?_, fun b st v hb => ?_, fun to' m2 hb hy => ?_⟩
    · rcases ctx_ev S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ he with h | ⟨hr', h⟩
      · obtain ⟨w, hw, hle⟩ := (hA.sentPR r to m h).1 hr
        rcases R2 r _ w hw with ⟨h1, h2, h3⟩ | h'
        · subst r w; rw [h2]; exact ⟨w', R3, Int.le_trans hle hwb⟩
        · exact ⟨w, h', hle⟩
      · simp only [Event.sent.injEq, Msg.prepareReply.injEq] at h; obtain ⟨-, rfl⟩ := h
        subst hr'; rw [hrx, hrb]; exact ⟨w', R3, Int.le_refl _⟩
    · have hv : S.ev r (.vote ⟨toN m.replica, toN m.inst⟩ b st v) := by
        obtain ⟨pp, pp', -, -, h⟩ := hb; exact hvo _ _ _ _ _ (List.mem_of_getElem? h)
      have hb0 := hnotE _ (fun _ _ h => by cases h) hb hv
      obtain ⟨pp, pp', -, h1, -⟩ := id hb0
      exact (hA.sentPR r to m (List.mem_of_getElem? h1)).2.1 b st v hb0
    · have hv : S.ev r (.sent to' (.acceptReply m2)) := by
        obtain ⟨pp, pp', -, -, h⟩ := hb
        exact ctx_ev_old S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn r _ (List.mem_of_getElem? h) (fun h => by cases h)
      have hb0 := hnotE _ (fun _ _ h h' => by cases h; cases h') hb hv
      obtain ⟨pp, pp', -, h1, -⟩ := id hb0
      exact (hA.sentPR r to m (List.mem_of_getElem? h1)).2.2 to' m2 hb0 hy
  · -- confCover
    intro r hr e y cy he hrec c hc
    rw [(F r).2.2.1]
    exact hA.confCover r hr e y cy (hold r e he (fun h => by subst h; simp [Event.recorded] at hrec))
      hrec c hc
  · -- classWf
    have hcl : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
        (S'.rep r).lastPut = (S.rep r).lastPut := by
      intro r; rw [hH.rep]; by_cases h : r = i
      · subst h; simp only [upd_same, RState.setInst]
        exact ⟨by rw [(AuxProof.bumpRB_cls _ _).1], by rw [(AuxProof.bumpRB_cls _ _).2]⟩
      · simp [upd_apply, h]
    intro r hr
    refine AuxProof.clsWf_keep (hA.classWf r hr) (hcl r).1 (hcl r).2 (fun y h => ?_)
    obtain ⟨w1, h1⟩ := Option.ne_none_iff_exists'.mp h
    rcases R2 r y w1 h1 with ⟨rfl, rfl, -⟩ | h2
    · rw [R3]; simp
    · rw [h2]; simp
  · -- classCover
    have hcl : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
        (S'.rep r).lastPut = (S.rep r).lastPut := by
      intro r; rw [hH.rep]; by_cases h : r = i
      · subst h; simp only [upd_same, RState.setInst]
        exact ⟨by rw [(AuxProof.bumpRB_cls _ _).1], by rw [(AuxProof.bumpRB_cls _ _).2]⟩
      · simp [upd_apply, h]
    intro r hr e y cy he hrec
    rw [(hcl r).1, (hcl r).2]
    exact hA.classCover r hr e y cy (hold r e he (fun h => by subst h; simp [Event.recorded] at hrec)) hrec
  · -- paAttrs
    intro r y b st v hst hv
    exact hH.ev_old (hA.paAttrs r y b st v hst (hvo _ _ _ _ _ hv))
  · -- valOk
    intro r y b v hv
    rw [hH.owner]
    exact hA.valOk r y b v (hv.imp (fun h => hold r _ h (fun h => by cases h))
      (fun h => hold r _ h (fun h => by cases h)))
  · -- cmdsNe
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hA.cmdsNe
    refine ⟨fun fr' to m hm' cs hc => ?_, fun r hr y w cs hw hc => ?_,
      fun r hr y w lb cs hw hlb hc => ?_, fun fr' to m hm' hs => ?_,
      fun r m he => m5 r m (hold r _ he (fun h => by cases h)),
      fun r y b v hv => m6 r y b v (hv.imp (fun h => hold r _ h (fun h => by cases h))
        (fun h => hold r _ h (fun h => by cases h)))⟩
    · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to m hm' with h | ⟨-, -, rfl⟩
      · exact m1 fr' to m h cs hc
      · cases hc
    · by_cases hcc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw; rw [hcm] at hc
        rcases hX with h | ⟨-, h⟩
        · exact m2 r hr y w0 cs h hc
        · rw [h] at hc; simp [newInstanceDefault] at hc
      · exact m2 r hr y w cs (hoth r y w hw hcc) hc
    · by_cases hcc : r = i ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hcc; rw [R3] at hw; cases hw
        rw [hlbeq] at hlb
        rcases hX with h | ⟨-, h⟩
        · exact m3 r hr y w0 lb cs h hlb hc
        · rw [h] at hlb; simp [newInstanceDefault] at hlb
      · exact m3 r hr y w lb cs (hoth r y w hw hcc) hlb hc
    · rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to _ hm' with h | ⟨-, -, h⟩
      · exact m4 fr' to m h hs
      · simp only [Msg.prepareReply.injEq] at h; subst h hrp
        simp only [prepRep] at hs ⊢
        rw [hst] at hs; rw [hcm]
        rcases hX with h | ⟨-, h⟩
        · obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp (hA.cmdsSome i hi x w0 h hs)
          rw [hcs]; exact m2 i hi x w0 cs h hcs
        · rw [h] at hs; exact absurd rfl hs
  · -- prSent
    intro fr' to m hm'
    rcases ctx_msgs S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn fr' to _ hm' with h | ⟨hf, ht, h⟩
    · exact hH.ev_old (hA.prSent fr' to m h)
    · simp only [Msg.prepareReply.injEq] at h; subst h hf ht
      exact hH.ev_new (by simp)
  · -- selfOk
    intro r m he hs
    exact hA.selfOk r m (hold r _ he (fun h => by cases h)) hs
  · -- selfRaw
    intro r m he
    exact hA.selfRaw r m (hold r _ he (fun h => by cases h))
  · -- pm (sixth agent)
    exact ctx_pm S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn
  · -- ownerCrt (p-model2)
    intro y ps h; rw [hH.owner] at h; rw [hcrt]; exact hA.ownerCrt y ps h
  · -- execLo (p-exec)
    exact AuxProof.execLo_of_eq hS.2.execLo (fun r _ => (F r).2.2.2.1)
  · -- execution fields (p-modelexec)
    refine ExecOrd.invExec_hs hS.1 hS.2.exec hH hidle (ctx_agr S S' fr i n p x w0 w' rp hS hi hfr hidle hn hm hx hH hro hw' hrp hdn) hchan R4 R3
      (fun w hw hs => ?_) (fun lb' hl hne => ?_)
    · rcases hro with h | ⟨h, -⟩
      · rw [h] at hw; cases hw; exact hcm
      · rw [h] at hw; cases hw
    · rw [hlbeq] at hl
      rcases hro with h | ⟨-, h⟩
      · exact ⟨w0, lb', h, hl, hne⟩
      · subst h; simp [newInstanceDefault] at hl

end

/-- **`handlePrepare` keeps the invariant.** -/
theorem inv_deliver_prepare' (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : Prepare)
    (hm : (S.sent fr i)[n]? = some (.prepare p)) : Inv (S.deliver fr i n (.prepare p)) := by
  have hpm := mem_msgs_of_sent S hm
  obtain ⟨hldr, -⟩ := hS.1.2.2.2.2.2.1.2.2.2.1 fr i p hpm
  have hH := prepare_step S fr i n p hidle hm hfr hldr
  have hro := recOr_of (S.rep i) ⟨toN p.replica, toN p.inst⟩
  have hdn := deliver_delivered S fr i n (.prepare p)
  generalize recOr (S.rep i) ⟨toN p.replica, toN p.inst⟩ = w0 at hH hro
  generalize hw' : prepRec w0 p = w' at hH
  generalize hrp : prepRep (S.rep i) w' p = rp at hH
  have hwf := ctx_wf S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn
  have hbal := ctx_ballots S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn
  have hown := ctx_own S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn
  have hvf := ctx_vf S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn
  have hsafe := ctx_safe S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn
  obtain ⟨e1, e2, e3, e4⟩ := ctx_exec S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn
  exact ⟨⟨hwf, ctx_msgWf S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_rt S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_ntpa S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, hbal, hown, ctx_op S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, hvf,
    ctx_rr S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_hi S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_lb S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_agr S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_dc S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn,
    chosenSafe_of_safe _ hwf hbal hown hvf hsafe, ctx_dcv S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_wit S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_ac S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, e1, e2,
    e3, e4, ctx_slots S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_co S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_cm S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, ctx_pk S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn, hsafe, ctx_reports S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn⟩,
    ctx_aux S _ fr i n p _ w0 w' rp hS hi hfr hidle hn hm rfl hH hro hw'.symm hrp.symm hdn (ExecOrd.deliver_chan_nil S fr i n _ (fun c h => by cases h))⟩

end PrepareProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
