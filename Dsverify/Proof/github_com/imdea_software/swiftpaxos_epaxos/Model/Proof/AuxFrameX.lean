/-
`InvAux` under a step that may also move records from COMMITTED to EXECUTED (the executor's
`instDone`, p-modelexec): `aux_congr_ex`, a copy of `AuxProof.aux_congr` (AuxFrame.lean) whose
record relation `CoreEqX` lets the status go from COMMITTED to EXECUTED; only the bullets of the
fields reading a record's status differ. (When fields are added to `InvAux`, add them here as in
`aux_congr`.)
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxFrame

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace AuxProof

/-- A status kept, or COMMITTED become EXECUTED. -/
def StRel (s s' : w8) : Prop := s' = s ∨ (s = stCOMMITTED ∧ s' = stEXECUTED)

/-- `CoreEq` with the status relaxed to `StRel`. -/
def CoreEqX (w w' : InstRec) : Prop :=
  w'.cmds = w.cmds ∧ w'.bal = w.bal ∧ w'.vbal = w.vbal ∧ StRel w.status w'.status ∧
    w'.seq = w.seq ∧ w'.deps = w.deps ∧
    (∀ lb', w'.lb = some lb' → ∃ lb, w.lb = some lb ∧ LbEq lb lb') ∧
    (∀ lb, w.lb = some lb → ∃ lb', w'.lb = some lb' ∧ LbEq lb lb')

theorem CoreEqX.instVal {w w' : InstRec} (h : CoreEqX w w') : instVal w' = instVal w := by
  obtain ⟨h1, -, -, -, h5, h6, -⟩ := h
  simp only [model.instVal, h1, h5, h6]

/-- `AuxFrame` with `CoreEqX`. -/
structure AuxFrameX (S S' : Sys) : Prop where
  inst1 : ∀ r x w', (S'.rep r).inst x = some w' → ∃ w, (S.rep r).inst x = some w ∧ CoreEqX w w'
  inst2 : ∀ r x w, (S.rep r).inst x = some w → ∃ w', (S'.rep r).inst x = some w' ∧ CoreEqX w w'
  crt : ∀ r, (S'.rep r).crtInstance = (S.rep r).crtInstance
  peer : ∀ r < nR, ((S'.rep r).peerOrder.take (nR - 1)).Nodup ∧
    ∀ p ∈ (S'.rep r).peerOrder.take (nR - 1), p < nR ∧ p ≠ r
  ev : ∀ r e, (∀ to m, e ≠ .sent to m) → (S'.ev r e ↔ S.ev r e)
  sub : ∀ fr to, (S'.msgs fr to).Sublist (S.msgs fr to)
  pos : ∀ fr to n m, (S'.msgs fr to)[n]? = some m →
    ∃ n', (S.msgs fr to)[n']? = some m ∧ (n' = n ∨ (S.sent fr to).length ≤ n')
  del : ∀ d, d ∈ S.delivered → d ∈ S'.delivered
  evPR : ∀ r to m, S'.ev r (.sent to (.prepareReply m)) → S.ev r (.sent to (.prepareReply m))
  evB : ∀ r e r' e', (∀ to m, e' = .sent to m → m.isBcast = false) → S'.evBefore r e r' e' →
    S.evBefore r e r' e'
  conf : ∀ r, (S'.rep r).conflicts = (S.rep r).conflicts
  owner : S'.owner = S.owner
  mono : ∀ r e, S.ev r e → S'.ev r e
  /-- (stage 2) the class arrays (fix S1) are kept -/
  cls : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧ (S'.rep r).lastPut = (S.rep r).lastPut

theorem aux_congr_ex (S S' : Sys) (hA : InvAux S)
    (hwf7 : ∀ fr to n, (fr, to, n) ∈ S.delivered → n < (S.sent fr to).length)
    (hF : AuxFrameX S S') (hpm : InvPM S') (hX : InvExec S') (hlo : ExecLo S') : InvAux S' := by
  obtain ⟨i1, i2, hcrt, hpeer, hev, hsub, hpos, hdel, hevPR, hevB, hconf, howner, hmono, hcls⟩ := hF
  -- events other than sends
  have hvote : ∀ r x b st v, S'.ev r (.vote x b st v) ↔ S.ev r (.vote x b st v) :=
    fun r x b st v => hev r _ (fun _ _ h => by cases h)
  have hcm : ∀ r x b v, S'.ev r (.commit x b v) ↔ S.ev r (.commit x b v) :=
    fun r x b v => hev r _ (fun _ _ h => by cases h)
  have hph : ∀ r x b v, S'.ev r (.phase1 x b v) ↔ S.ev r (.phase1 x b v) :=
    fun r x b v => hev r _ (fun _ _ h => by cases h)
  have hac : ∀ r x b v, S'.ev r (.accept x b v) ↔ S.ev r (.accept x b v) :=
    fun r x b v => hev r _ (fun _ _ h => by cases h)
  have hcnt : ∀ fr to p, S'.cnt fr to p ≤ S.cnt fr to p :=
    fun fr to p => cnt_le_of_sublist (hsub fr to) p
  have hmem : ∀ fr to m, m ∈ S'.msgs fr to → m ∈ S.msgs fr to :=
    fun fr to m h => (hsub fr to).subset h
  have hall : ∀ fr to p, S.allDeliv fr to p → S'.allDeliv fr to p := by
    intro fr to p h n m hn hp
    obtain ⟨n', hn', heq | hge⟩ := hpos fr to n m hn
    · subst heq; exact hdel _ (h _ m hn' hp)
    · have := hwf7 fr to n' (h n' m hn' hp); omega
  have habove : ∀ r x b, S.lastAbove r x b → S'.lastAbove r x b := by
    rintro r x b ⟨w, lb, hw, hlb, hlt⟩
    obtain ⟨w', hw', -, -, -, -, -, -, -, h8⟩ := i2 r x w hw
    obtain ⟨lb', hlb', e1, -⟩ := h8 lb hlb
    exact ⟨w', lb', hw', hlb', by rw [e1]; exact hlt⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, b1, b2, a31, a32, a33, a34, a35, a36, a37, a38, -, -⟩ := hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlo, hX⟩
  · intro r hr x w' hw'
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rcases c.2.2.2.1 with hst | ⟨-, hst⟩
    · rw [hst]; exact a1 r hr x w hw
    · rw [hst]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.1]
    rcases c.2.2.2.1 with hst | ⟨h0, -⟩
    · rw [hst] at hs; exact a2 r hr x w hw hs
    · exact a2 r hr x w hw (by rw [h0]; decide)
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rcases c.2.2.2.1 with hst | ⟨-, hst⟩
    · rw [hst] at hs
      obtain ⟨h1, h2⟩ := a3 r hr x w hw hs
      exact ⟨by rw [c.2.2.1]; exact h1, fun b st v h => h2 b st v ((hvote _ _ _ _ _).mp h)⟩
    · rw [hst] at hs; exact absurd hs (by decide)
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.1]
    rcases c.2.2.2.1 with hst | ⟨h0, -⟩
    · rw [hst] at hs; exact a4 r hr x w hw hs
    · exact a4 r hr x w hw (by rw [h0]; decide)
  · intro r hr x w' hw' b st v hv
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.1]; exact a5 r hr x w hw b st v ((hvote _ _ _ _ _).mp hv)
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rcases c.2.2.2.1 with hst | ⟨-, hst⟩
    · rw [hst] at hs ⊢; rw [c.2.2.1, c.instVal, hvote]; exact a6 r hr x w hw hs
    · rw [hst] at hs; exfalso; rcases hs with (h | h) | h <;> exact absurd h (by decide)
  · intro r hr x w' hw' b u hv hle
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.1] at hle
    rcases c.2.2.2.1 with hst | ⟨-, hst⟩
    · rw [hst]; exact a7 r hr x w hw b u ((hvote _ _ _ _ _).mp hv) hle
    · rw [hst]; exact Or.inr (Or.inr rfl)
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    have hs' : isCommitted w.status := by
      rcases c.2.2.2.1 with hst | ⟨h0, -⟩
      · rw [hst] at hs; exact hs
      · exact Or.inl h0
    obtain ⟨b, v, h1, h2⟩ := a8 r hr x w hw hs'
    exact ⟨b, v, (hcm _ _ _ _).mpr h1, by rw [c.2.1]; exact h2⟩
  · intro r x b v hr hv
    obtain ⟨w, hw, hs⟩ := a9 r x b v hr ((hcm _ _ _ _).mp hv)
    obtain ⟨w', hw', c⟩ := i2 r x w hw
    refine ⟨w', hw', ?_⟩
    rcases c.2.2.2.1 with hst | ⟨-, hst⟩
    · rw [hst]; exact hs
    · rw [hst]; exact Or.inr rfl
  · intro r x v hv
    obtain ⟨h1, b, h2⟩ := a10 r x v ((hev r _ (fun _ _ h => by cases h)).mp hv)
    exact ⟨h1, b, (hcm _ _ _ _).mpr h2⟩
  · intro r x b hr hv
    obtain ⟨w, lb, hw, hlb, hle⟩ := a11 r x b hr ((hev r _ (fun _ _ h => by cases h)).mp hv)
    obtain ⟨w', hw', -, -, -, -, -, -, -, h8⟩ := i2 r x w hw
    obtain ⟨lb', hlb', e1, -⟩ := h8 lb hlb
    exact ⟨w', lb', hw', hlb', by rw [e1]; exact hle⟩
  · intro r hr x w' lb' hw' hlb'
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    obtain ⟨lb, hlb, e⟩ := c.2.2.2.2.2.2.1 lb' hlb'
    rw [e.1, c.2.1]; exact a12 r hr x w lb hw hlb
  · exact hpeer
  · intro r hr q hq; rw [hcrt, hcrt]; exact a14 r hr q hq
  · intro r hr x w' hw'
    obtain ⟨w, hw, -⟩ := i1 r x w' hw'
    rw [hcrt]; exact a15 r hr x w hw
  · intro fr to m x hm hx; rw [hcrt]; exact a16 fr to m x (hmem _ _ _ hm) hx
  · intro r e x he hx
    have hns : ∀ to m, e ≠ .sent to m := by
      intro to m h; subst h; simp [Event.instOf] at hx
    rw [hcrt]; exact a17 r e x ((hev r e hns).mp he) hx
  · intro q hq j hj
    rw [hcrt] at hj
    obtain ⟨w, lb, hw, hlb⟩ := a18 q hq j hj
    obtain ⟨w', hw', -, -, -, -, -, -, -, h8⟩ := i2 q _ w hw
    obtain ⟨lb', hlb', -⟩ := h8 lb hlb
    exact ⟨w', lb', hw', hlb'⟩
  · intro r hr x w' lb' hw' hlb' hs v hv
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    obtain ⟨lb, hlb, e⟩ := c.2.2.2.2.2.2.1 lb' hlb'
    rw [e.2.1] at hs; rw [e.1] at hv
    exact a19 r hr x w lb hw hlb hs v ((hac _ _ _ _).mp hv)
  · intro r hr x w' lb' hw' hlb' hs hp hc hb
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    obtain ⟨lb, hlb, e⟩ := c.2.2.2.2.2.2.1 lb' hlb'
    rcases c.2.2.2.1 with hst | ⟨-, hst⟩
    · rw [e.2.1] at hs; rw [e.1] at hp hb ⊢; rw [hst] at hc ⊢; rw [c.2.1] at hb; rw [c.2.2.1]
      obtain ⟨v, hv⟩ := hp
      exact a20 r hr x w lb hw hlb hs ⟨v, (hph _ _ _ _).mp hv⟩ hc hb
    · rw [hst] at hc; exact absurd hc (by decide)
  · intro r hr x w' lb' hw' hlb' hp
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    obtain ⟨lb, hlb, e⟩ := c.2.2.2.2.2.2.1 lb' hlb'
    obtain ⟨e1, -, e3, e4, e5, -⟩ := e
    rw [e3] at hp; rw [e1, e4, e5]
    obtain ⟨h1, h2, h3, h4, h5⟩ := a21 r hr x w lb hw hlb hp
    exact ⟨h1, fun v hv => h2 v ((hph _ _ _ _).mp hv), fun v hv => h3 v ((hac _ _ _ _).mp hv),
      h4, h5⟩
  · intro fr to x b; exact Nat.le_trans (hcnt _ _ _) (a22 fr to x b)
  · intro fr to x b; exact Nat.le_trans (hcnt _ _ _) (a23 fr to x b)
  · intro r x b st v hst hv
    rcases a24 r x b st v hst ((hvote _ _ _ _ _).mp hv) with ⟨v0, h⟩ | h
    · exact Or.inl ⟨v0, (hph _ _ _ _).mpr h⟩
    · exact Or.inr (fun fr => hall _ _ _ (h fr))
  · intro a r x b h1
    obtain ⟨h2, h3⟩ := a25 a r x b (Nat.le_trans h1 (hcnt _ _ _))
    exact ⟨Nat.le_antisymm (h2 ▸ hcnt _ _ _) h1, hall _ _ _ h3⟩
  · intro a r m hm
    obtain ⟨b', v, h1, h2⟩ := a26 a r m (hmem _ _ _ hm)
    exact ⟨b', v, h1, (hac _ _ _ _).mpr h2⟩
  · intro a r x b h1
    rcases a27 a r x b (Nat.le_trans h1 (hcnt _ _ _)) with h | ⟨h2, h3⟩
    · exact Or.inl (habove _ _ _ h)
    · exact Or.inr ⟨Nat.le_antisymm (h2 ▸ hcnt _ _ _) h1, hall _ _ _ h3⟩
  · intro fr to m hm; exact a28 fr to m (hmem _ _ _ hm)
  · intro r to m he
    obtain ⟨c1, c2, c3⟩ := a29 r to m (hevPR r to m he)
    refine ⟨fun hr => ?_, fun b st v hb => c2 b st v (hevB _ _ _ _ (fun _ _ h => by cases h) hb),
      fun to' m2 hb hy => c3 to' m2 (hevB _ _ _ _ (fun _ _ h => by cases h; rfl) hb) hy⟩
    obtain ⟨w, hw, hle⟩ := c1 hr
    obtain ⟨w', hw', -, h2, -⟩ := i2 r _ w hw
    exact ⟨w', hw', by rw [h2]; exact hle⟩
  · intro r hr e x cx he hrec c hc
    rw [hconf]
    have hns : ∀ to m, e ≠ .sent to m := by
      intro to m h; subst h; simp [Event.recorded] at hrec
    exact a30 r hr e x cx ((hev r e hns).mp he) hrec c hc
  · intro r hr q hq
    rw [(hcls r).1, (hcls r).2]
    obtain ⟨c1, c2, c3, c4⟩ := b1 r hr q hq
    refine ⟨fun h => ?_, fun h => ?_, c3, c4⟩
    · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (c1 h)
      obtain ⟨w', hw', -⟩ := i2 r _ w hw
      rw [hw']; simp
    · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (c2 h)
      obtain ⟨w', hw', -⟩ := i2 r _ w hw
      rw [hw']; simp
  · intro r hr e x cx he hrec c hc
    rw [(hcls r).1, (hcls r).2]
    have hns : ∀ to m, e ≠ .sent to m := by
      intro to m h; subst h; simp [Event.recorded] at hrec
    exact b2 r hr e x cx ((hev r e hns).mp he) hrec c hc
  · intro r x b st v hst hv
    exact (hev r _ (fun _ _ h => by cases h)).mpr (a31 r x b st v hst ((hvote _ _ _ _ _).mp hv))
  · intro r x b v hv
    rw [howner]
    exact a32 r x b v (hv.imp (hph _ _ _ _).mp (hac _ _ _ _).mp)
  · obtain ⟨n1, n2, n3, n4, n5, n6⟩ := a33
    refine ⟨fun fr to m hm => n1 fr to m (hmem _ _ _ hm), fun r hr x w' cs hw' hc => ?_,
      fun r hr x w' lb' cs hw' hlb' hc => ?_, fun fr to m hm => n4 fr to m (hmem _ _ _ hm),
      fun r m he => n5 r m ((hev r _ (fun _ _ h => by cases h)).mp he),
      fun r x b v hv => n6 r x b v (hv.imp (hph _ _ _ _).mp (hac _ _ _ _).mp)⟩
    · obtain ⟨w, hw, c⟩ := i1 r x w' hw'
      rw [c.1] at hc; exact n2 r hr x w cs hw hc
    · obtain ⟨w, hw, c⟩ := i1 r x w' hw'
      obtain ⟨lb, hlb, e⟩ := c.2.2.2.2.2.2.1 lb' hlb'
      rw [e.2.2.2.2.2] at hc; exact n3 r hr x w lb cs hw hlb hc
  · intro fr to m hm; exact hmono _ _ (a34 fr to m (hmem _ _ _ hm))
  · intro r m he hs; exact a35 r m ((hev r _ (fun _ _ h => by cases h)).mp he) hs
  · intro r m he; exact a36 r m ((hev r _ (fun _ _ h => by cases h)).mp he)
  · exact hpm
  · intro x ps h; rw [howner] at h; rw [hcrt]; exact a38 x ps h

end AuxProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
