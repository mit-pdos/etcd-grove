/-
`InvAux` under the steps that change no record field it reads (`CoreEq`), make no event it reads
(only `sent` events), only shrink the message lists (keeping the positions of what stays, or
moving it past `sent`), and only add deliveries: `aux_congr`. Used for the finished steps
(the frame steps, `lose`, `bcast`, `execSCC`, `execBump`, the no-op deliveries).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecFrame
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.PMFrame

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace AuxProof

/-! ### `ExecLo` (p-exec) under the steps -/

/-- `ExecLo` when no `ExecedUpTo` changed. -/
theorem execLo_of_eq {S S' : Sys} (h : ExecLo S)
    (he : ∀ r < nR, (S'.rep r).execedUpTo = (S.rep r).execedUpTo) : ExecLo S' := by
  intro r hr q hq; rw [he r hr]; exact h r hr q hq

/-- `ExecLo` when one replica's state changed, keeping its `ExecedUpTo`. -/
theorem execLo_upd {S S' : Sys} {i : Nat} {σ' : RState} (h : ExecLo S)
    (hrep : S'.rep = upd S.rep i σ') (he : σ'.execedUpTo = (S.rep i).execedUpTo) : ExecLo S' := by
  refine execLo_of_eq h (fun r _ => ?_)
  rw [hrep]; by_cases hr : r = i
  · subst hr; simp only [upd_same]; exact he
  · simp only [upd_other _ _ _ _ hr]

/-- The bookkeeping fields `InvAux` reads. -/
def LbEq (lb lb' : LbRec) : Prop :=
  lb'.lastTriedBallot = lb.lastTriedBallot ∧ lb'.status = lb.status ∧
    lb'.preparing = lb.preparing ∧ lb'.prepareReplies = lb.prepareReplies ∧
    lb'.leaderResponded = lb.leaderResponded ∧ lb'.cmds = lb.cmds

/-- The record fields `InvAux` reads. -/
def CoreEq (w w' : InstRec) : Prop :=
  w'.cmds = w.cmds ∧ w'.bal = w.bal ∧ w'.vbal = w.vbal ∧ w'.status = w.status ∧
    w'.seq = w.seq ∧ w'.deps = w.deps ∧
    (∀ lb', w'.lb = some lb' → ∃ lb, w.lb = some lb ∧ LbEq lb lb') ∧
    (∀ lb, w.lb = some lb → ∃ lb', w'.lb = some lb' ∧ LbEq lb lb')

theorem LbEq.refl (lb : LbRec) : LbEq lb lb := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CoreEq.refl (w : InstRec) : CoreEq w w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun lb' h => ⟨lb', h, LbEq.refl _⟩,
    fun lb h => ⟨lb, h, LbEq.refl _⟩⟩

theorem CoreEq.instVal {w w' : InstRec} (h : CoreEq w w') : instVal w' = instVal w := by
  obtain ⟨h1, -, -, -, h5, h6, -⟩ := h
  simp only [model.instVal, h1, h5, h6]

/-- A sublist's count is at most the list's. -/
theorem cnt_le_of_sublist {l l' : List Msg} (h : l'.Sublist l) (p : Msg → Bool) :
    (l'.filter p).length ≤ (l.filter p).length :=
  (h.filter p).length_le

/-! ### `classWf` / `classCover` per replica state (stage 2) -/

/-- `InvAux.classWf` of one replica's state. -/
def ClsWf (σ : RState) : Prop :=
  ∀ q < nR,
    (0 ≤ zz (σ.lastScan q) → σ.inst ⟨q, toN (σ.lastScan q)⟩ ≠ none) ∧
    (0 ≤ zz (σ.lastPut q) → σ.inst ⟨q, toN (σ.lastPut q)⟩ ≠ none) ∧
    -1 ≤ zz (σ.lastScan q) ∧ -1 ≤ zz (σ.lastPut q)

/-- `InvAux.classCover` of one recorded `(x, cx)` against one replica's state. -/
def ClsCov (σ : RState) (x : InstId) (cx : List WCmd) : Prop :=
  ∀ c ∈ cx, (c.op = opSCAN → (x.i : Int) ≤ zz (σ.lastScan x.q)) ∧
    (c.op = opPUT → (x.i : Int) ≤ zz (σ.lastPut x.q))

theorem clsWf_keep {σ σ' : RState} (h : ClsWf σ) (hs : σ'.lastScan = σ.lastScan)
    (hp : σ'.lastPut = σ.lastPut) (hg : ∀ y, σ.inst y ≠ none → σ'.inst y ≠ none) : ClsWf σ' := by
  intro q hq
  obtain ⟨a1, a2, a3, a4⟩ := h q hq
  rw [hs, hp]
  exact ⟨fun h => hg _ (a1 h), fun h => hg _ (a2 h), a3, a4⟩

/-- The class arrays only grow. -/
def clsLe (σ σ' : RState) : Prop :=
  ∀ q, zz (σ.lastScan q) ≤ zz (σ'.lastScan q) ∧ zz (σ.lastPut q) ≤ zz (σ'.lastPut q)

theorem clsLe_refl (σ : RState) : clsLe σ σ := fun _ => ⟨Int.le_refl _, Int.le_refl _⟩

theorem clsLe_trans {σ σ' σ'' : RState} (h1 : clsLe σ σ') (h2 : clsLe σ' σ'') : clsLe σ σ'' :=
  fun q => ⟨Int.le_trans (h1 q).1 (h2 q).1, Int.le_trans (h1 q).2 (h2 q).2⟩

theorem clsCov_mono {σ σ' : RState} (hle : clsLe σ σ') {x : InstId} {cx : List WCmd}
    (h : ClsCov σ x cx) : ClsCov σ' x cx := fun c hc =>
  ⟨fun e => Int.le_trans ((h c hc).1 e) (hle x.q).1, fun e => Int.le_trans ((h c hc).2 e) (hle x.q).2⟩

theorem clsLe_of_eq {σ σ' : RState} (hs : σ'.lastScan = σ.lastScan)
    (hp : σ'.lastPut = σ.lastPut) : clsLe σ σ' := by
  intro q; rw [hs, hp]; exact ⟨Int.le_refl _, Int.le_refl _⟩

/-- (stage 2) `bumpRecvBallot` and `setInst` keep the class arrays. -/
theorem bumpRB_cls (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).lastScan = σ.lastScan ∧ (bumpRecvBallot σ b).lastPut = σ.lastPut := by
  unfold bumpRecvBallot; split <;> exact ⟨rfl, rfl⟩

theorem bumpCrt_cls (σ : RState) (q : Nat) (n : w32) :
    (bumpCrt σ q n).lastScan = σ.lastScan ∧ (bumpCrt σ q n).lastPut = σ.lastPut := by
  unfold bumpCrt; split <;> exact ⟨rfl, rfl⟩

theorem setInst_cls (σ : RState) (x : InstId) (w : InstRec) :
    (σ.setInst x w).lastScan = σ.lastScan ∧ (σ.setInst x w).lastPut = σ.lastPut := ⟨rfl, rfl⟩

/-- A step's frame for `InvAux`. -/
structure AuxFrame (S S' : Sys) : Prop where
  inst1 : ∀ r x w', (S'.rep r).inst x = some w' → ∃ w, (S.rep r).inst x = some w ∧ CoreEq w w'
  inst2 : ∀ r x w, (S.rep r).inst x = some w → ∃ w', (S'.rep r).inst x = some w' ∧ CoreEq w w'
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

theorem aux_congr (S S' : Sys) (hA : InvAux S)
    (hwf7 : ∀ fr to n, (fr, to, n) ∈ S.delivered → n < (S.sent fr to).length)
    (hF : AuxFrame S S') (hpm : InvPM S') (hX : InvExec S') (hlo : ExecLo S') : InvAux S' := by
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
    rw [c.2.2.2.1]; exact a1 r hr x w hw
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.2.1] at hs; rw [c.1]; exact a2 r hr x w hw hs
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.2.1] at hs
    obtain ⟨h1, h2⟩ := a3 r hr x w hw hs
    exact ⟨by rw [c.2.2.1]; exact h1, fun b st v h => h2 b st v ((hvote _ _ _ _ _).mp h)⟩
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.2.1] at hs; rw [c.2.2.1]; exact a4 r hr x w hw hs
  · intro r hr x w' hw' b st v hv
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.1]; exact a5 r hr x w hw b st v ((hvote _ _ _ _ _).mp hv)
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.2.1] at hs ⊢; rw [c.2.2.1, c.instVal, hvote]; exact a6 r hr x w hw hs
  · intro r hr x w' hw' b u hv hle
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.2.1]; rw [c.2.2.1] at hle
    exact a7 r hr x w hw b u ((hvote _ _ _ _ _).mp hv) hle
  · intro r hr x w' hw' hs
    obtain ⟨w, hw, c⟩ := i1 r x w' hw'
    rw [c.2.2.2.1] at hs
    obtain ⟨b, v, h1, h2⟩ := a8 r hr x w hw hs
    exact ⟨b, v, (hcm _ _ _ _).mpr h1, by rw [c.2.1]; exact h2⟩
  · intro r x b v hr hv
    obtain ⟨w, hw, hs⟩ := a9 r x b v hr ((hcm _ _ _ _).mp hv)
    obtain ⟨w', hw', c⟩ := i2 r x w hw
    exact ⟨w', hw', by rw [c.2.2.2.1]; exact hs⟩
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
    rw [e.2.1] at hs; rw [e.1] at hp hb ⊢; rw [c.2.2.2.1] at hc ⊢; rw [c.2.1] at hb; rw [c.2.2.1]
    obtain ⟨v, hv⟩ := hp
    exact a20 r hr x w lb hw hlb hs ⟨v, (hph _ _ _ _).mp hv⟩ hc hb
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
