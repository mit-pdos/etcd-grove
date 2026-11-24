/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/ExInv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b (RMW side): **the executed accounting** (`XInv`, `xinv`).

Per instance `x = (rid32 L, i)` (leader `L`), a ghost phase per replica `r` (`G r L i`): `none`,
`eo` (its `ExecuteOverwrite` of `x` is pending at `r`: exactly one), `ex` (its `Executed` is in
flight to `L`: the `Executed(x)` at `L` count the `ex` replicas), `done` (handled at `L`). A
replica past `none` executed `x` with result `vt` (in its executed sequence), the pending
`ExecuteOverwrite` carries `vt.t`, and past `eo` its store holds at least `vt.t`. The leader's
bookkeeping of `x` counts at most the `done` replicas (`numReplicasExecuted`), and 2 fewer if
`x` was already replied to (`Rep`); a reply (`repliedClient`) is recorded in `Rep`, and a replied
instance has 2 `done` replicas. Hence (`rep_new`) a reply to `x` is never repeated: at a second
one the leader would count `≥ 4` replicas.
-/
module

public import Dsverify.Proof.gryff.PureLb.ExBase

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- The leader's bookkeeping `lb` of `(rid32 L, i)` is accounted for. -/
def LBOk (l : List Label) (G : GX) (L : Fin 3) (i : w32) (lb : LB) : Prop :=
  (lb.repliedClient = true → Rep l (rid32 L, i)) ∧
  (lb.repliedClient = false → 0 ≤ sint.Z lb.numReplicasExecuted ∧
    sint.Z lb.numReplicasExecuted ≤ phCnt (fun r => G r L i) .done ∧
    (Rep l (rid32 L, i) → sint.Z lb.numReplicasExecuted + 2 ≤ phCnt (fun r => G r L i) .done))

/-- The accounting of instance `(rid32 L, i)`. -/
structure XI (l : List Label) (c : Cfg gNet) (G : GX) (L : Fin 3) (i : w32) : Prop where
  eo : ∀ r, (infR c r).countP (isEOx (rid32 L) i) = if G r L i = .eo then 1 else 0
  ex : (infR c L).count (exM (rid32 L) i) = phCnt (fun r => G r L i) .ex
  ph : ∀ r, G r L i ≠ .none → ∃ vt, ((rid32 L, i), vt) ∈ execSeq r (projR l r) ∧
    (∀ m, Msg.executeOverwrite m ∈ infR c r → m.leader = rid32 L → m.slot = i → m.t = vt.t) ∧
    (G r L i ≠ .eo → tagLe vt.t.toP (stR c r).tag.toP)
  rep : Rep l (rid32 L, i) → 2 ≤ phCnt (fun r => G r L i) .done
  lb : ∀ cp lb, (stR c L).inst (rid32 L) i = some cp → cp.lb = some lb → LBOk l G L i lb

def XInv (l : List Label) (c : Cfg gNet) (G : GX) : Prop := ∀ L i, XI l c G L i

/-! ## Facts of the run and of A2's invariant -/

section
variable {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}

theorem StepAt.st_a (hs : StepAt l c a e c' s' o) : stOf a (projR l a) = stR c a := by
  have := cutSt_len hs.run a
  unfold cutSt at this; rwa [List.take_length] at this

theorem StepAt.exec_mono (hs : StepAt l c a e c' s' o) {r : Fin 3} {x : w32 × w32} {vt : ValTag}
    (h : (x, vt) ∈ execSeq r (projR l r)) : (x, vt) ∈ execSeq r (projR (l ++ [(a, e)]) r) := by
  rw [proj_snoc]; split
  · exact execSeq_append_mem r [e] h
  · exact h

theorem StepAt.countP_inf (hs : StepAt l c a e c' s' o) (f : Msg → Bool) (j : Fin 3) :
    (infR c' j).countP f =
      (if j = a then consume e.recv (infR c j) else infR c j).countP f + (sentR j o).countP f := by
  rw [hs.inf j, List.countP_append]

theorem StepAt.count_inf (hs : StepAt l c a e c' s' o) (m : Msg) (j : Fin 3) :
    (infR c' j).count m =
      (if j = a then consume e.recv (infR c j) else infR c j).count m + (sentR j o).count m := by
  rw [hs.inf j, List.count_append]

/-- A2's facts used here. -/
structure AF (c : Cfg gNet) : Prop where
  id : ∀ r, (stR c r).id = rid32 r
  inst : ∀ r q i cp, (stR c r).inst q i = some cp → (∃ L, q = rid32 L) ∧ cp.leader = q ∧ cp.slot = i
  eo : ∀ r m, Msg.executeOverwrite m ∈ infR c r → ∃ L, m.leader = rid32 L
  ex : ∀ r m, Msg.executed m ∈ infR c r → m.replica = rid32 r

theorem af_of {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : AF c := by
  obtain ⟨hS, hM⟩ := tot.inv_reach h
  refine ⟨fun r => (hS r).id, ?_, ?_, ?_⟩
  · intro r q i cp hc
    obtain ⟨⟨L, hL, -⟩, hok⟩ := (hS r).inst q i cp hc
    exact ⟨⟨L, hL⟩, hok.2.2.1, hok.2.2.2.1⟩
  · intro r m hm
    obtain ⟨⟨L, hL, -⟩, -⟩ := hM r _ hm
    exact ⟨L, hL⟩
  · intro r m hm
    exact (hM r _ hm).1

end

/-! ## Frame -/

theorem lbok_mono {l l' : List Label} {G G' : GX} {L : Fin 3} {i : w32} {lb : LB}
    (h : LBOk l G L i lb) (hc : phCnt (fun r => G r L i) .done ≤ phCnt (fun r => G' r L i) .done)
    (hr : Rep l' (rid32 L, i) ↔ Rep l (rid32 L, i)) : LBOk l' G' L i lb := by
  refine ⟨fun h1 => hr.2 (h.1 h1), fun h1 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h.2 h1
  exact ⟨a1, by omega, fun h2 => by have := a3 (hr.1 h2); omega⟩

theorem lbok_fresh {l : List Label} {G : GX} {L : Fin 3} {i : w32} {lb : LB}
    (hrep : Rep l (rid32 L, i) → 2 ≤ phCnt (fun r => G r L i) .done)
    (h0 : (lb.numReplicasExecuted, lb.repliedClient) = (0, false)) : LBOk l G L i lb := by
  simp only [Prod.mk.injEq] at h0
  obtain ⟨h1, h2⟩ := h0
  refine ⟨fun h => (by rw [h2] at h; cases h), fun _ => ?_⟩
  rw [h1]
  have : sint.Z (0 : w32) = 0 := by decide
  rw [this]
  exact ⟨Int.le_refl _, by omega, fun h => by have := hrep h; omega⟩

theorem ph_part' {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {G G' : GX} {L : Fin 3} {i : w32}
    (hI : XI l c G L i) {r : Fin 3} (hn : G' r L i ≠ .none → G r L i ≠ .none)
    (he : G' r L i ≠ .eo → G r L i ≠ .eo)
    (hmsg : ∀ m, Msg.executeOverwrite m ∈ infR c' r → m.leader = rid32 L → m.slot = i →
      Msg.executeOverwrite m ∈ infR c r) :
    G' r L i ≠ .none → ∃ vt, ((rid32 L, i), vt) ∈ execSeq r (projR (l ++ [(a, e)]) r) ∧
      (∀ m, Msg.executeOverwrite m ∈ infR c' r → m.leader = rid32 L → m.slot = i → m.t = vt.t) ∧
      (G' r L i ≠ .eo → tagLe vt.t.toP (stR c' r).tag.toP) := by
  intro hr
  obtain ⟨vt, h1, h2, h3⟩ := hI.ph r (hn hr)
  exact ⟨vt, hs.exec_mono h1, fun m hm a1 a2 => h2 m (hmsg m hm a1 a2) a1 a2,
    fun h => tagLe_trans (h3 (he h)) (hs.tag_mono r)⟩

theorem ph_part {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {G G' : GX} {L : Fin 3} {i : w32}
    (hI : XI l c G L i) {r : Fin 3} (hG : G' r L i = G r L i)
    (hmsg : ∀ m, Msg.executeOverwrite m ∈ infR c' r → m.leader = rid32 L → m.slot = i →
      Msg.executeOverwrite m ∈ infR c r) :
    G' r L i ≠ .none → ∃ vt, ((rid32 L, i), vt) ∈ execSeq r (projR (l ++ [(a, e)]) r) ∧
      (∀ m, Msg.executeOverwrite m ∈ infR c' r → m.leader = rid32 L → m.slot = i → m.t = vt.t) ∧
      (G' r L i ≠ .eo → tagLe vt.t.toP (stR c' r).tag.toP) :=
  ph_part' hs hI (by rw [hG]; exact id) (by rw [hG]; exact id) hmsg

theorem lb_part {l l' : List Label} {c c' : Cfg gNet} {G G' : GX} {L : Fin 3} {i : w32}
    (hI : XI l c G L i)
    (hc : phCnt (fun r => G r L i) .done ≤ phCnt (fun r => G' r L i) .done)
    (hrep : Rep l' (rid32 L, i) ↔ Rep l (rid32 L, i))
    (hrep' : Rep l' (rid32 L, i) → 2 ≤ phCnt (fun r => G' r L i) .done)
    (hlb : ∀ v, NumIn (stR c' L) (rid32 L) i v → NumIn (stR c L) (rid32 L) i v ∨ v = (0, false)) :
    ∀ cp lb, (stR c' L).inst (rid32 L) i = some cp → cp.lb = some lb → LBOk l' G' L i lb := by
  intro cp lb hc' hlb'
  rcases hlb _ ⟨cp, lb, hc', hlb', rfl⟩ with ⟨cp0, lb0, hc0, hlb0, he⟩ | h0
  · have := hI.lb cp0 lb0 hc0 hlb0
    have e1 : lb0.numReplicasExecuted = lb.numReplicasExecuted := congrArg Prod.fst he
    have e2 : lb0.repliedClient = lb.repliedClient := congrArg Prod.snd he
    have hok : LBOk l G L i lb := by
      simp only [LBOk] at this ⊢
      rw [← e1, ← e2]; exact this
    exact lbok_mono hok hc hrep
  · exact lbok_fresh hrep' h0

/-- The accounting of `(rid32 L, i)` is kept by a step that does not touch it. -/
theorem xi_frame {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {G G' : GX} {L : Fin 3} {i : w32}
    (hI : XI l c G L i) (hG : ∀ r, G' r L i = G r L i)
    (heo : ∀ r, (infR c' r).countP (isEOx (rid32 L) i) = (infR c r).countP (isEOx (rid32 L) i))
    (hex : (infR c' L).count (exM (rid32 L) i) = (infR c L).count (exM (rid32 L) i))
    (hmsg : ∀ r m, Msg.executeOverwrite m ∈ infR c' r → m.leader = rid32 L → m.slot = i →
      Msg.executeOverwrite m ∈ infR c r)
    (hrep : Rep (l ++ [(a, e)]) (rid32 L, i) ↔ Rep l (rid32 L, i))
    (hlb : ∀ v, NumIn (stR c' L) (rid32 L) i v → NumIn (stR c L) (rid32 L) i v ∨ v = (0, false)) :
    XI (l ++ [(a, e)]) c' G' L i := by
  have hG' : (fun r => G' r L i) = fun r => G r L i := funext hG
  have hrep' : Rep (l ++ [(a, e)]) (rid32 L, i) → 2 ≤ phCnt (fun r => G' r L i) .done := by
    rw [hG']; exact fun h => hI.rep (hrep.1 h)
  refine ⟨fun r => by rw [heo r, hI.eo r, hG r], by rw [hex, hI.ex, hG'], fun r =>
    ph_part hs hI (hG r) (hmsg r), hrep',
    lb_part hI (by rw [hG']; exact Nat.le_refl _) hrep hrep' hlb⟩

/-! ## The leader's `handleExecuted` -/

theorem sge2_iff {x : w32} : sge x 2 = true ↔ 2 ≤ sint.Z x := by
  have : sint.Z (2 : w32) = 2 := by decide
  simp only [sge, sle, decide_eq_true_eq, this]

theorem hx_uniq {e : Ev} {x y : w32 × w32} (hx : HX e x) (hy : HX e y) : x = y := by
  rcases hx with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩ <;>
    rcases hy with ⟨m', he, rfl⟩ | ⟨m', he, rfl⟩ <;> cases he <;> rfl

theorem handleExecuted_tag {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : s'.tag = s.tag := by
  rcases handleExecuted_spec h with ⟨rfl, -⟩ | ⟨c, lb, b, -, -, rfl, -⟩ <;> rfl

theorem handleExecuted_other {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) {q i : w32} (hne : ¬(q = m.replica ∧ i = m.inst)) :
    s'.inst q i = s.inst q i := by
  rcases handleExecuted_spec h with ⟨rfl, -⟩ | ⟨c, lb, b, -, -, rfl, -⟩
  · rfl
  · change (if q = m.replica ∧ i = m.inst then _ else s.inst q i) = _
    rw [if_neg hne]

/-- **The core**: `handleExecuted` at the leader `L` on `(rid32 L, i)`, counting one more
replica (`r0`, now `done`). A reply needs the instance not replied to before. -/
theorem core_hx {l l' : List Label} {c : Cfg gNet} {G : GX} {L r0 : Fin 3} {i : w32}
    (hI : XI l c G L i) (hr0 : G r0 L i ≠ .done) {s0 s' : RState} {o : List Out}
    (hs0 : s0.inst = (stR c L).inst)
    (hh : handleExecuted s0 { replica := rid32 L, inst := i } = .ok (s', o))
    (hrep : Rep l' (rid32 L, i) ↔ Rep l (rid32 L, i) ∨
      ∃ cid rid f, Out.ext (.rmwReply cid rid f) ∈ o) :
    (Rep l' (rid32 L, i) → 2 ≤ phCnt (fun r => gupd G r0 L i .done r L i) .done) ∧
    (∀ cp lb, s'.inst (rid32 L) i = some cp → cp.lb = some lb →
      LBOk l' (gupd G r0 L i .done) L i lb) ∧
    ((∃ cid rid f, Out.ext (.rmwReply cid rid f) ∈ o) → ¬ Rep l (rid32 L, i)) := by
  have hc := cnt_upd3 (fun r => G r L i) r0 .done .done
  simp only [hr0, if_false, if_true] at hc
  have hle := cnt_le2 (f := fun r => G r L i) hr0
  have hrepI := hI.rep
  have hlbI := hI.lb
  simp only [LBOk] at hlbI ⊢
  rw [gupd_same]
  generalize phCnt (fun r => G r L i) .done = C at hc hle hrepI hlbI
  generalize phCnt (upd3 (fun r => G r L i) r0 .done) .done = C' at hc ⊢
  rcases handleExecuted_spec hh with ⟨rfl, rfl⟩ | ⟨c0, lb0, b, hc0, hlb0, rfl, hbr⟩
  · have hr : Rep l' (rid32 L, i) ↔ Rep l (rid32 L, i) := by simpa using hrep
    refine ⟨fun h => by have := hrepI (hr.1 h); omega, ?_, fun ⟨_, _, _, h⟩ => by cases h⟩
    intro cp lb hcp hlb
    rw [hs0] at hcp
    obtain ⟨a1, a2⟩ := hlbI cp lb hcp hlb
    refine ⟨fun h => hr.2 (a1 h), fun h => ?_⟩
    obtain ⟨b1, b2, b3⟩ := a2 h
    exact ⟨b1, by omega, fun h' => by have := b3 (hr.1 h'); omega⟩
  · rw [hs0] at hc0
    obtain ⟨a1, a2⟩ := hlbI c0 lb0 hc0 hlb0
    have hnew : ∀ cp lb, (s0.setInst (rid32 L) i { c0 with lb := some { lb0 with
        numReplicasExecuted := lb0.numReplicasExecuted + 1, repliedClient := b } }).inst
          (rid32 L) i = some cp → cp.lb = some lb →
        lb = { lb0 with numReplicasExecuted := lb0.numReplicasExecuted + 1, repliedClient := b } := by
      intro cp lb hcp hlb
      change (if rid32 L = rid32 L ∧ i = i then some _ else _) = _ at hcp
      rw [if_pos ⟨rfl, rfl⟩] at hcp
      cases hcp; cases hlb; rfl
    rcases hbr with ⟨rfl, rfl, hno⟩ | ⟨hrc, hsge, rfl, p, hp, rfl⟩
    · have hr : Rep l' (rid32 L, i) ↔ Rep l (rid32 L, i) := by simpa using hrep
      refine ⟨fun h => by have := hrepI (hr.1 h); omega, ?_, fun ⟨_, _, _, h⟩ => by cases h⟩
      intro cp lb hcp hlb
      obtain rfl := hnew cp lb hcp hlb
      refine ⟨fun h => hr.2 (a1 h), fun h => ?_⟩
      obtain ⟨b1, b2, b3⟩ := a2 h
      have hz : sint.Z (lb0.numReplicasExecuted + 1) = sint.Z lb0.numReplicasExecuted + 1 :=
        Z_succ32 (by omega)
      simp only [hz]
      exact ⟨by omega, by omega, fun h' => by have := b3 (hr.1 h'); omega⟩
    · obtain ⟨b1, b2, b3⟩ := a2 hrc
      have hz : sint.Z (lb0.numReplicasExecuted + 1) = sint.Z lb0.numReplicasExecuted + 1 :=
        Z_succ32 (by omega)
      have h2 := sge2_iff.1 hsge
      rw [hz] at h2
      have hR : Rep l' (rid32 L, i) := hrep.2 (Or.inr ⟨_, _, _, List.mem_singleton.2 rfl⟩)
      refine ⟨fun _ => by omega, ?_, fun _ h => by have := b3 h; omega⟩
      intro cp lb hcp hlb
      obtain rfl := hnew cp lb hcp hlb
      exact ⟨fun _ => hR, fun h => by cases h⟩

/-! ## Frame, for the instances a step does not touch -/

theorem consume_countP {e : Ev} {f : Msg → Bool} (h : ∀ m, e.recv = some m → f m = false)
    (L : List Msg) : (consume e.recv L).countP f = L.countP f := by
  cases hr : e.recv with
  | none => rfl
  | some m => exact countP_erase_of (h m hr) L

theorem consume_count {e : Ev} {x : Msg} (h : ∀ m, e.recv = some m → m ≠ x) (L : List Msg) :
    (consume e.recv L).count x = L.count x := by
  cases hr : e.recv with
  | none => rfl
  | some m => exact List.count_erase_of_ne (fun h' => h m hr h'.symm)

theorem xi_frame' {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {G G' : GX} {L : Fin 3} {i : w32}
    (hI : XI l c G L i) (hG : ∀ r, G' r L i = G r L i)
    (hrecv : ∀ m, e.recv = some m → isEOx (rid32 L) i m = false ∧ m ≠ exM (rid32 L) i)
    (hsent : ∀ r m, m ∈ sentR r o → isEOx (rid32 L) i m = false ∧ m ≠ exM (rid32 L) i)
    (hrep : Rep (l ++ [(a, e)]) (rid32 L, i) ↔ Rep l (rid32 L, i))
    (hlb : ∀ v, NumIn (stR c' L) (rid32 L) i v → NumIn (stR c L) (rid32 L) i v ∨ v = (0, false)) :
    XI (l ++ [(a, e)]) c' G' L i := by
  refine xi_frame hs hI hG ?_ ?_ ?_ hrep hlb
  · intro r
    have h0 : (sentR r o).countP (isEOx (rid32 L) i) = 0 :=
      List.countP_eq_zero.2 (fun m hm => by simp [(hsent r m hm).1])
    rw [hs.countP_inf, h0, Nat.add_zero]
    split
    · exact consume_countP (fun m hm => (hrecv m hm).1) _
    · rfl
  · have h0 : (sentR L o).count (exM (rid32 L) i) = 0 :=
      List.count_eq_zero.2 (fun hm => (hsent L _ hm).2 rfl)
    rw [hs.count_inf, h0, Nat.add_zero]
    split
    · exact consume_count (fun m hm => (hrecv m hm).2) _
    · rfl
  · intro r m hm h1 h2
    rcases hs.mem hm with h | h
    · exact h
    · have := (hsent r _ h).1; simp [isEOx, h1, h2] at this

theorem lflow_cfg {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) (hlf : LFlow (stR c a) s') (L : Fin 3) (q i : w32) :
    ∀ v, NumIn (stR c' L) q i v → NumIn (stR c L) q i v ∨ v = (0, false) := by
  intro v hv
  by_cases hL : L = a
  · subst hL; rw [hs.sti] at hv; exact hlf q i v hv
  · rw [hs.stj hL] at hv; exact Or.inl hv

theorem rep_noreply {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o)
    (h : ∀ cid rid f, Out.ext (.rmwReply cid rid f) ∉ o) (x : w32 × w32) :
    Rep (l ++ [(a, e)]) x ↔ Rep l x := by
  rw [rep_snoc, repX_last hs.st_a hs.ok]
  constructor
  · rintro (h1 | ⟨-, -, cid, rid, f, h2⟩)
    · exact h1
    · exact absurd h2 (h cid rid f)
  · exact Or.inl

theorem rep_nohx {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {x : w32 × w32} (h : ¬ HX e x) :
    Rep (l ++ [(a, e)]) x ↔ Rep l x := by
  rw [rep_snoc, repX_last hs.st_a hs.ok]
  constructor
  · rintro (h1 | ⟨-, h2, -⟩)
    · exact h1
    · exact absurd h2 h
  · exact Or.inl

/-! ## Steps that are not the executor's nor the run loop's notices -/

theorem xspecial_m {e : Ev} (h : Ev.xspecial e = false) : Ev.mspecial e = false := by
  cases e <;> try rfl
  rename_i m; cases m <;> first | rfl | cases h

theorem xspecial_recv {e : Ev} (h : Ev.xspecial e = false) {m : Msg} (hm : e.recv = some m) :
    isXMsg m = false := by
  cases e with
  | msg m' =>
    simp only [Ev.recv, Option.some.injEq] at hm
    subst hm; cases m' <;> first | rfl | cases h
  | _ => cases hm

theorem noX_isEOx {m : Msg} (h : isXMsg m = false) (q i : w32) : isEOx q i m = false ∧ m ≠ exM q i := by
  cases m <;> simp_all [isXMsg, isEOx, exM]

theorem noM_noreply {o : List Out} (h : NoM o) : ∀ cid rid f, Out.ext (.rmwReply cid rid f) ∉ o :=
  fun _ _ _ hx => by have := h _ hx; simp [isMOut] at this

theorem xinv_A {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {G : GX} (hI : XInv l c G)
    (he : Ev.xspecial e = false) :
    XInv (l ++ [(a, e)]) c' G ∧ ∀ x, RepX (l ++ [(a, e)]) l.length x → ¬ Rep l x := by
  have hnx := step_noX hs.ok he
  have hnr := noM_noreply (step_noM hs.ok (xspecial_m he))
  have hlf := step_lflow hs.ok (xspecial_m he)
  refine ⟨fun L i => xi_frame' hs (hI L i) (fun _ => rfl)
    (fun m hm => noX_isEOx (xspecial_recv he hm) _ _)
    (fun r m hm => noX_isEOx (sentR_noX hnx r m hm) _ _) (rep_noreply hs hnr _)
    (lflow_cfg hs hlf L _ _), fun x hx _ => ?_⟩
  obtain ⟨-, -, cid, rid, f, h⟩ := (repX_last hs.st_a hs.ok).1 hx
  exact hnr cid rid f h

/-! ## The executor -/

theorem eox_eq {L : Fin 3} {i : w32} {m : ExecuteOverwriteM} :
    isEOx (rid32 L) i (.executeOverwrite m) = decide (m.leader = rid32 L ∧ m.slot = i) := rfl

theorem xinv_B {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {q i0 : w32} {s' : RState}
    {o : List Out} (hs : StepAt l c a (.exec q i0) c' s' o) (hAF : AF c) {G : GX} (hI : XInv l c G)
    (hnd : ((execSeq a (projR (l ++ [(a, .exec q i0)]) a)).map Prod.fst).Nodup) :
    ∃ G', XInv (l ++ [(a, .exec q i0)]) c' G' ∧
      ∀ x, RepX (l ++ [(a, .exec q i0)]) l.length x → ¬ Rep l x := by
  have hok : stepExec (stR c a) q i0 = .ok (s', o) := hs.ok
  obtain ⟨c0, hc0, -, -, -, ho⟩ := stepExec_out hok
  have hlf := stepExec_lf hok
  have hnr : ∀ cid rid f, Out.ext (.rmwReply cid rid f) ∉ o := by
    rcases ho with rfl | ⟨d, v, t, -, rfl⟩ <;> simp
  have hnoRep : ∀ x, RepX (l ++ [(a, .exec q i0)]) l.length x → ¬ Rep l x := fun x hx _ => by
    obtain ⟨-, -, cid, rid, f, h⟩ := (repX_last hs.st_a hs.ok).1 hx; exact hnr cid rid f h
  have hrecv : ∀ m, (Ev.exec q i0).recv = some m → False := fun m hm => by cases hm
  rcases ho with rfl | ⟨d, v, t, hd, rfl⟩
  · exact ⟨G, fun L i => xi_frame' hs (hI L i) (fun _ => rfl) (fun m hm => (hrecv m hm).elim)
      (fun r m hm => by simp [sentR] at hm) (rep_noreply hs hnr _) (lflow_cfg hs hlf L _ _), hnoRep⟩
  obtain ⟨⟨L0, rfl⟩, hlead, hslot⟩ := hAF.inst a _ _ c0 hc0
  rw [hAF.id a, dstOf_rid32] at hd
  cases hd
  rw [hlead, hslot] at hs
  rw [hlead, hslot] at hnr
  -- the sent messages
  have hsent : ∀ r, sentR r [Out.send a (.executeOverwrite { v, t, leader := rid32 L0, slot := i0 })] =
      if a = r then [.executeOverwrite { v, t, leader := rid32 L0, slot := i0 }] else [] := by
    intro r; simp only [sentR, List.filterMap_cons, List.filterMap_nil]; split <;> simp_all
  -- the new execution
  have hseq : execSeq a (projR (l ++ [(a, .exec (rid32 L0) i0)]) a) =
      execSeq a (projR l a) ++ [((rid32 L0, i0), ⟨v, t⟩)] := by
    rw [proj_snoc, if_pos rfl, execSeq_snoc_lb a _ _ (by rw [hs.st_a]; exact hs.ok)]
    simp [execRes]
  have hnone : G a L0 i0 = .none := by
    cases hG : G a L0 i0 with
    | none => rfl
    | _ =>
      exfalso
      obtain ⟨vt, hvt, -, -⟩ := (hI L0 i0).ph a (by rw [hG]; exact fun h => by cases h)
      rw [hseq, List.map_append, List.nodup_append] at hnd
      exact hnd.2.2 _ (List.mem_map.2 ⟨_, hvt, rfl⟩) _ (List.mem_singleton.2 rfl) rfl
  refine ⟨gupd G a L0 i0 .eo, fun L i => ?_, hnoRep⟩
  by_cases hx : L = L0 ∧ i = i0
  · obtain ⟨rfl, rfl⟩ := hx
    have hI0 := hI L i
    have hcu := fun p => cnt_upd3 (fun r => G r L i) a .eo p
    simp only [hnone] at hcu
    have hrep := rep_noreply hs hnr (rid32 L, i)
    have hdone : phCnt (fun r => gupd G a L i .eo r L i) .done = phCnt (fun r => G r L i) .done := by
      rw [gupd_same]; have := hcu .done; simpa using this
    refine ⟨fun r => ?_, ?_, fun r => ?_, ?_, ?_⟩
    · rw [hs.countP_inf, hsent r]
      by_cases hr : r = a
      · subst hr
        have := hI0.eo r
        rw [hnone] at this
        change _ = (if Ph.none = Ph.eo then 1 else 0) at this
        simp only [reduceCtorEq, if_false] at this
        rw [if_pos rfl, if_pos rfl, gupd_at]
        change (infR c r).countP _ + _ = _
        rw [this]; simp [eox_eq]
      · rw [if_neg hr, if_neg (Ne.symm hr), List.countP_nil, Nat.add_zero, hI0.eo r,
          gupd_ne _ _ _ _ _ (fun h => hr h.1)]
    · rw [hs.count_inf, hsent L]
      have hc := hcu .ex
      rw [gupd_same]
      have e0 : (if a = L then [Msg.executeOverwrite { v, t, leader := rid32 L, slot := i }]
          else []).count (exM (rid32 L) i) = 0 := by split <;> simp [exM]
      have e1 : (if L = a then consume (Ev.exec (rid32 L) i).recv (infR c L) else infR c L) =
          infR c L := by split <;> rfl
      rw [e0, e1, Nat.add_zero, hI0.ex]
      simpa using hc.symm
    · by_cases hr : r = a
      · subst hr
        intro _
        refine ⟨⟨v, t⟩, by rw [hseq]; simp, fun m hm h1 h2 => ?_, fun h => by
          rw [gupd_at] at h; exact absurd rfl h⟩
        rcases hs.mem hm with hm | hm
        · exfalso
          have hpos := countP_pos_mem (f := isEOx (rid32 L) i) (by simp [eox_eq, h1, h2]) hm
          have := hI0.eo r; rw [hnone] at this
          change _ = (if Ph.none = Ph.eo then 1 else 0) at this
          simp only [reduceCtorEq, if_false] at this
          omega
        · rw [hsent r, if_pos rfl] at hm
          simp only [List.mem_singleton, Msg.executeOverwrite.injEq] at hm
          subst hm; rfl
      · refine ph_part hs hI0 (gupd_ne _ _ _ _ _ (fun h => hr h.1)) (fun m hm h1 h2 => ?_)
        rcases hs.mem hm with h | h
        · exact h
        · rw [hsent r, if_neg (Ne.symm hr)] at h; cases h
    · rw [hdone]; exact fun h => hI0.rep (hrep.1 h)
    · exact lb_part hI0 (by rw [hdone]; exact Nat.le_refl _) hrep
        (by rw [hdone]; exact fun h => hI0.rep (hrep.1 h)) (lflow_cfg hs hlf L _ _)
  · refine xi_frame' hs (hI L i) (fun r => gupd_ne _ _ _ _ _ (fun h => hx ⟨h.2.1, h.2.2⟩))
      (fun m hm => (hrecv m hm).elim) (fun r m hm => ?_) (rep_noreply hs hnr _)
      (lflow_cfg hs hlf L _ _)
    rw [hsent r] at hm
    split at hm
    · simp only [List.mem_singleton] at hm; subst hm
      refine ⟨?_, by simp [exM]⟩
      rw [eox_eq]; simp only [decide_eq_false_iff_not]
      rintro ⟨h1, h2⟩
      exact hx ⟨(rid32_inj h1).symm, h2.symm⟩
    · cases hm

/-! ## The leader's notices -/

theorem hmsg_nosent {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {r : Fin 3} (h : ∀ m, Msg.executeOverwrite m ∉ sentR r o)
    {L i : w32} (m : ExecuteOverwriteM) (hm : Msg.executeOverwrite m ∈ infR c' r)
    (_ : m.leader = L) (_ : m.slot = i) : Msg.executeOverwrite m ∈ infR c r := by
  rcases hs.mem hm with h1 | h1
  · exact h1
  · exact absurd h1 (h m)

theorem sentR_allExt {o : List Out} (h : ∀ x ∈ o, ∃ y, x = .ext y) (r : Fin 3) : sentR r o = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro m hm
  unfold sentR at hm
  obtain ⟨x, hx, hx'⟩ := List.mem_filterMap.1 hm
  obtain ⟨y, rfl⟩ := h x hx
  cases hx'

theorem hlb_hx {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState}
    {o : List Out} (hs : StepAt l c a e c' s' o) {s0 : RState} (hs0 : s0.inst = (stR c a).inst)
    {i0 : w32} (hh : handleExecuted s0 { replica := rid32 a, inst := i0 } = .ok (s', o))
    {L : Fin 3} {i : w32} (hx : ¬(L = a ∧ i = i0)) :
    ∀ v, NumIn (stR c' L) (rid32 L) i v → NumIn (stR c L) (rid32 L) i v ∨ v = (0, false) := by
  intro v hv
  by_cases hL : L = a
  · subst hL
    rw [hs.sti] at hv
    obtain ⟨cp, lb, hc, h2, h3⟩ := hv
    rw [handleExecuted_other hh (fun h => hx ⟨rfl, h.2⟩), hs0] at hc
    exact Or.inl ⟨cp, lb, hc, h2, h3⟩
  · rw [hs.stj hL] at hv; exact Or.inl hv

theorem gupd_eq_iff (G : GX) (r0 L : Fin 3) (i : w32) (p q : Ph) (r : Fin 3) :
    (gupd G r0 L i p r L i = q) ↔ (if r = r0 then p = q else G r L i = q) := by
  simp only [gupd, upd3, and_self, if_true]
  split <;> rfl

theorem xinv_D {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {m : ExecutedM} {s' : RState}
    {o : List Out} (hs : StepAt l c a (.msg (.executed m)) c' s' o) (hAF : AF c) {G : GX}
    (hI : XInv l c G) :
    ∃ G', XInv (l ++ [(a, .msg (.executed m))]) c' G' ∧
      ∀ x, RepX (l ++ [(a, .msg (.executed m))]) l.length x → ¬ Rep l x := by
  have hm := hs.recv _ rfl
  have hrm := hAF.ex a m hm
  obtain ⟨rq, i0⟩ := m
  simp only at hrm; subst hrm
  have hok : handleExecuted (stR c a) { replica := rid32 a, inst := i0 } = .ok (s', o) := hs.ok
  have hsE := sentR_allExt (handleExecuted_ext hok)
  have hI0 := hI a i0
  have hcnt : 0 < phCnt (fun r => G r a i0) .ex := by
    rw [← hI0.ex]; exact List.count_pos_iff.2 hm
  obtain ⟨r0, hr0⟩ := cnt_pos hcnt
  have hr0d : G r0 a i0 ≠ .done := by rw [hr0]; exact fun h => by cases h
  have hrepq : Rep (l ++ [(a, .msg (.executed { replica := rid32 a, inst := i0 }))]) (rid32 a, i0) ↔
      Rep l (rid32 a, i0) ∨ ∃ cid rid f, Out.ext (.rmwReply cid rid f) ∈ o := by
    rw [rep_snoc, repX_last hs.st_a hs.ok]
    constructor
    · rintro (h | ⟨-, -, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Or.inl ⟨_, rfl, rfl⟩, h⟩
  have hcore := core_hx hI0 hr0d rfl hok hrepq
  have hhx : ∀ x, HX (.msg (.executed { replica := rid32 a, inst := i0 })) x → x = (rid32 a, i0) :=
    fun x hx => hx_uniq hx (Or.inl ⟨_, rfl, rfl⟩)
  have hnoRep : ∀ x, RepX (l ++ [(a, .msg (.executed { replica := rid32 a, inst := i0 }))])
      l.length x → ¬ Rep l x := fun x hx => by
    obtain ⟨-, h2, h3⟩ := (repX_last hs.st_a hs.ok).1 hx
    rw [hhx x h2]; exact hcore.2.2 h3
  refine ⟨gupd G r0 a i0 .done, fun L i => ?_, hnoRep⟩
  by_cases hx : L = a ∧ i = i0
  · obtain ⟨rfl, rfl⟩ := hx
    have hcu := fun p => cnt_upd3 (fun r => G r L i) r0 .done p
    simp only [hr0] at hcu
    refine ⟨fun r => ?_, ?_, fun r => ?_, hcore.1, ?_⟩
    · rw [hs.countP_inf, hsE, List.countP_nil, Nat.add_zero]
      have e1 : (if r = L then consume (Ev.msg (.executed { replica := rid32 L, inst := i })).recv
          (infR c r) else infR c r).countP (isEOx (rid32 L) i) = (infR c r).countP (isEOx (rid32 L) i) := by
        split
        · exact countP_erase_of rfl _
        · rfl
      rw [e1, hI0.eo r]
      by_cases hr : r = r0
      · subst hr; rw [gupd_at, hr0]; rfl
      · rw [gupd_ne _ _ _ _ _ (fun h => hr h.1)]
    · rw [hs.count_inf, hsE, if_pos rfl, gupd_same]
      change ((infR c L).erase (exM (rid32 L) i)).count (exM (rid32 L) i) + 0 = _
      rw [List.count_erase_self, hI0.ex]
      have := hcu .ex
      simp only [reduceCtorEq, if_false, if_true] at this
      omega
    · by_cases hr : r = r0
      · subst hr
        refine ph_part' hs hI0 (fun _ => by rw [hr0]; exact fun h => by cases h)
          (fun _ => by rw [hr0]; exact fun h => by cases h)
          (hmsg_nosent hs (fun m h => by rw [hsE] at h; cases h))
      · exact ph_part hs hI0 (gupd_ne _ _ _ _ _ (fun h => hr h.1))
          (hmsg_nosent hs (fun m h => by rw [hsE] at h; cases h))
    · intro cp lb hc hlb
      rw [hs.sti] at hc
      exact hcore.2.1 cp lb hc hlb
  · refine xi_frame' hs (hI L i) (fun r => gupd_ne _ _ _ _ _ (fun h => hx ⟨h.2.1, h.2.2⟩))
      (fun m hm => ?_) (fun r m hm => by rw [hsE] at hm; cases hm)
      (rep_nohx hs (fun h => hx ?_)) (hlb_hx hs rfl hok hx)
    · simp only [Ev.recv, Option.some.injEq] at hm
      subst hm
      refine ⟨rfl, fun h => hx ?_⟩
      simp only [exM, Msg.executed.injEq, ExecutedM.mk.injEq] at h
      exact ⟨rid32_inj h.1.symm, h.2.symm⟩
    · have := hhx _ h
      simp only [Prod.mk.injEq] at this
      exact ⟨rid32_inj this.1, this.2⟩

theorem ow_lflow (s : RState) (v : w64) (t : model.Tag) : LFlow s (s.overwrite v t) :=
  lflow_same (LFlow.rfl' s) (tot.ow_inst ..)

theorem xinv_C {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {m : ExecuteOverwriteM} {s' : RState}
    {o : List Out} (hs : StepAt l c a (.msg (.executeOverwrite m)) c' s' o) (hAF : AF c) {G : GX}
    (hI : XInv l c G) :
    ∃ G', XInv (l ++ [(a, .msg (.executeOverwrite m))]) c' G' ∧
      ∀ x, RepX (l ++ [(a, .msg (.executeOverwrite m))]) l.length x → ¬ Rep l x := by
  have hm := hs.recv _ rfl
  obtain ⟨L0, hL0⟩ := hAF.eo a m hm
  obtain ⟨v, t, ld, i0⟩ := m
  simp only at hL0; subst hL0
  have hI0 := hI L0 i0
  have hpos : 0 < (infR c a).countP (isEOx (rid32 L0) i0) :=
    countP_pos_mem (by simp [eox_eq]) hm
  have hGa : G a L0 i0 = .eo := by
    have := hI0.eo a; rw [this] at hpos
    revert hpos; split
    · intro _; assumption
    · intro h; exact absurd h (by decide)
  obtain ⟨vt, hvt, hmt, -⟩ := hI0.ph a (by rw [hGa]; exact fun h => by cases h)
  have hmt' : t = vt.t := hmt _ hm rfl rfl
  have hEOx : ∀ L i, ¬(L = L0 ∧ i = i0) → isEOx (rid32 L) i
      (.executeOverwrite { v, t, leader := rid32 L0, slot := i0 }) = false := by
    intro L i hx; rw [eox_eq]; simp only [decide_eq_false_iff_not]
    rintro ⟨h1, h2⟩; exact hx ⟨rid32_inj h1.symm, h2.symm⟩
  have hhx : ∀ x, HX (.msg (.executeOverwrite { v, t, leader := rid32 L0, slot := i0 })) x →
      x = (rid32 L0, i0) := fun x hx => hx_uniq hx (Or.inr ⟨_, rfl, rfl⟩)
  have hcntA : ∀ r, ((if r = a then consume (Ev.msg (.executeOverwrite
      { v, t, leader := rid32 L0, slot := i0 })).recv (infR c r) else infR c r).countP
        (isEOx (rid32 L0) i0)) + (if r = a then 1 else 0) = (infR c r).countP (isEOx (rid32 L0) i0) := by
    intro r; split
    · rename_i hr; subst hr; exact countP_erase_mem (by simp [eox_eq]) hm
    · rfl
  have hcntO : ∀ L i, ¬(L = L0 ∧ i = i0) → ∀ r, ((if r = a then consume (Ev.msg (.executeOverwrite
      { v, t, leader := rid32 L0, slot := i0 })).recv (infR c r) else infR c r).countP
        (isEOx (rid32 L) i)) = (infR c r).countP (isEOx (rid32 L) i) := by
    intro L i hx r; split
    · exact countP_erase_of (hEOx L i hx) _
    · rfl
  have hcntX : ∀ L i r, ((if r = a then consume (Ev.msg (.executeOverwrite
      { v, t, leader := rid32 L0, slot := i0 })).recv (infR c r) else infR c r).count
        (exM (rid32 L) i)) = (infR c r).count (exM (rid32 L) i) := by
    intro L i r; split
    · exact List.count_erase_of_ne (by simp [exM])
    · rfl
  have htag : ∀ s1 : RState, s1.tag = ((stR c a).overwrite v t).tag → tagLe vt.t.toP s1.tag.toP := by
    intro s1 h1; rw [h1, ← hmt']; exact (overwrite_tag _ _ _).2
  rcases stepEO_spec hs.ok with ⟨hself, hh⟩ | ⟨hne, rfl, d, hd, rfl⟩
  · -- to self: the leader counts itself
    simp only at hself
    rw [hAF.id a] at hself
    obtain rfl := rid32_inj hself
    have hok : handleExecuted ((stR c L0).overwrite v t) { replica := rid32 L0, inst := i0 } =
        .ok (s', o) := hh
    have hsE := sentR_allExt (handleExecuted_ext hok)
    have hrepq : Rep (l ++ [(L0, .msg (.executeOverwrite { v, t, leader := rid32 L0, slot := i0 }))])
        (rid32 L0, i0) ↔ Rep l (rid32 L0, i0) ∨ ∃ cid rid f, Out.ext (.rmwReply cid rid f) ∈ o := by
      rw [rep_snoc, repX_last hs.st_a hs.ok]
      constructor
      · rintro (h | ⟨-, -, h⟩)
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inr ⟨_, rfl, rfl⟩, h⟩
    have hcore := core_hx hI0 (r0 := L0) (by rw [hGa]; exact fun h => by cases h)
      (tot.ow_inst ..) hok hrepq
    have hnoRep : ∀ x, RepX (l ++ [(L0, .msg (.executeOverwrite
        { v, t, leader := rid32 L0, slot := i0 }))]) l.length x → ¬ Rep l x := fun x hx => by
      obtain ⟨-, h2, h3⟩ := (repX_last hs.st_a hs.ok).1 hx
      rw [hhx x h2]; exact hcore.2.2 h3
    refine ⟨gupd G L0 L0 i0 .done, fun L i => ?_, hnoRep⟩
    by_cases hx : L = L0 ∧ i = i0
    · obtain ⟨rfl, rfl⟩ := hx
      have hcu := fun p => cnt_upd3 (fun r => G r L i) L .done p
      simp only [hGa] at hcu
      refine ⟨fun r => ?_, ?_, fun r => ?_, hcore.1, ?_⟩
      · rw [hs.countP_inf, hsE, List.countP_nil, Nat.add_zero]
        by_cases hr : r = L
        · subst hr
          rw [if_pos rfl, gupd_at]
          have h1 := countP_erase_mem (f := isEOx (rid32 r) i) (by simp [eox_eq]) hm
          rw [hI0.eo r, hGa] at h1
          change ((infR c r).erase _).countP _ = _
          simp only [reduceCtorEq, if_false, if_true] at h1 ⊢
          omega
        · rw [if_neg hr, gupd_ne _ _ _ _ _ (fun h => hr h.1), hI0.eo r]
      · rw [hs.count_inf, hsE, List.count_nil, Nat.add_zero, hcntX, hI0.ex, gupd_same]
        have := hcu .ex
        simp only [reduceCtorEq, if_false] at this
        omega
      · by_cases hr : r = L
        · subst hr
          intro _
          refine ⟨vt, hs.exec_mono hvt, fun m' hm' a1 a2 =>
            hmt m' (hmsg_nosent hs (fun m h => by rw [hsE] at h; cases h) m' hm' a1 a2) a1 a2,
            fun _ => ?_⟩
          rw [hs.sti]; exact htag s' (handleExecuted_tag hok)
        · exact ph_part hs hI0 (gupd_ne _ _ _ _ _ (fun h => hr h.1))
            (hmsg_nosent hs (fun m h => by rw [hsE] at h; cases h))
      · intro cp lb hc hlb
        rw [hs.sti] at hc
        exact hcore.2.1 cp lb hc hlb
    · refine xi_frame' hs (hI L i) (fun r => gupd_ne _ _ _ _ _ (fun h => hx ⟨h.2.1, h.2.2⟩))
        (fun m hm => ?_) (fun r m hm => by rw [hsE] at hm; cases hm)
        (rep_nohx hs (fun h => hx ?_)) (hlb_hx hs (tot.ow_inst ..) hok hx)
      · simp only [Ev.recv, Option.some.injEq] at hm
        subst hm
        exact ⟨hEOx L i hx, by simp [exM]⟩
      · have := hhx _ h
        simp only [Prod.mk.injEq] at this
        exact ⟨rid32_inj this.1, this.2⟩
  · -- to the leader: an `Executed`
    have hLa : L0 ≠ a := fun h => hne (by simp only; rw [hAF.id a, h])
    rw [dstOf_rid32] at hd
    cases hd
    have hsent : ∀ r, sentR r [Out.send L0 (exM (rid32 L0) i0)] =
        if L0 = r then [exM (rid32 L0) i0] else [] := by
      intro r; simp only [sentR, List.filterMap_cons, List.filterMap_nil]; split <;> simp_all
    have hnr : ∀ cid rid f, Out.ext (Ext.rmwReply cid rid f) ∉ [Out.send L0 (exM (rid32 L0) i0)] := by
      simp
    have hlf := lflow_cfg hs (ow_lflow (stR c a) v t)
    refine ⟨gupd G a L0 i0 .ex, fun L i => ?_, fun x hx _ => ?_⟩
    · by_cases hx : L = L0 ∧ i = i0
      · obtain ⟨rfl, rfl⟩ := hx
        have hcu := fun p => cnt_upd3 (fun r => G r L i) a .ex p
        simp only [hGa] at hcu
        have hrep := rep_noreply hs hnr (rid32 L, i)
        have hdone : phCnt (fun r => gupd G a L i .ex r L i) .done = phCnt (fun r => G r L i) .done := by
          rw [gupd_same]; have := hcu .done; simpa using this
        refine ⟨fun r => ?_, ?_, fun r => ?_, ?_, ?_⟩
        · rw [hs.countP_inf, hsent r]
          by_cases hr : r = a
          · subst hr
            rw [if_pos rfl, if_neg hLa, List.countP_nil, Nat.add_zero, gupd_at]
            have h1 := countP_erase_mem (f := isEOx (rid32 L) i) (by simp [eox_eq]) hm
            rw [hI0.eo r, hGa] at h1
            change ((infR c r).erase _).countP _ = _
            simp only [reduceCtorEq, if_false, if_true] at h1 ⊢
            omega
          · have e0 : (if L = r then [exM (rid32 L) i] else []).countP (isEOx (rid32 L) i) = 0 := by
              split <;> simp [exM, isEOx]
            rw [if_neg hr, e0, Nat.add_zero, gupd_ne _ _ _ _ _ (fun h => hr h.1), hI0.eo r]
        · have e1 : (if L = a then consume (Ev.msg (.executeOverwrite
              { v, t, leader := rid32 L, slot := i })).recv (infR c L) else infR c L) = infR c L :=
            if_neg hLa
          rw [hs.count_inf, hsent L, e1, if_pos rfl, gupd_same, hI0.ex]
          have := hcu .ex
          simp only [reduceCtorEq, if_false, if_true] at this
          simp only [exM, List.count_singleton_self]
          omega
        · by_cases hr : r = a
          · subst hr
            intro _
            refine ⟨vt, hs.exec_mono hvt, fun m' hm' a1 a2 => hmt m' (hmsg_nosent hs (fun m h => by
              rw [hsent r, if_neg hLa] at h; cases h) m' hm' a1 a2) a1 a2, fun _ => ?_⟩
            rw [hs.sti]; exact htag _ rfl
          · exact ph_part hs hI0 (gupd_ne _ _ _ _ _ (fun h => hr h.1))
              (hmsg_nosent hs (fun m h => by
                rw [hsent r] at h; split at h <;> simp [exM] at h))
        · rw [hdone]; exact fun h => hI0.rep (hrep.1 h)
        · exact lb_part hI0 (by rw [hdone]; exact Nat.le_refl _) hrep
            (by rw [hdone]; exact fun h => hI0.rep (hrep.1 h)) (hlf L _ _)
      · refine xi_frame' hs (hI L i) (fun r => gupd_ne _ _ _ _ _ (fun h => hx ⟨h.2.1, h.2.2⟩))
          (fun m hm => ?_) (fun r m hm => ?_) (rep_noreply hs hnr _) (hlf L _ _)
        · simp only [Ev.recv, Option.some.injEq] at hm
          subst hm
          exact ⟨hEOx L i hx, by simp [exM]⟩
        · rw [hsent r] at hm
          split at hm
          · simp only [List.mem_singleton] at hm; subst hm
            refine ⟨by simp [exM, isEOx], fun h => hx ?_⟩
            simp only [exM, Msg.executed.injEq, ExecutedM.mk.injEq] at h
            exact ⟨rid32_inj h.1.symm, h.2.symm⟩
          · cases hm
    · obtain ⟨-, -, cid, rid, f, h⟩ := (repX_last hs.st_a hs.ok).1 hx
      exact hnr cid rid f h

/-! ## Along a run -/

theorem xinv_step {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hst : GStep c a e c' x) {G : GX} (hI : XInv l c G) :
    ∃ G', XInv (l ++ [(a, e)]) c' G' ∧ ∀ y, RepX (l ++ [(a, e)]) l.length y → ¬ Rep l y := by
  obtain ⟨s', o, hs⟩ := StepAt.of h hst
  have hAF := af_of h
  cases hx : Ev.xspecial e with
  | false => exact ⟨G, xinv_A hs hI hx⟩
  | true =>
    cases e with
    | exec q i0 => exact xinv_B hs hAF hI (exec_nodup (grun_snoc h hst) a)
    | msg m =>
      cases m with
      | executed m => exact xinv_D hs hAF hI
      | executeOverwrite m => exact xinv_C hs hAF hI
      | _ => cases hx
    | _ => cases hx

theorem xinv_init : XInv [] (Cfg.init gNet) (fun _ _ _ => .none) := by
  intro L i
  refine ⟨fun r => rfl, rfl, fun r h => absurd rfl h, fun ⟨n, hn⟩ => ?_, fun cp lb hc => ?_⟩
  · obtain ⟨_, _, h1, -⟩ := hn; cases h1
  · change (RState.init L.val).inst (rid32 L) i = some cp at hc
    cases hc

/-- **The executed accounting holds along every run.** -/
theorem xinv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : ∃ G, XInv l c G :=
  grun_inv (fun l c => ∃ G, XInv l c G) ⟨_, xinv_init⟩
    (fun _ _ _ _ _ _ h hI hs => by
      obtain ⟨G, hI⟩ := hI
      obtain ⟨G', h1, -⟩ := xinv_step h hs hI
      exact ⟨G', h1⟩) l c h

/-- **An instance's reply is not repeated**: a step replying to `y` finds it not replied to. -/
theorem rep_new {l : List Label} {c c' : Cfg gNet} {a : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hst : GStep c a e c' x) {y : w32 × w32}
    (hy : RepX (l ++ [(a, e)]) l.length y) : ¬ Rep l y := by
  obtain ⟨G, hI⟩ := xinv h
  obtain ⟨G', -, h2⟩ := xinv_step h hst hI
  exact h2 y hy

/-- **At a reply, two distinct replicas executed the instance with a result at most their
stores.** -/
theorem rep_two {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {L : Fin 3}
    {i : w32} (hr : Rep l (rid32 L, i)) :
    ∃ r1 r2 vt1 vt2, r1 ≠ r2 ∧ ((rid32 L, i), vt1) ∈ execSeq r1 (projR l r1) ∧
      ((rid32 L, i), vt2) ∈ execSeq r2 (projR l r2) ∧
      tagLe vt1.t.toP (stR c r1).tag.toP ∧ tagLe vt2.t.toP (stR c r2).tag.toP := by
  obtain ⟨G, hI⟩ := xinv h
  obtain ⟨r1, r2, hne, h1, h2⟩ := cnt_two ((hI L i).rep hr)
  have hn : ∀ r, G r L i = .done → G r L i ≠ .none := fun r h => by rw [h]; exact fun h => by cases h
  have he : ∀ r, G r L i = .done → G r L i ≠ .eo := fun r h => by rw [h]; exact fun h => by cases h
  obtain ⟨vt1, m1, -, t1⟩ := (hI L i).ph r1 (hn r1 h1)
  obtain ⟨vt2, m2, -, t2⟩ := (hI L i).ph r2 (hn r2 h2)
  exact ⟨r1, r2, vt1, vt2, hne, m1, m2, t1 (he r1 h1), t2 (he r2 h2)⟩

end Perennial.gryff.pure
