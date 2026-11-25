/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/Steps2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: the tag bound kept by the coordinator's record handlers (`rops`, `wops`), the client
requests, and the executor.
-/
module

public import Dsverify.Proof.gryff.PureLa.Steps
public import Dsverify.Proof.gryff.PureLa.Count
public import Dsverify.Proof.gryff.PureLa.NReqs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

namespace AMap
theorem mem_of_get? {n : Nat} {V : Type} {m : model.AMap n V} {k : BitVec n} {v : V}
    (h : m.get? k = some v) : (k, v) ∈ m := by
  obtain ⟨l1, l2, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

theorem mem_put {n : Nat} {V : Type} {m : model.AMap n V} {k : BitVec n} {v : V} {e : BitVec n × V}
    (h : e ∈ m.put k v) : e = (k, v) ∨ e ∈ m := by
  induction m with
  | nil => simp [model.AMap.put] at h; exact Or.inl h
  | cons x t ih =>
    obtain ⟨k0, v0⟩ := x
    unfold model.AMap.put at h
    split at h
    · simp at h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · split at h
      · simp at h; rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
        · exact Or.inr (by simp [h])
      · simp at h; rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by simp [h'])

theorem mem_del {n : Nat} {V : Type} {m : model.AMap n V} {k : BitVec n} {e : BitVec n × V}
    (h : e ∈ m.del k) : e ∈ m := (List.mem_filter.1 h).1
end AMap

theorem SB.of_rops {T E : Int} {s s' : RState} (h : SB T E s) (e1 : s'.tag = s.tag)
    (e2 : s'.prevValTag = s.prevValTag) (e3 : s'.inst = s.inst) (e4 : s'.wops = s.wops)
    (hr : ∀ e ∈ s'.rops, ROB T E e.2) : SB T E s' where
  tag := e1 ▸ h.tag
  pvt := e2 ▸ h.pvt
  inst := e3 ▸ h.inst
  wops := e4 ▸ h.wops
  rops := hr

theorem SB.of_wops {T E : Int} {s s' : RState} (h : SB T E s) (e1 : s'.tag = s.tag)
    (e2 : s'.prevValTag = s.prevValTag) (e3 : s'.inst = s.inst) (e5 : s'.rops = s.rops)
    (hw : ∀ e ∈ s'.wops, WOB T E e.2) : SB T E s' where
  tag := e1 ▸ h.tag
  pvt := e2 ▸ h.pvt
  inst := e3 ▸ h.inst
  wops := hw
  rops := e5 ▸ h.rops

theorem wops_put {T E : Int} {m : model.AMap 64 WriteOp} (h : ∀ e ∈ m, WOB T E e.2) {k : w64}
    {r : WriteOp} (hr : WOB T E r) : ∀ e ∈ m.put k r, WOB T E e.2 := by
  intro e he; rcases AMap.mem_put he with rfl | he
  · exact hr
  · exact h e he

theorem wops_del {T E : Int} {m : model.AMap 64 WriteOp} (h : ∀ e ∈ m, WOB T E e.2) {k : w64} :
    ∀ e ∈ m.del k, WOB T E e.2 := fun e he => h e (AMap.mem_del he)

theorem WOB_get {T E : Int} {s : RState} (h : SB T E s) {k : w64} {r : WriteOp}
    (hr : s.wops.get? k = some r) : WOB T E r := h.wops _ (AMap.mem_of_get? hr)

/-- A write record not yet past its `Write2` round. -/
def fW (w : WriteOp) : Bool := !w.sentWrite2Round

/-- The `ts` potential of a replica: its client requests minus its write records that have not
chosen their `WriteTag`. -/
def Pot (s : RState) : Int := (s.nReqs : Int) - (cnt fW s.wops : Int)

theorem ROB_get {T E : Int} {s : RState} (h : SB T E s) {k : w64} {r : ReadOp}
    (hr : s.rops.get? k = some r) : ROB T E r := h.rops _ (AMap.mem_of_get? hr)

theorem rops_put {T E : Int} {m : model.AMap 64 ReadOp} (h : ∀ e ∈ m, ROB T E e.2) {k : w64}
    {r : ReadOp} (hr : ROB T E r) : ∀ e ∈ m.put k r, ROB T E e.2 := by
  intro e he; rcases AMap.mem_put he with rfl | he
  · exact hr
  · exact h e he

theorem rops_del {T E : Int} {m : model.AMap 64 ReadOp} (h : ∀ e ∈ m, ROB T E e.2) {k : w64} :
    ∀ e ∈ m.del k, ROB T E e.2 := fun e he => h e (AMap.mem_del he)

set_option hygiene false in
macro "rob" : tactic => `(tactic| (refine ⟨?_, ?_⟩ <;> (intro v hv; dsimp only at hv; first
  | (cases hv; assumption)
  | exact hrd.1 v hv
  | exact hrd.2 v hv)))

set_option hygiene false in
macro "rd" : tactic => `(tactic| first
  | exact SB.of_rops hs rfl rfl rfl rfl (rops_del hs.rops)
  | exact SB.of_rops hso rfl rfl rfl rfl (rops_del hso.rops)
  | (refine SB.of_rops hs rfl rfl rfl rfl (rops_put hs.rops ?_); rob)
  | (refine SB.of_rops hso rfl rfl rfl rfl (rops_put hso.rops ?_); rob)
  | exact hs
  | exact hso)

theorem Z_succ32' {x : w32} (h1 : sint.Z x < 2 ^ 31 - 1) : sint.Z (x + 1) = sint.Z x + 1 := by
  simp only [sint.Z] at *
  rw [BitVec.toInt_add]
  have := BitVec.toInt_le (x := x); have := BitVec.le_toInt (x := x)
  simp [Int.bmod]; omega

theorem slt_sge_false {x : w64} (h1 : slt x 0 = true) (h2 : sge x 0 = true) : False := by
  simp only [slt, sge, sle, decide_eq_true_eq] at h1 h2; omega

theorem shortCircuit_sb {T E : Int} {s s' : RState} {n : w32} {v : ValTag} {f : Bool}
    {o : List Out} (hs : SB T E s) (h : shortCircuit s n v f = some (s', o)) :
    SB T E s' ∧ OB T E o ∧ s'.wops = s.wops ∧ s'.nReqs = s.nReqs := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · exact ⟨hs, OB_nil, rfl, rfl⟩
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => SB T E p.1 ∧ OB T E p.2 ∧
      p.1.wops = s.wops ∧ p.1.nReqs = s.nReqs)
      ⟨SB.of_rops hs rfl rfl rfl rfl hs.rops, OB_nil, rfl, rfl⟩ ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf)
    all_goals first
      | exact hb
      | exact ⟨hb.1, OB_append hb.2.1 OB_ext, hb.2.2⟩
      | exact ⟨SB.of_rops hb.1 rfl rfl rfl rfl (rops_del hb.1.rops), OB_append hb.2.1 OB_ext, hb.2.2⟩

theorem shortCircuit_ite_sb {T E : Int} {s s' : RState} {c : Prop} [Decidable c] {n : w32}
    {v : ValTag} {f : Bool} {o : List Out} (hs : SB T E s)
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) :
    SB T E s' ∧ OB T E o ∧ s'.wops = s.wops ∧ s'.nReqs = s.nReqs := by
  split at h
  · exact shortCircuit_sb hs h
  · cases h; exact ⟨hs, OB_nil, rfl, rfl⟩

theorem pot_put {s s' : RState} {K : w64} {w w' : WriteOp} (hsrt : Srt s.wops)
    (hg : s.wops.get? K = some w) (hn : s'.nReqs = s.nReqs) (hw : s'.wops = s.wops.put K w') :
    Pot s' + g1 fW (some w') = Pot s + g1 fW (some w) := by
  have := cnt_put fW hsrt K w'
  rw [hg] at this
  unfold Pot; rw [hn, hw]; omega

theorem pot_del {s s' : RState} {K : w64} (hsrt : Srt s.wops) (hn : s'.nReqs = s.nReqs)
    (hw : s'.wops = s.wops.del K) : Pot s ≤ Pot s' := by
  have := cnt_del fW hsrt K
  unfold Pot; rw [hn, hw]; omega

theorem pot_put_same {s s' : RState} {K : w64} {w w' : WriteOp} (hsrt : Srt s.wops)
    (hg : s.wops.get? K = some w) (hn : s'.nReqs = s.nReqs) (hw : s'.wops = s.wops.put K w')
    (hf : w'.sentWrite2Round = w.sentWrite2Round) : Pot s' = Pot s := by
  have := pot_put hsrt hg hn hw
  have e : g1 fW (some w') = g1 fW (some w) := by simp [g1, fW, hf]
  omega

theorem pot_put_choice {s s' : RState} {K : w64} {w w' : WriteOp} (hsrt : Srt s.wops)
    (hg : s.wops.get? K = some w) (hn : s'.nReqs = s.nReqs) (hw : s'.wops = s.wops.put K w')
    (hf : (!w.sentWrite2Round) = true) (hf' : w'.sentWrite2Round = true) : Pot s' = Pot s + 1 := by
  have := pot_put hsrt hg hn hw
  have e1 : g1 fW (some w') = 0 := by simp [g1, fW, hf']
  have e2 : g1 fW (some w) = 1 := by simp [g1, fW]; simpa using hf
  omega

theorem pot_choice_le {T : Int} {s s' : RState} {K : w64} {w w' : WriteOp} (hsrt : Srt s.wops)
    (hg : s.wops.get? K = some w) (hf : (!w.sentWrite2Round) = true) (hn : s'.nReqs = s.nReqs)
    (hw : s'.wops = s.wops.put K w') (hf' : w'.sentWrite2Round = true) :
    T + 1 - T ≤ Pot s' - Pot s := by
  rw [pot_put_choice hsrt hg hn hw hf hf']; omega

theorem pot_same_le {T : Int} {s s' : RState} {K : w64} {w w' : WriteOp} (hsrt : Srt s.wops)
    (hg : s.wops.get? K = some w) (hn : s'.nReqs = s.nReqs)
    (hw : s'.wops = s.wops.put K w') (hf : w'.sentWrite2Round = w.sentWrite2Round) :
    T - T ≤ Pot s' - Pot s := by
  rw [pot_put_same hsrt hg hn hw hf]; omega

theorem pot_del' {s s0 s' : RState} {K : w64} (hn0 : s0.nReqs = s.nReqs) (hw0 : s0.wops = s.wops)
    (hsrt : Srt s.wops) (hn : s'.nReqs = s0.nReqs) (hw : s'.wops = s0.wops.del K) :
    Pot s ≤ Pot s' := by
  rw [hw0] at hw; rw [hn0] at hn
  exact pot_del hsrt hn hw

theorem TB_rsucc {T E : Int} {t : model.Tag} (h : TB T E t) (hE2 : E < 2 ^ 31 - 2) :
    TB T (E + 1) { t with rmwc := t.rmwc + 1 } := by
  have h1 := h.r0; have h2 := h.r1
  have e : sint.Z (t.rmwc + 1) = sint.Z t.rmwc + 1 := Z_succ32' (by omega)
  exact ⟨h.ts0, h.ts1, by simp only [e]; omega, by simp only [e]; omega⟩

theorem pot_req {T : Int} {s s' : RState} {K : w64} {w' : WriteOp} (hsrt : Srt s.wops)
    (hn : s'.nReqs = s.nReqs + 1) (hw : s'.wops = s.wops.put K w') : T - T ≤ Pot s' - Pot s := by
  have := cnt_put fW hsrt K w'
  have e1 : g1 fW (some w') ≤ 1 := by simp only [g1]; split <;> omega
  unfold Pot; rw [hn, hw]; push_cast; omega

theorem pot_req' {T : Int} {s s' : RState} (hn : s'.nReqs = s.nReqs + 1) (hw : s'.wops = s.wops) :
    T - T ≤ Pot s' - Pot s := by
  unfold Pot; rw [hn, hw]; push_cast; omega

theorem guard_slt {k : w64} {d : Dep} {cid : w32}
    (h : ¬(!(k == 0 && slt d.key 0 && sge cid 0)) = true) : slt d.key 0 = true := by
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at h; exact h.1.2

theorem stepExec_shape {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) :
    ∃ c, s.inst q i = some c ∧
      ((o = [] ∧ s' = s.setInst q i { c with status := St.EXECUTED }) ∨
       ∃ vt0 : ValTag, (vt0 = c.base ∨ ∃ pvt, s.prevValTag = some pvt ∧ vt0 = pvt) ∧
         ∃ (m : ExecuteOverwriteM) (d : Fin 3), o = [.send d (.executeOverwrite m)] ∧
           m.t = { vt0.t with rmwc := vt0.t.rmwc + 1 } ∧
           s' = ({ s with prevValTag := some ⟨m.v, m.t⟩ } : RState).setInst
             q i { c with status := St.EXECUTED }) := by
  unfold stepExec at h
  peel h
  · cases h; exact ⟨_, ‹_›, Or.inl ⟨rfl, rfl⟩⟩
  all_goals (
    cases h
    obtain ⟨d, -, rfl⟩ := sendTo_out ‹sendTo _ _ = some _›
    rename Copy => c
    refine ⟨c, ‹_›, Or.inr ⟨(match s.prevValTag with
      | none => c.base
      | some pvt => if c.base.t.gt pvt.t = true then c.base else pvt), ?_, _, d, rfl, ?_, ?_⟩⟩
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr ⟨_, ‹_›, rfl⟩
    all_goals (repeat' split) <;> simp_all)

theorem sub_self_le_of {T a b : Int} (h : a ≤ b) : T - T ≤ b - a := by omega

theorem TB_succ {T E : Int} {t : model.Tag} (h : TB T E t) (h72 : T ≤ 72) (hE : 0 ≤ E) {c : w32} :
    TB (T + 1) E ⟨t.ts + 1, c, 0⟩ := by
  have h1 := h.ts0; have h2 := h.ts1
  have e : sint.Z (t.ts + 1) = sint.Z t.ts + 1 := Z_succ32' (by omega)
  have z : sint.Z (0 : w32) = 0 := by decide
  exact ⟨by simp only [e]; omega, by simp only [e]; omega, by simp only [z]; omega,
    by simp only [z]; omega⟩

section
variable {T E : Int} {s s' : RState} {o : List Out} (hs : SB T E s) (hT : 0 ≤ T) (hE : 0 ≤ E)
include hs hT hE

theorem stepRead1Reply_tb {m : Read1ReplyM} (hm : MB T E (.read1Reply m))
    (h : stepRead1Reply s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; have hso := SB.overwrite hs hm (v := m.vt.v)
  unfold stepRead1Reply at h; peel h
  all_goals (cases h; try have hrd := ROB_get hs ‹_›)
  all_goals (try have hrv := hrd.2 _ (by assumption))
  all_goals (try have hrv' := hrd.1 _ (by assumption))
  all_goals (refine ⟨?_, ?_⟩)
  all_goals first | ob | rd

theorem stepRead2Reply_tb {m : Read2ReplyM}
    (h : stepRead2Reply s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  have hso := hs
  unfold stepRead2Reply at h; peel h
  all_goals (cases h; try have hrd := ROB_get hs ‹_›)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals first | ob | rd

theorem stepWrite1_tb {m : Write1ProxiedM} (hm : MB T E (.write1 m))
    (h : stepWrite1 s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm
  unfold stepWrite1 at h; peel h
  all_goals (try (exfalso; exact slt_sge_false hm ‹_›))
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | ob | sb
end

section
variable {T E : Int} {s s' : RState} {o : List Out} (hs : SB T E s) (hT : 0 ≤ T) (hE : 0 ≤ E)
  (hT72 : T ≤ 72) (hsrt : Srt s.wops)
include hs hT hE hT72 hsrt

theorem stepWrite1Reply_tb {m : Write1ReplyM} (hm : MB T E (.write1Reply m))
    (h : stepWrite1Reply s m = .ok (s', o)) :
    ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧ Srt s'.wops ∧
      s'.nReqs = s.nReqs := by
  simp only [MB] at hm
  unfold stepWrite1Reply at h; peel h
  all_goals (cases h)
  all_goals (try have hsc := shortCircuit_sb hs ‹shortCircuit _ _ _ _ = some _›)
  all_goals (try have hw := WOB_get hs ‹s.wops.get? _ = some _›)
  all_goals first
    | exact ⟨T, Int.le_refl _, sub_self_le_of (pot_del' hsc.2.2.2 hsc.2.2.1 hsrt (by rfl) (by rfl)),
        SB.of_wops hsc.1 rfl rfl rfl rfl (wops_del (by rw [hsc.2.2.1]; exact hs.wops)),
        OB_append hsc.2.1 OB_ext, srt_del (by rw [hsc.2.2.1]; exact hsrt) _, hsc.2.2.2⟩
    | exact ⟨T, Int.le_refl _, by omega, hs, OB_nil, hsrt, rfl⟩
    | (refine ⟨T, Int.le_refl _, pot_same_le hsrt ‹_› (by rfl) (by rfl) (by rfl),
          SB.of_wops hs rfl rfl rfl rfl (wops_put hs.wops ⟨?_, ?_⟩), OB_nil, srt_put hsrt _ _, rfl⟩
       · dsimp only; first | exact hm | exact hw.1
       · intro t ht; dsimp only at ht; exact hw.2 t ht)
    | (have hs1 : SB (T + 1) E s := hs.mono (by omega) (Int.le_refl _)
       refine ⟨T + 1, by omega, pot_choice_le hsrt ‹_› ‹_› (by rfl) (by rfl) (by rfl),
          SB.of_wops hs1 rfl rfl rfl rfl (wops_put hs1.wops ⟨?_, ?_⟩), ?_, srt_put hsrt _ _, rfl⟩
       · dsimp only; first | exact hm.mono (by omega) (Int.le_refl _) | exact hw.1.mono (by omega) (Int.le_refl _)
       · intro t ht; dsimp only at ht; cases ht
         first | exact TB_succ hm hT72 hE | exact TB_succ hw.1 hT72 hE
       · apply OB_mapM_sendTo ‹_›; simp only [MB]
         first | exact TB_succ hm hT72 hE | exact TB_succ hw.1 hT72 hE)
theorem stepWrite2Reply_tb {m : Write2ReplyM}
    (h : stepWrite2Reply s m = .ok (s', o)) :
    ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧ Srt s'.wops ∧
      s'.nReqs = s.nReqs := by
  unfold stepWrite2Reply at h; peel h
  all_goals (cases h)
  all_goals (try have hsc := shortCircuit_ite_sb hs ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›)
  all_goals (try have hw := WOB_get hs ‹s.wops.get? _ = some _›)
  all_goals first
    | exact ⟨T, Int.le_refl _, sub_self_le_of (pot_del' hsc.2.2.2 hsc.2.2.1 hsrt (by rfl) (by rfl)),
        SB.of_wops hsc.1 rfl rfl rfl rfl (wops_del (by rw [hsc.2.2.1]; exact hs.wops)),
        OB_append hsc.2.1 OB_ext, srt_del (by rw [hsc.2.2.1]; exact hsrt) _, hsc.2.2.2⟩
    | exact ⟨T, Int.le_refl _, by omega, hs, OB_nil, hsrt, rfl⟩
    | (refine ⟨T, Int.le_refl _, pot_same_le hsrt ‹_› (by rfl) (by rfl) (by rfl),
          SB.of_wops hs rfl rfl rfl rfl (wops_put hs.wops ⟨?_, ?_⟩), OB_nil, srt_put hsrt _ _, rfl⟩
       · dsimp only; exact hw.1
       · intro t ht; dsimp only at ht; exact hw.2 t ht)
theorem stepClientWrite_tb {rid cid : w32} {k v : w64} {d : Dep} (hn : s.nReqs ≤ 24)
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) :
    ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧ Srt s'.wops ∧
      s'.nReqs ≤ 24 := by
  unfold stepClientWrite at h; peel h
  cases h
  refine ⟨T, Int.le_refl _, pot_req hsrt (by rfl) (by rfl),
    SB.of_wops hs rfl rfl rfl rfl (wops_put hs.wops ⟨TB_tag0 hT hE, fun t ht => by cases ht⟩),
    OB_mapM_sendTo ‹_› (by simp only [MB]; exact guard_slt ‹_›), srt_put hsrt _ _, ?_⟩
  have := ‹¬s.nReqs ≥ 24›
  show s.nReqs + 1 ≤ 24; omega
theorem stepClientRead_tb {rid cid : w32} {k : w64} {d : Dep} (hn : s.nReqs ≤ 24)
    (h : stepClientRead s rid cid k d = .ok (s', o)) :
    ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧ Srt s'.wops ∧
      s'.nReqs ≤ 24 := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  have hm := ‹List.mapM _ _ = some o›
  have h24 := ‹¬s.nReqs ≥ 24›
  have hP : SB T E s' ∧ s'.wops = s.wops ∧ s'.nReqs = s.nReqs + 1 ∧ s'.tag = s.tag := by
    refine forIn_exc_inv _ _ _ (fun x : RState => SB T E x ∧ x.wops = s.wops ∧
      x.nReqs = s.nReqs + 1 ∧ x.tag = s.tag) ?_ ?_ _ hx
    · refine ⟨SB.of_rops hs rfl rfl rfl rfl (rops_put hs.rops ⟨?_, ?_⟩), rfl, rfl, rfl⟩
      · intro v hv; cases hv
      · intro v hv; cases hv
    intro a b st hb hf
    peel hf
    all_goals (cases hf)
    all_goals first
      | exact hb
      | exact ⟨SB.of_eq hb.1 rfl rfl rfl rfl rfl, hb.2⟩
  refine ⟨T, Int.le_refl _, pot_req' hP.2.2.1 hP.2.1, hP.1, OB_mapM_sendPeer hm ?_,
    hP.2.1 ▸ hsrt, by omega⟩
  simp only [MB]
  exact ⟨TB_tag0 hT hE, by show TB T E s'.tag; rw [hP.2.2.2]; exact hs.tag⟩

theorem stepClientRMW_tb {rid cid : w32} {k : w64} {d : Dep} {a b : w64} (hn : s.nReqs ≤ 24)
    (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧ Srt s'.wops ∧
      s'.nReqs ≤ 24 := by
  have hcr := stepClientRMW_spec h
  unfold stepClientRMW at h
  peel h
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
  have h24 := ‹¬s.nReqs ≥ 24›
  have hn' := startPhase1_nr h
  have hsb := startPhase1_tb ?_ hT hE h
  rotate_left
  · exact SB.of_eq hs rfl rfl rfl rfl rfl
  have hn'' : s'.nReqs = s.nReqs + 1 := hn'
  refine ⟨T, Int.le_refl _, pot_req' hn'' hcr.2.2.2.2.1, hsb.1, hsb.2, hcr.2.2.2.2.1 ▸ hsrt,
    by omega⟩

theorem stepExec_tb {q i : w32} (hE2 : E < 2 ^ 31 - 2)
    (h : stepExec s q i = .ok (s', o)) :
    SB T (E + if (execRes o).isSome then 1 else 0) s' ∧
      OB T (E + if (execRes o).isSome then 1 else 0) o := by
  obtain ⟨c, hc, hsh⟩ := stepExec_shape h
  rcases hsh with ⟨rfl, rfl⟩ | ⟨vt0, hv0, me, d, rfl, hmt, rfl⟩
  · have : (execRes ([] : List Out)).isSome = false := rfl
    rw [this]; simp only [Bool.false_eq_true, if_false, Int.add_zero]
    exact ⟨hs.setInst (by exact hs.inst q i c hc), OB_nil⟩
  · have : (execRes [Out.send d (.executeOverwrite me)]).isSome = true := rfl
    rw [this]; simp only [if_true]
    have hv : TB T E vt0.t := by
      rcases hv0 with e | ⟨pvt, hp, e⟩
      · rw [e]; exact (hs.inst q i c hc).1
      · rw [e]; exact hs.pvt pvt hp
    have hs1 : SB T (E + 1) s := hs.mono (Int.le_refl _) (by omega)
    have ht := TB_rsucc hv hE2
    rw [← hmt] at ht
    refine ⟨SB.setInst (s := { s with prevValTag := some ⟨me.v, me.t⟩ })
      ⟨hs1.tag, ?_, hs1.inst, hs1.wops, hs1.rops⟩ (by exact hs1.inst q i c hc), ?_⟩
    · intro x hx; injection hx with hx; subst hx; exact ht
    intro y hy; simp at hy; subst hy; exact ht
end

end Perennial.gryff.pure.La
