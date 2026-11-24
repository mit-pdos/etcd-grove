/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/VInv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: **L3 over runs** (`vinv`): along a prefix of a run `L`, every carried pair is produced
in `L` (`Prod L`) with `rmwc ≥ 0`. The two sources (`src_exec`, `src_write`) are discharged with the
commands invariant, the chain, and the write records.
-/
module

public import Dsverify.Proof.gryff.PureLc.Vals
public import Dsverify.Proof.gryff.PureLc.WSrc

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- L3's predicate in run `L`. -/
def QL (L : List Label) (v : w64) (t : model.Tag) : Prop := Prod L v t ∧ 0 ≤ sint.Z t.rmwc

theorem QL_zero (L : List Label) : QL L 0 model.tag0 :=
  ⟨Or.inl ⟨by simp [model.Tag.toP, model.tag0, proto.tag0, sint.Z], rfl⟩, by
    simp [model.tag0, sint.Z]⟩

/-- The values invariant of a configuration. -/
def VInv (L : List Label) (c : Cfg gNet) : Prop :=
  ∀ j : Fin 3, VS (QL L) (stR c j) ∧ ∀ m ∈ infR c j, VM (QL L) m

/-- A configuration on a prefix of `L` holds `L`'s cut states. -/
theorem stR_prefix {L l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (hpre : l <+: L) (r : Fin 3) : stR c r = cutSt L l.length r := by
  obtain ⟨L2, rfl⟩ := hpre
  rw [grun_st h r]; unfold cutSt; rw [List.take_left' rfl, List.take_length]

/-- An RMW whose instance some replica executed (with a result) has that result. -/
theorem rmwRes_of_exec {L : List Label} {cL : Cfg gNet} (hL : GRun (Cfg.init gNet) L cL) {o : Op}
    {r : Fin 3} {vt : ValTag} (hm : (rmwInst L o, vt) ∈ execSeq r (projR L r)) :
    rmwRes L o = some vt := by
  cases hr : rmwRes L o with
  | some vt' =>
    obtain ⟨r', hm'⟩ := rmwRes_mem hr
    rw [exec_same hL r' r hm' hm]
  | none =>
    exfalso
    unfold rmwRes at hr
    have h1 := List.findSome?_eq_none_iff.1 hr r (List.mem_finRange r)
    unfold execVT at h1
    obtain ⟨j, hj, hv⟩ := (mem_execSeq r).1 hm
    have h2 := List.findSome?_eq_none_iff.1 h1 j
      (List.mem_range.2 (List.getElem?_eq_some_iff.1 hj).1)
    rw [hj] at h2; simp only [if_true] at h2
    rw [hv] at h2; cases h2

/-- **Source: an execution's result is produced.** -/
theorem src_exec {L l : List Label} {cL c : Cfg gNet} (hL : GRun (Cfg.init gNet) L cL)
    (h : GRun (Cfg.init gNet) l c) (hi : VInv L c) {i : Fin 3} {q i' : w32}
    (hpre : l ++ [(i, .exec q i')] <+: L) {s' : RState} {o : List Out}
    (hs : stepR i (stR c i) (.exec q i') = .ok (s', o)) {vt : ValTag} (hv : execRes o = some vt) :
    QL L vt.v vt.t := by
  have hpre' : l <+: L := (List.prefix_append l _).trans hpre
  have hst := stR_prefix h hpre' i
  have hs' := hs
  change stepExec _ q i' = _ at hs'
  obtain ⟨cp, c0, rest, hcp, hcst, hcm, vt0, hor, -, -, htt, hvv⟩ := stepExec_full hs' hv
  -- the applied pair
  have hQ0 : QL L vt0.v vt0.t := by
    rcases hor with e | e
    · rw [e]; exact ((hi i).1.inst _ _ _ hcp).1
    · exact (hi i).1.prev _ e
  obtain ⟨hb1, hb2⟩ := rmwc_bounded hL l.length i
  rw [← hst] at hb1 hb2
  have hbound : sint.Z vt0.t.rmwc < 2 ^ 31 - 1 := by
    rcases hor with e | e
    · rw [e]; exact hb2 _ _ _ hcp
    · exact hb1 _ e
  refine ⟨?_, ?_⟩
  · -- the RMW whose instance this is
    have hci := cinv (L := L) _ _ h hpre'
    obtain ⟨o', ho', hio, hx⟩ := ((hci i).1 _ _ cp hcp).1 c0 rest hcm
    refine Or.inr (Or.inr ⟨o', ho', _, _, hio, ?_⟩)
    -- this execution is in `i`'s executed sequence
    obtain ⟨L2, hL2⟩ := hpre
    have hn : L[l.length]? = some (i, .exec q i') := by rw [← hL2]; simp
    have hj := proj_cons_drop L i hn
    obtain ⟨n, s'', o'', -, hc, hs'', -, ho''⟩ := proj_step hL hj
    have hseq : stOf i ((projR L i).take (projR (L.take l.length) i).length) = stR c i := by
      rw [hst]; unfold cutSt
      congr 1
      subst hL2
      rw [List.append_assoc, List.take_left' rfl, proj_append, List.take_left' rfl]
    rw [hseq, hs] at hs''
    cases hs''
    have hm : (rmwInst L o', vt) ∈ execSeq i (projR L i) := by
      rw [hx, mem_execSeq]
      exact ⟨_, hj, by rw [ho'']; exact hv⟩
    exact rmwRes_of_exec hL hm
  · rw [htt]
    show 0 ≤ sint.Z (vt0.t.rmwc + 1)
    rw [Z_succ32 hbound]; have := hQ0.2; omega

/-- **Source: a write's new `WriteTag`, with its value, is produced.** -/
theorem src_write {L l : List Label} {cL c : Cfg gNet} (hL : GRun (Cfg.init gNet) L cL)
    (h : GRun (Cfg.init gNet) l c) (hi : VInv L c) {i : Fin 3} {m : Write1ReplyM}
    (hpre : l ++ [(i, .msg (.write1Reply m))] <+: L) {s' : RState} {o : List Out}
    (hs : stepR i (stR c i) (.msg (.write1Reply m)) = .ok (s', o)) {K : w64} {w w' : WriteOp}
    (hw : (stR c i).wops.get? K = some w) (hn : w.writeTag = none) (hw' : s'.wops.get? K = some w')
    {wt : model.Tag} (ht : w'.writeTag = some wt) : QL L w'.writeValue wt := by
  have hpre' : l <+: L := (List.prefix_append l _).trans hpre
  have hst := stR_prefix h hpre' i
  have hs' := hs
  change stepWrite1Reply _ m = _ at hs'
  rcases stepWrite1Reply_wt hs' K w' hw' with ⟨w0, hw0, e⟩ | ⟨hK, ts, e⟩
  · rw [hw] at hw0; cases hw0; rw [e, hn] at ht; cases ht
  rw [e] at ht; cases ht
  obtain ⟨w1, hw1, ⟨-, -, i3⟩⟩ := stepWrite1Reply_wid hs' K w' hw'
  rw [hw] at hw1; cases hw1
  -- this step in `i`'s projection
  obtain ⟨L2, hL2⟩ := hpre
  have hn' : L[l.length]? = some (i, .msg (.write1Reply m)) := by rw [← hL2]; simp
  have hj := proj_cons_drop L i hn'
  obtain ⟨n, s'', o'', -, -, hs'', hs2, -⟩ := proj_step hL hj
  have hseq : stOf i ((projR L i).take (projR (L.take l.length) i).length) = stR c i := by
    rw [hst]; unfold cutSt
    congr 1
    subst hL2
    rw [List.append_assoc, List.take_left' rfl, proj_append, List.take_left' rfl]
  rw [hseq, hs] at hs''
  cases hs''
  have hjlt := (List.getElem?_eq_some_iff.1 hj).1
  generalize hjn : (projR (L.take l.length) i).length = jn at hseq hjlt hs2
  -- the record's write
  obtain ⟨hKw, j', hj', k, d, hwj⟩ := wrec_origin hL i jn (by omega) K w (by rw [hseq]; exact hw)
  obtain ⟨n', hn'', hp'⟩ := proj_index L i hwj
  let ow : Op := { g := n', r := i, j := (projR (L.take n') i).length, cid := w.clientId,
                   rid := w.requestId, inp := .write w.writeValue }
  have hop : opAt L n' = some ow := by unfold opAt; rw [hn'']; rfl
  have ho : ow ∈ ops L := mem_ops.2 ⟨(List.getElem?_eq_some_iff.1 hn'').1, hop⟩
  have hjlt' := (List.getElem?_eq_some_iff.1 hwj).1
  have hoj : ow.j = j' := by
    show (projR (L.take n') i).length = j'
    rw [hp', List.length_take]; omega
  have hokey : ow.key = K := by rw [hKw]; rfl
  refine ⟨Or.inr (Or.inl ⟨ow, ho, by rw [i3], ?_⟩), by simp [sint.Z]⟩
  show writePlace L ow = some _
  unfold writePlace
  refine firstFrom_eq (b := jn) (by omega) hjlt ?_ ?_
  · show ((stOf i ((projR L i).take (jn + 1))).wops.get? ow.key).bind WriteOp.writeTag = _
    rw [hs2, hokey, hw']; exact e
  · intro c' hc1 hc2
    cases hf : ((stOf i ((projR L i).take (c' + 1))).wops.get? ow.key).bind WriteOp.writeTag with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨w2, hw2, hwt2⟩ := Option.bind_eq_some_iff.1 hf
      rw [hokey] at hw2
      have hset : ∀ w, (stOf i ((projR L i).take (c' + 1))).wops.get? K = some w →
          w.writeTag.isSome := by
        intro w3 h3; rw [hw2] at h3; cases h3; rw [hwt2]; rfl
      have hno : ∀ z, c' + 1 ≤ z → z < c' + 1 + (jn - (c' + 1)) → ∀ rid cid k v dd,
          (projR L i)[z]? = some (.write rid cid k v dd) → K ≠ shiftInts rid cid := by
        intro z hz1 hz2 rid cid k v dd hz hK2
        obtain ⟨n2, hn2, hp2⟩ := proj_index L i hz
        let o2 : Op := { g := n2, r := i, j := (projR (L.take n2) i).length, cid, rid,
                         inp := .write v }
        have hop2 : opAt L n2 = some o2 := by unfold opAt; rw [hn2]; rfl
        have ho2 : o2 ∈ ops L := mem_ops.2 ⟨(List.getElem?_eq_some_iff.1 hn2).1, hop2⟩
        have hz' := (List.getElem?_eq_some_iff.1 hz).1
        have ho2j : o2.j = z := by
          show (projR (L.take n2) i).length = z
          rw [hp2, List.length_take]; omega
        have hc1 := ((winv hL).1.ops ow ho).2
        have hc2 := ((winv hL).1.ops o2 ho2).2
        obtain ⟨er, ec⟩ := shiftInts_inj hc1 hc2 (hKw.symm.trans hK2)
        have := (rinv hL).2.1.uniq ow ho o2 ho2 rfl ec er
        rw [← this] at ho2j
        omega
      have := wtag_persist hL i hset (jn - (c' + 1)) (by omega) hno w
        (by rw [show c' + 1 + (jn - (c' + 1)) = jn by omega, hseq]; exact hw)
      rw [hn] at this; cases this

theorem vinv_step {L l : List Label} {cL c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (hL : GRun (Cfg.init gNet) L cL) (h : GRun (Cfg.init gNet) l c) (hi : VInv L c)
    (hs : GStep c i e c' x) (hpre : l ++ [(i, e)] <+: L) : VInv L c' := by
  obtain ⟨s', o, hst⟩ := StepAt.of h hs
  have key := step_v hst.ok (QL_zero L) (hi i).1 (fun m hm => (hi i).2 m (hst.recv m hm))
    (fun q i' he vt hv => by subst he; exact src_exec hL h hi hpre hst.ok hv)
    (fun m he K w w' hw hn hw' wt ht => by subst he; exact src_write hL h hi hpre hst.ok hw hn hw' ht)
  intro j
  refine ⟨?_, fun m hm => ?_⟩
  · rw [hst.st j]
    split
    · exact key.1
    · exact (hi j).1
  · rcases hst.mem hm with hm | hm
    · exact (hi j).2 m hm
    · obtain ⟨d, hd⟩ := mem_sentR hm
      exact key.2 _ hd

theorem vinv_init (L : List Label) : VInv L (Cfg.init gNet) := by
  intro j
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun m hm => by cases hm⟩
  · exact QL_zero L
  · intro vt h; cases h
  · intro q i cp h; cases h
  · intro K rd h; simp [stR, Cfg.init, gNet, RState.init, AMap.get?] at h
  · intro K w h; simp [stR, Cfg.init, gNet, RState.init, AMap.get?] at h

/-- **L3 over runs.** -/
theorem vinv {L : List Label} {cL : Cfg gNet} (hL : GRun (Cfg.init gNet) L cL) :
    ∀ l c, GRun (Cfg.init gNet) l c → l <+: L → VInv L c :=
  grun_inv (fun l c => l <+: L → VInv L c) (fun _ => vinv_init L)
    (fun l c i e c' x h hi hs hpre =>
      vinv_step hL h (hi ((List.prefix_append l _).trans hpre)) hs hpre)

/-- L3 at a cut's states. -/
theorem vinv_cut {L : List Label} {cL : Cfg gNet} (hL : GRun (Cfg.init gNet) L cL) (n : Nat)
    (r : Fin 3) : VS (QL L) (cutSt L n r) := by
  obtain ⟨cn, h1, -, h3⟩ := grun_cut hL n
  have hs : stR cn r = cutSt L n r := by
    obtain ⟨o', ho'⟩ := h3 r; unfold cutSt; rw [stOf_of_runP ho']; rfl
  rw [← hs]; exact (vinv hL _ _ h1 (List.take_prefix n L) r).1

end Perennial.gryff.pure
