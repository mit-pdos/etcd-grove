/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/L2W.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **reply ownership** for reads' and writes' replies (`rw_reply_owner`: a read or write
reply output at `R` has the key of a read / write operation at `R`, the owner of a live record),
and **L2 for writes** (`l2_write_lb`): when a write is replied to, its place (its record's
`WriteTag`, `WPInv`) is held by two distinct `Write2` repliers' stores.
-/
module

public import Dsverify.Proof.gryff.PureLb.WPlace
public import Dsverify.Proof.gryff.PureLb.L2
public import Dsverify.Proof.gryff.PureLb.RmwOwn

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem noR_not_writeReply {o : List Out} (h : NoR o) {cid rid : w32} {f : w8} :
    Out.ext (.writeReply cid rid f) ∉ o := fun hx => by
  have := h _ hx; simp [isROut] at this

/-- The events whose outputs can contain a write reply. -/
theorem writeReply_src {r : Fin 3} {s s' : RState} {e : Ev} {outs : List Out} {cid rid : w32}
    {f : w8} (h : stepR r s e = .ok (s', outs))
    (hx : Out.ext (.writeReply cid rid f) ∈ outs) :
    (∃ m, e = .msg (.read1Reply m)) ∨ (∃ m, e = .msg (.write1Reply m)) ∨
    (∃ m, e = .msg (.write2Reply m)) ∨ (∃ m, e = .msg (.read2 m)) ∨
    (∃ m, e = .msg (.read2Reply m)) := by
  cases e with
  | read =>
    obtain ⟨-, -, -, -, -, ho⟩ := stepClientRead_spec' h
    obtain ⟨dd, hdd, -⟩ := ho _ hx; cases hdd
  | write => exact absurd hx (noR_not_writeReply (stepClientWrite_spec' h).2.2.2.2)
  | rmw => exact absurd hx (noR_not_writeReply (stepClientRMW_fr h).2.2.2.2.2)
  | msg m =>
    cases m with
    | read1 =>
      obtain ⟨-, -, -, y, hy, rfl⟩ := stepRead1_spec h
      obtain ⟨d, -, rfl⟩ := sendTo_out hy; exact absurd hx not_ext_mem_send
    | write1 =>
      obtain ⟨-, hout⟩ := stepWrite1_spec h
      rcases hout with rfl | ⟨y, hy, rfl⟩
      · cases hx
      · obtain ⟨d, -, rfl⟩ := sendTo_out hy; exact absurd hx not_ext_mem_send
    | write2 =>
      obtain ⟨-, -, -, y, hy, rfl⟩ := stepWrite2_spec h
      obtain ⟨d, -, rfl⟩ := sendTo_out hy; exact absurd hx not_ext_mem_send
    | read1Reply m => exact Or.inl ⟨m, rfl⟩
    | write1Reply m => exact Or.inr (Or.inl ⟨m, rfl⟩)
    | write2Reply m => exact Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))
    | read2 m => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))
    | read2Reply m => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩)))
    | _ => exact absurd hx (noR_not_writeReply (step_fr_other h rfl).2)
  | _ => exact absurd hx (noR_not_writeReply (step_fr_other h rfl).2)

/-- A `Write2Reply` that replies to the write has counted a majority of replies. -/
theorem stepWrite2Reply_cnt {s s' : RState} {m : Write2ReplyM} {o : List Out} {w : WriteOp}
    (hk : s.wops.get? (shiftInts m.requestId m.clientId) = some w)
    (h : stepWrite2Reply s m = .ok (s', o)) {cid rid : w32} {f : w8}
    (hx : Out.ext (.writeReply cid rid f) ∈ o) :
    sge (w.numWrite2Replies + 1) (NHALF + 1) = true := by
  unfold stepWrite2Reply at h
  simp only [hk] at h
  peel h
  all_goals (cases h)
  all_goals (first | (simp at hx; done) | assumption)

/-- The step's outputs, from a reachable configuration. -/
structure ReplyCtx (l : List Label) (cn : Cfg gNet) (R : Fin 3) (e : Ev) (s' : RState)
    (outs : List Out) : Prop where
  run : GRun (Cfg.init gNet) l cn
  ok : stepR R (stR cn R) e = .ok (s', outs)
  recv : ∀ m, e.recv = some m → m ∈ infR cn R

/-- A short-circuit deletes the records of the reads it replies to. -/
theorem shortCircuit_del {s s' : RState} {n : w32} {value : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n value f = some (s', o)) {cid rid : w32} {v : w64} {f' : w8}
    (hx : Out.ext (.readReply cid rid v f') ∈ o) : s'.rops.get? (shiftInts rid cid) = none := by
  revert cid rid v f'
  unfold shortCircuit at h
  opeel h
  all_goals (try (cases h))
  all_goals (
    refine forIn_opt_inv_mem _ _ _ (fun p : RState × List Out =>
      ∀ {cid rid : w32} {v : w64} {f' : w8}, (Out.ext (.readReply cid rid v f') : Out) ∈ p.2 →
        p.1.rops.get? (shiftInts rid cid) = none) ?_ ?_ _ ‹forIn _ _ _ = some _›)
  all_goals (first
    | (intro cid rid v f' hx; simp at hx; done)
    | (intro a ha b st hb hf
       opeel hf
       all_goals (cases hf)
       all_goals (try exact hb)
       intro cid rid v f' hx
       dsimp only [ForInStep.value] at hx ⊢
       rcases List.mem_append.1 hx with hx | hx
       · have := hb hx
         rw [AMap.get?_del]; split
         · rfl
         · exact this
       · simp only [List.mem_singleton, Out.ext.injEq, Ext.readReply.injEq] at hx
         obtain ⟨rfl, rfl, -, -⟩ := hx
         rw [AMap.get?_del, if_pos rfl]))

/-- **Read reply ownership**: a read reply output at `R` has the key of a read at `R`. -/
theorem readReply_owner {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {cid rid : w32} {v : w64} {f : w8}
    (hx : Out.ext (.readReply cid rid v f) ∈ outs) :
    (∃ o ∈ ops l, o.r = R ∧ o.inp = .read ∧ o.cid = cid ∧ o.rid = rid) ∧
      (stR cn R).rops.get? (shiftInts rid cid) ≠ none ∧ s'.rops.get? (shiftInts rid cid) = none := by
  obtain ⟨hM, hR, -⟩ := rinv hc.run
  have hstep := hc.ok
  rcases readReply_src hstep hx with ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ <;>
    subst he <;> have hm := hc.recv _ rfl
  · cases hk : (stR cn R).rops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepRead1Reply_none hk hstep; cases hx
    | some rd =>
      obtain ⟨hfresh, hK, ⟨o, ho, hor, hoi, hoc, hoq⟩, -⟩ := hR.rops R _ rd hk
      rw [hfresh] at hk
      obtain ⟨rfl, rfl⟩ := stepRead1Reply_fresh hk hstep
      simp only [List.mem_singleton, Out.ext.injEq, Ext.readReply.injEq] at hx
      obtain ⟨hc', hr', -, -⟩ := hx
      subst hc' hr'
      refine ⟨⟨o, ho, hor, hoi, hoc, hoq⟩, ?_, ?_⟩
      · rw [← hK, hk]; simp
      · show ((stR cn R).rops.del _).get? _ = none
        rw [AMap.get?_del, if_pos hK.symm]
  · exfalso
    cases hk : (stR cn R).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite1Reply_none hk hstep; cases hx
    | some w =>
      obtain ⟨-, -, -, hwv, hwa⟩ := hR.wops R _ w (AMap.mem_of_get? hk)
      obtain ⟨w', -, -, -, -, -, -, -, hbr⟩ :=
        stepWrite1Reply_some hk hwv hwa (hM R _ hm) hstep
      rcases hbr with ⟨-, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      · cases hx
      · simp at hx
  · cases hk : (stR cn R).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite2Reply_none hk hstep; cases hx
    | some w =>
      rcases stepWrite2Reply_some hk hstep with ⟨-, rfl⟩ | ⟨wt, s1, outs', hwt, hsc, rfl, rfl⟩
      · cases hx
      replace hx : Out.ext (.readReply cid rid v f) ∈ outs' := by
        rcases List.mem_append.1 hx with hx | hx
        · exact hx
        · simp at hx
      obtain ⟨-, hsc⟩ : sge (w2bump w m.applied).numWrite2Applies (NHALF + 1) = true ∧
          shortCircuit (stR cn R) w.n ⟨w.writeValue, wt⟩ false = some (s1, outs') := by
        rcases hsc with hsc | ⟨-, rfl⟩
        · exact hsc
        · cases hx
      have hdel := shortCircuit_del hsc hx
      obtain ⟨_, _, -, -, -, -, hsco⟩ := shortCircuit_spec hsc
      obtain ⟨cid', rid', hxe, op, hop, k, hk', e', he', hec, her, rd, hrd⟩ := hsco _ hx
      simp only [Out.ext.injEq, Ext.readReply.injEq] at hxe
      obtain ⟨hc', hr', -, -⟩ := hxe
      subst hc' hr'
      obtain ⟨-, hK, ⟨o, ho, hor, hoi, hoc, hoq⟩, ⟨e1, he1, he1a, he1b⟩⟩ := hR.rops R _ rd hrd
      have hc1 := (hR.ongoing R _ _ he').2.2.2.2
      have hc2 := (hR.ongoing R _ _ he1).2.2.2.2
      rw [he1b] at hc2
      rw [← hec, ← her] at hK
      obtain ⟨a, b⟩ := shiftInts_inj hc1 hc2 hK
      refine ⟨⟨o, ho, hor, hoi, by rw [hoc, ← b, hec], by rw [hoq, ← a, her]⟩, ?_, hdel⟩
      first | (rw [hrd]; simp) | (rw [← hec, ← her, hrd]; simp) | (rw [hec, her] at hrd; rw [hrd]; simp) | (rw [← hec, ← her] at hrd; rw [hrd]; simp)
  · exact (hM R _ hm).elim
  · exact (hM R _ hm).elim

/-- **Write reply ownership**: a write reply output at `R` completes a write's record at `R`
(a `Write2Reply` with a majority of replies counted), whose owner is a write at `R` with the
reply's key. -/
theorem writeReply_owner {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {cid rid : w32} {f : w8}
    (hx : Out.ext (.writeReply cid rid f) ∈ outs) :
    ∃ m w wt, e = .msg (.write2Reply m) ∧ Msg.write2Reply m ∈ infR cn R ∧
      (stR cn R).wops.get? (shiftInts m.requestId m.clientId) = some w ∧
      w.writeTag = some wt ∧ sge (w.numWrite2Replies + 1) (NHALF + 1) = true ∧
      w.clientId = cid ∧ w.requestId = rid ∧ shiftInts m.requestId m.clientId = shiftInts rid cid ∧
      s'.wops.get? (shiftInts rid cid) = none ∧
      ∃ o ∈ ops l, o.r = R ∧ (∃ v, o.inp = .write v) ∧ o.cid = cid ∧ o.rid = rid := by
  obtain ⟨hM, hR, -⟩ := rinv hc.run
  have hstep := hc.ok
  rcases writeReply_src hstep hx with ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ <;>
    subst he <;> have hm := hc.recv _ rfl
  · exfalso
    cases hk : (stR cn R).rops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepRead1Reply_none hk hstep; cases hx
    | some rd =>
      obtain ⟨hfresh, -, -, -⟩ := hR.rops R _ rd hk
      rw [hfresh] at hk
      obtain ⟨-, rfl⟩ := stepRead1Reply_fresh hk hstep
      simp at hx
  · exfalso
    cases hk : (stR cn R).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite1Reply_none hk hstep; cases hx
    | some w =>
      obtain ⟨-, -, -, hwv, hwa⟩ := hR.wops R _ w (AMap.mem_of_get? hk)
      obtain ⟨w', -, -, -, -, -, -, -, hbr⟩ :=
        stepWrite1Reply_some hk hwv hwa (hM R _ hm) hstep
      rcases hbr with ⟨-, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      · cases hx
      · simp at hx
  · cases hk : (stR cn R).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite2Reply_none hk hstep; cases hx
    | some w =>
      have hcnt := stepWrite2Reply_cnt hk hstep hx
      rcases stepWrite2Reply_some hk hstep with ⟨-, rfl⟩ | ⟨wt, s1, outs', hwt, hsc, rfl, rfl⟩
      · cases hx
      have hx' : (Out.ext (Ext.writeReply cid rid f) : Out) =
          Out.ext (Ext.writeReply w.clientId w.requestId 1) := by
        rcases List.mem_append.1 hx with hx | hx
        · exfalso
          rcases hsc with ⟨-, hsc⟩ | ⟨-, rfl⟩
          · obtain ⟨_, _, -, -, -, -, hsco⟩ := shortCircuit_spec hsc
            obtain ⟨_, _, hxe, -⟩ := hsco _ hx
            cases hxe
          · cases hx
        · exact List.mem_singleton.1 hx
      simp only [Out.ext.injEq, Ext.writeReply.injEq] at hx'
      obtain ⟨rfl, rfl, -⟩ := hx'
      obtain ⟨hK, ⟨o, ho, hor, hov, hoc, hoq⟩, -⟩ := hR.wops R _ w (AMap.mem_of_get? hk)
      refine ⟨m, w, wt, rfl, hm, hk, hwt, hcnt, rfl, rfl, hK, ?_, o, ho, hor, hov, hoc, hoq⟩
      show (s1.wops.del _).get? _ = none
      rw [AMap.get?_del, if_pos hK.symm]
  · exact (hM R _ hm).elim
  · exact (hM R _ hm).elim

/-- **RMW reply ownership**: an RMW reply output at `R` has the key of an RMW at `R` (it is
`handleExecuted`'s, from a proposal of `R`'s state, owned by an RMW: `pown`). -/
theorem rmwReply_owner {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {cid rid : w32} {f : w8}
    (hx : Out.ext (.rmwReply cid rid f) ∈ outs) :
    ∃ o ∈ ops l, o.r = R ∧ (∃ a b, o.inp = .cas a b) ∧ o.cid = cid ∧ o.rid = rid := by
  obtain ⟨p, hp, h1, h2⟩ := rmwReply_prop hc.ok hx
  obtain ⟨o, ho, a1, a2, a3, a4⟩ := pown hc.run R p hp
  exact ⟨o, ho, a1, a2, by rw [a3, h1], by rw [a4, h2]⟩

/-- **Reply ownership**: a reply output at `R` has the key of an operation at `R` of its kind. -/
theorem reply_owner {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {x : Ext} (hx : Out.ext x ∈ outs) :
    ∃ o ∈ ops l, o.r = R ∧ (o.cid, o.rid) = x.key ∧ x.fits o.inp := by
  cases x with
  | readReply cid rid v f =>
    obtain ⟨⟨o, ho, hor, hoi, hoc, hoq⟩, -⟩ := readReply_owner hc hx
    refine ⟨o, ho, hor, by rw [hoc, hoq]; rfl, ?_⟩
    rw [hoi]; trivial
  | writeReply cid rid f =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, o, ho, hor, ⟨v, hov⟩, hoc, hoq⟩ := writeReply_owner hc hx
    refine ⟨o, ho, hor, by rw [hoc, hoq]; rfl, ?_⟩
    rw [hov]; trivial
  | rmwReply cid rid f =>
    obtain ⟨o, ho, hor, ⟨a, b, hoi⟩, hoc, hoq⟩ := rmwReply_owner hc hx
    refine ⟨o, ho, hor, by rw [hoc, hoq]; rfl, ?_⟩
    rw [hoi]; trivial

/-! ## L2 for writes -/

/-- The configuration before label `n` of a run, and the step at `n`. -/
theorem label_ctx {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {n : Nat}
    {R : Fin 3} {e : Ev} (hn : l[n]? = some (R, e)) :
    ∃ cn s' outs, ReplyCtx (l.take n) cn R e s' outs ∧ outsAt l n = outs ∧
      (∀ r, cutSt l n r = stR cn r) ∧ cutSt l (n + 1) R = s' ∧
      (∀ q, q ≠ R → cutSt l (n + 1) q = cutSt l n q) := by
  obtain ⟨s', outs, hstep, hR1, hR2, houts, -⟩ := grun_label h hn
  obtain ⟨cn, h1, h2, h3⟩ := grun_cut h n
  have hcs : ∀ r, cutSt l n r = stR cn r := fun r => by
    obtain ⟨o', h'⟩ := h3 r; exact stOf_of_runP h'
  have hd : l.drop n = (R, e) :: l.drop (n + 1) := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hn
    rw [List.drop_eq_getElem_cons hlt, he]
  obtain ⟨c1, xx, hs, -⟩ := grun_cons_inv (grun_of_eq hd h2)
  obtain ⟨-, -, -, hrecv, -, -, -⟩ := hs
  exact ⟨cn, s', outs, ⟨h1, by rw [← hcs]; exact hstep, hrecv⟩, houts, hcs, hR1, hR2⟩

theorem ext_mem_outs {l : List Label} {n : Nat} {outs : List Out} (houts : outsAt l n = outs)
    {x : Ext} (hx : x ∈ extsAt l n) : Out.ext x ∈ outs := by
  rw [← houts]
  unfold extsAt extsIn at hx
  obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hx
  cases y with
  | ext y => cases hy'; exact hy
  | send _ _ => cases hy'

/-- A reply to `o` at label `n`: the owner of the reply is `o` (keys are unique per replica). -/
theorem reply_is_own {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {n : Nat} (hr : RepliesTo l n o) :
    ∃ e cn s' outs x, l[n]? = some (o.r, e) ∧ ReplyCtx (l.take n) cn o.r e s' outs ∧
      outsAt l n = outs ∧ (∀ r, cutSt l n r = stR cn r) ∧ cutSt l (n + 1) o.r = s' ∧
      (∀ q, q ≠ o.r → cutSt l (n + 1) q = cutSt l n q) ∧ o ∈ ops (l.take n) ∧
      Out.ext x ∈ outs ∧ x.key = (o.cid, o.rid) ∧ x.fits o.inp := by
  obtain ⟨hgn, hn, x, hx, hxk⟩ := hr
  obtain ⟨⟨R, e⟩, hn', hR⟩ := Option.map_eq_some_iff.1 hn
  simp only at hR; subst hR
  obtain ⟨cn, s', outs, hc, houts, hcs, hR1, hR2⟩ := label_ctx h hn'
  have hnl : n < l.length := (List.getElem?_eq_some_iff.1 hn').1
  have ho' : o ∈ ops (l.take n) := by
    rw [← ops_take, List.mem_filter]; exact ⟨ho, by simp; omega⟩
  have hxo := ext_mem_outs houts hx
  obtain ⟨o', ho'', hor, hk, hfit⟩ := reply_owner hc hxo
  rw [hxk] at hk
  obtain ⟨hk1, hk2⟩ := Prod.mk.inj hk
  have e : o' = o := (rinv hc.run).2.1.uniq o' ho'' o ho' hor hk1 hk2
  subst e
  exact ⟨e, cn, s', outs, x, hn', hc, houts, hcs, hR1, hR2, ho', hxo, hxk, hfit⟩

/-- **L2 for writes** (unit L-c's `l2_write`, `PureLc/Facts.lean`, has this statement): when a
write is replied to (label `n`), its place is at most the frontier
after the label: two distinct `Write2` repliers' stores hold its `WriteTag`. -/
theorem l2_write_lb {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {v : w64} (hi : o.inp = .write v) {n : Nat} (hr : RepliesTo l n o)
    {t : model.Tag} (ht : place l o = some t) : tagLe t.toP (front l (n + 1)) := by
  have ht' : writePlace l o = some t := by unfold place at ht; rw [hi] at ht; exact ht
  obtain ⟨e, cn, s', outs, x, -, hc, -, hcs, hR1, hR2, ho', hxo, hxk, hfit⟩ := reply_is_own h ho hr
  cases x with
  | readReply => rw [hi] at hfit; exact hfit.elim
  | rmwReply => rw [hi] at hfit; exact hfit.elim
  | writeReply cid rid f =>
  simp only [Ext.key, Prod.mk.injEq] at hxk
  obtain ⟨rfl, rfl⟩ := hxk
  obtain ⟨m, w, wt, rfl, hm, hk, hwt, hcnt, -, -, hKeq, -, -⟩ := writeReply_owner hc hxo
  obtain ⟨hM, -, hW2⟩ := rinv hc.run
  have hW := winv hc.run
  have hkey : o.key = shiftInts m.requestId m.clientId := by unfold Op.key; rw [hKeq]
  rw [← hkey] at hk
  -- the place is the record's tag
  have hwp := (wpinv hc.run o ho' v hi w hk).1
  rw [hwt] at hwp
  have hwp' : writePlace (l.take n ++ l.drop n) o = some wt := writePlace_append hwp
  rw [List.take_append_drop, ht'] at hwp'
  cases hwp'
  -- the replies
  obtain ⟨hmu, hmc⟩ := hM o.r _ hm
  obtain ⟨ea, eb⟩ := shiftInts_inj hmc (hW.1.ops o ho').2 hKeq
  have hwr : w2rOf o (.write2Reply m) = true := by simp [w2rOf, ea, eb]
  obtain ⟨sent, C, I, h1, h2, -, -, h5, h6, h7⟩ := hW2 o ho' v hi
  have hmf : Msg.write2Reply m ∈ (infR cn o.r).filter (w2rOf o) := List.mem_filter.2 ⟨hm, hwr⟩
  obtain ⟨p, hpI, -⟩ := List.mem_map.1 (h2.mem_iff.1 hmf)
  obtain ⟨-, b, -, -, nr⟩ := h7 w hk
  cases hsent : sent with
  | none => obtain ⟨-, hI⟩ := h5 hsent; rw [hI] at hpI; cases hpI
  | some gw =>
  obtain ⟨g2, wt0⟩ := gw
  have hwt0 := b g2 wt0 hsent
  rw [hwt] at hwt0; cases hwt0
  obtain ⟨-, hap⟩ := h6 g2 t hsent
  have hperm : (C ++ [p] ++ I.erase p).Perm (C ++ I) := by
    rw [List.append_assoc]
    exact List.Perm.append_left C (List.perm_cons_erase hpI).symm
  have hn3 : ((C ++ [p] ++ I.erase p).map Prod.fst).Nodup :=
    (hperm.map Prod.fst).nodup_iff.2 h1
  rw [List.map_append] at hn3
  have hnC : ((C ++ [p]).map Prod.fst).Nodup := hn3.sublist (List.sublist_append_left _ _)
  have hClen : C.length ≤ 2 := by
    have := nodup_fin3_len hnC; simp at this; omega
  have h2le := sge_two hcnt
  rw [Z_succ64 nr (by omega) (by omega)] at h2le
  have hLl : 2 ≤ (C ++ [p]).length := by simp; omega
  obtain ⟨q1, hq1, q2, hq2, hne⟩ := two_distinct' hnC hLl
  have hL : ∀ q ∈ C ++ [p], tagLe t.toP (cutSt l (n + 1) q.1).tag.toP := by
    intro q hq
    have h0 : tagLe t.toP (stR cn q.1).tag.toP := by
      refine (hap q ?_).2
      rcases List.mem_append.1 hq with hq | hq
      · exact List.mem_append_left _ hq
      · rw [List.mem_singleton.1 hq]; exact List.mem_append_right _ hpI
    refine tagLe_trans h0 ?_
    by_cases hq' : q.1 = o.r
    · rw [hq', hR1]; exact step_tag_mono hc.ok
    · rw [hR2 _ hq', hcs]; exact tagLe_refl _
  exact le_front_of_pair hne (hL q1 hq1) (hL q2 hq2)

end Perennial.gryff.pure
