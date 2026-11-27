/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/F3.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **(F3) replies** and **reply uniqueness** over one run (`lin_reply_run`,
`reply_once_run`; `Pure/Lin.lean`'s `lin_reply`, `reply_once` are these at `l1 ++ l2`).

A reply at label `n` is owned by an operation `o` of its kind created earlier at the same replica
with its key (`reply_owner`); `o` is placed with place at most the frontier after `n` (L2:
`l2_read`'s `reply_stores`, `l2_write_lb`), and its output is the reply's. The RMW side
(`rmw_once`, `rmw_l2'` in `PureLb/RmwL2.lean`, by the executed accounting `xinv` of `PureLb/ExInv.lean`).
-/
module

public import Dsverify.Proof.gryff.PureLb.Once
public import Dsverify.Proof.gryff.PureLb.RmwL2

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## The RMW side -/

/-- An RMW is replied to at most once: `handleExecuted` replies from the head proposal of the
instance's bookkeeping, owned by the RMW that created the instance, and once per instance (the
executed accounting, `rep_new`). -/
theorem rmw_reply_once {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n n' : Nat}
    (r1 : RepliesTo l n o) (r2 : RepliesTo l n' o) : n = n' :=
  rmw_once h ho hi r1 r2

/-- **L2 for RMWs**: a replied RMW is placed, at most the frontier after its reply.

The leader replies once two replicas executed the instance
(`numReplicasExecuted`, counted by `Executed` notices, each sent after its replica's
`ExecuteOverwrite` of the result: `HandleOverwrite`), so two stores hold at least the result's
tag; all executions agree (A1's `exec_same`), so `rmwPlace` is that tag. -/
theorem rmw_l2 {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n : Nat} (hr : RepliesTo l n o) :
    ∃ t, place l o = some t ∧ tagLe t.toP (front l (n + 1)) :=
  rmw_l2' h ho hi hr

/-! ## Reply uniqueness -/

/-- **An operation is replied to at most once** (in one run). -/
theorem reply_once_run {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {n n' : Nat} (r1 : RepliesTo l n o) (r2 : RepliesTo l n' o) : n = n' := by
  cases hi : o.inp with
  | read => exact reply_once_rw h ho (Or.inl hi) r1 r2
  | write v => exact reply_once_rw h ho (Or.inr ⟨v, hi⟩) r1 r2
  | cas a b => exact rmw_reply_once h ho hi r1 r2

/-! ## Writes -/

theorem write_l2 {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {v : w64} (hi : o.inp = .write v) {n : Nat} (hr : RepliesTo l n o) :
    ∃ t, place l o = some t ∧ tagLe t.toP (front l (n + 1)) := by
  obtain ⟨e, cn, s', outs, x, -, hc, -, -, -, -, ho', hxo, hxk, hfit⟩ := reply_is_own h ho hr
  cases x with
  | readReply => rw [hi] at hfit; exact hfit.elim
  | rmwReply => rw [hi] at hfit; exact hfit.elim
  | writeReply cid rid f =>
  simp only [Ext.key, Prod.mk.injEq] at hxk
  obtain ⟨rfl, rfl⟩ := hxk
  obtain ⟨m, w, wt, -, -, hk, hwt, -, -, -, hKeq, -, -⟩ := writeReply_owner hc hxo
  have hkey : o.key = shiftInts m.requestId m.clientId := by unfold Op.key; rw [hKeq]
  rw [← hkey] at hk
  have hwp := (wpinv hc.run o ho' v hi w hk).1
  rw [hwt] at hwp
  have hwp' : writePlace (l.take n ++ l.drop n) o = some wt := writePlace_append hwp
  rw [List.take_append_drop] at hwp'
  have hp : place l o = some wt := by unfold place; rw [hi]; exact hwp'
  exact ⟨wt, hp, l2_write_lb h ho hi hr hp⟩

/-! ## Reads -/

/-- Label `n` (at `r`) is `r`'s event number `|projR (l.take n) r|`. -/
theorem proj_at_label (l : List Label) {n : Nat} {r : Fin 3} {e : Ev} (hn : l[n]? = some (r, e)) :
    (projR l r)[(projR (l.take n) r).length]? = some e ∧
    (projR l r).take (projR (l.take n) r).length = projR (l.take n) r := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hn
  have h1 : projR l r = projR (l.take n) r ++ projR (l.drop n) r := by
    rw [← proj_append, List.take_append_drop]
  have h2 : l.drop n = [(r, e)] ++ l.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hlt, he]; rfl
  rw [h1, h2, proj_append, proj_single, if_pos rfl]
  constructor
  · simp
  · simp

/-- A read reply's step determines a tag (`readTag` is `some`). -/
theorem readTag_some {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {cid rid : w32} {v : w64} {f : w8}
    (hx : Out.ext (.readReply cid rid v f) ∈ outs) :
    ∃ t, readTag (stR cn R) (shiftInts rid cid) e = some t := by
  obtain ⟨hM, hR, -⟩ := rinv hc.run
  have hstep := hc.ok
  rcases readReply_src hstep hx with ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ <;>
    subst he <;> have hm := hc.recv _ rfl
  · cases hk : (stR cn R).rops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepRead1Reply_none hk hstep; cases hx
    | some rd =>
      obtain ⟨hfresh, hK, -, -⟩ := hR.rops R _ rd hk
      rw [hfresh] at hk
      obtain ⟨-, rfl⟩ := stepRead1Reply_fresh hk hstep
      simp only [List.mem_singleton, Out.ext.injEq, Ext.readReply.injEq] at hx
      obtain ⟨hc', hr', -, -⟩ := hx
      subst hc' hr'
      refine ⟨m.vt.t, ?_⟩
      simp only [readTag]
      rw [← hK, hk]
      simp [freshRead]
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
      rcases stepWrite2Reply_some hk hstep with ⟨-, rfl⟩ | ⟨wt, s1, outs', hwt, -, -, rfl⟩
      · cases hx
      exact ⟨wt, by simp [readTag, hk, hwt]⟩
  · exact (hM R _ hm).elim
  · exact (hM R _ hm).elim

/-- All read replies of a step carry the same value. -/
theorem readReply_same_v {l : List Label} {cn : Cfg gNet} {R : Fin 3} {e : Ev} {s' : RState}
    {outs : List Out} (hc : ReplyCtx l cn R e s' outs) {c1 r1 c2 r2 : w32} {v1 v2 : w64}
    {f1 f2 : w8} (hx1 : Out.ext (.readReply c1 r1 v1 f1) ∈ outs)
    (hx2 : Out.ext (.readReply c2 r2 v2 f2) ∈ outs) : v1 = v2 := by
  obtain ⟨hM, hR, -⟩ := rinv hc.run
  have hstep := hc.ok
  rcases readReply_src hstep hx1 with ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ <;>
    subst he <;> have hm := hc.recv _ rfl
  · cases hk : (stR cn R).rops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepRead1Reply_none hk hstep; cases hx1
    | some rd =>
      have hfresh := (hR.rops R _ rd hk).1
      rw [hfresh] at hk
      obtain ⟨-, rfl⟩ := stepRead1Reply_fresh hk hstep
      simp only [List.mem_singleton, Out.ext.injEq, Ext.readReply.injEq] at hx1 hx2
      rw [hx1.2.2.1, hx2.2.2.1]
  · exfalso
    cases hk : (stR cn R).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite1Reply_none hk hstep; cases hx1
    | some w =>
      obtain ⟨-, -, -, hwv, hwa⟩ := hR.wops R _ w (AMap.mem_of_get? hk)
      obtain ⟨w', -, -, -, -, -, -, -, hbr⟩ :=
        stepWrite1Reply_some hk hwv hwa (hM R _ hm) hstep
      rcases hbr with ⟨-, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      · cases hx1
      · simp at hx1
  · cases hk : (stR cn R).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite2Reply_none hk hstep; cases hx1
    | some w =>
      rcases stepWrite2Reply_some hk hstep with ⟨-, rfl⟩ | ⟨wt, s1, outs', hwt, hsc, -, rfl⟩
      · cases hx1
      have hin : ∀ {c r : w32} {v : w64} {f : w8},
          Out.ext (.readReply c r v f) ∈ outs' ++ [.ext (.writeReply w.clientId w.requestId 1)] →
          v = w.writeValue := by
        intro c r v f hx
        rcases List.mem_append.1 hx with hx | hx
        · rcases hsc with ⟨-, hsc⟩ | ⟨-, rfl⟩
          · obtain ⟨_, _, -, -, -, -, hsco⟩ := shortCircuit_spec hsc
            obtain ⟨_, _, hxe, -⟩ := hsco _ hx
            simp only [Out.ext.injEq, Ext.readReply.injEq] at hxe
            exact hxe.2.2.1
          · cases hx
        · simp at hx
      rw [hin hx1, hin hx2]
  · exact (hM R _ hm).elim
  · exact (hM R _ hm).elim

/-- The label of an operation's request is at its coordinator. -/
theorem op_label_lb {l : List Label} {o : Op} (ho : o ∈ ops l) : ∃ e, l[o.g]? = some (o.r, e) := by
  obtain ⟨-, hopAt⟩ := mem_ops.1 ho
  unfold opAt at hopAt
  split at hopAt
  · rename_i r0 e0 hl
    obtain ⟨_, _, ho'⟩ := Option.map_eq_some_iff.1 hopAt
    have h2 := congrArg Op.r ho'
    simp only at h2
    rw [← h2]; exact ⟨e0, hl⟩
  · cases hopAt

/-- **L2 for reads, at the reply**: a read replied to at `n` (reply value `v`) is placed, its
place at most the frontier after `n`, and its output is `v`. -/
theorem read_l2 {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) (hi : o.inp = .read) {n : Nat} (hr : RepliesTo l n o) {cid rid : w32}
    {v : w64} {f : w8} (hx : Ext.readReply cid rid v f ∈ extsAt l n)
    (hk : (cid, rid) = (o.cid, o.rid)) :
    ∃ t, place l o = some t ∧ tagLe t.toP (front l (n + 1)) ∧ opOut l o = .value v := by
  obtain ⟨hgn, hn, -⟩ := hr
  obtain ⟨⟨R, e⟩, hn', hR⟩ := Option.map_eq_some_iff.1 hn
  simp only at hR; subst hR
  obtain ⟨cn, s', outs, hc, houts, hcs, hR1, hR2⟩ := label_ctx h hn'
  have hxo := ext_mem_outs houts hx
  simp only [Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  -- the reply's index in the coordinator's projection
  obtain ⟨hes, htake⟩ := proj_at_label l hn'
  generalize hjn : (projR (l.take n) o.r).length = jn at hes htake
  have hjl : jn < (projR l o.r).length := (List.getElem?_eq_some_iff.1 hes).1
  have hst : stOf o.r ((projR l o.r).take jn) = stR cn o.r := by
    rw [htake, ← hcs]; rfl
  have houtsOf : outsOf o.r (projR l o.r) jn = outs := by
    unfold outsOf resOf; rw [hes]; simp only; rw [hst, hc.ok]
  have hoj : o.j + 1 ≤ jn := by
    obtain ⟨e0, he0⟩ := op_label_lb ho
    have h1 := proj_take_len_mono l o.r (show o.g + 1 ≤ n by omega)
    rw [List.take_add_one, he0] at h1
    change (projR (l.take o.g ++ [(o.r, e0)]) o.r).length ≤ _ at h1
    rw [proj_snoc, if_pos rfl, List.length_append, ← op_j ho] at h1
    simp at h1; omega
  -- `readReply l o` finds this reply first
  let g : Nat → Option (Nat × w64) := fun j' =>
    (extsIn (outsOf o.r (projR l o.r) j')).findSome? fun x => match x with
      | .readReply cid rid v _ => if (cid, rid) = (o.cid, o.rid) then some (j', v) else none
      | _ => none
  have hrr : readReply l o = firstFrom (o.j + 1) (projR l o.r).length g := rfl
  have hgjn : g jn ≠ none := by
    intro hg
    have := List.findSome?_eq_none_iff.1 hg (Ext.readReply o.cid o.rid v f) (by
      rw [houtsOf]; unfold extsIn; exact List.mem_filterMap.2 ⟨_, hxo, rfl⟩)
    simp at this
  obtain ⟨⟨j0, v0⟩, hfirst⟩ : ∃ y, firstFrom (o.j + 1) (projR l o.r).length g = some y := by
    unfold firstFrom
    cases hfs : ((List.range (projR l o.r).length).filter (o.j + 1 ≤ ·)).findSome? g with
    | some y => exact ⟨y, rfl⟩
    | none =>
      exact absurd (List.findSome?_eq_none_iff.1 hfs jn
        (by simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]; omega)) hgjn
  -- the first reply is this one (replies are unique)
  have hj0 : j0 = jn ∧ v0 = v := by
    unfold firstFrom at hfirst
    obtain ⟨j', hj1, hj2⟩ := List.exists_of_findSome?_eq_some hfirst
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj1
    obtain ⟨x, hx', hx2⟩ := List.exists_of_findSome?_eq_some hj2
    cases x with
    | readReply cid' rid' v' f' =>
      simp only at hx2
      split at hx2
      · rename_i hcr
        simp only [Option.some.injEq, Prod.mk.injEq] at hx2
        obtain ⟨hjj, hvv⟩ := hx2
        simp only [Prod.mk.injEq] at hcr
        obtain ⟨rfl, rfl⟩ := hcr
        rw [← hjj, ← hvv]
        cases he1 : (projR l o.r)[j']? with
        | none => exact absurd he1 (by rw [List.getElem?_eq_getElem hj1.1]; simp)
        | some e1 =>
          obtain ⟨n0, hn0, hpn⟩ := proj_index l o.r he1
          obtain ⟨cn0, s0, outs0, hc0, houts0, hcs0, -, -⟩ := label_ctx h hn0
          have hst0 : stOf o.r ((projR l o.r).take j') = stR cn0 o.r := by
            rw [← hpn, ← hcs0]; rfl
          have hout0 : outsOf o.r (projR l o.r) j' = outs0 := by
            unfold outsOf resOf; rw [he1]; simp only; rw [hst0, hc0.ok]
          have hx0 : Out.ext (.readReply o.cid o.rid v' f') ∈ outs0 := by
            rw [← hout0]
            unfold extsIn at hx'
            obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hx'
            cases y with
            | ext y => cases hy'; exact hy
            | send _ _ => cases hy'
          have hgn0 : o.g < n0 := by
            apply Nat.lt_of_not_le; intro hc'
            have h1 := proj_take_len_mono l o.r hc'
            rw [hpn, ← op_j ho, List.length_take] at h1
            omega
          have hr0 : RepliesTo l n0 o := ⟨hgn0, by rw [hn0]; rfl, _, by
            unfold extsAt extsIn; rw [houts0]; exact List.mem_filterMap.2 ⟨_, hx0, rfl⟩, rfl⟩
          have hr' : RepliesTo l n o := ⟨hgn, by rw [hn']; rfl, _, hx, rfl⟩
          have e0 : n0 = n := reply_once_rw h ho (Or.inl hi) hr0 hr'
          rw [e0] at hpn houts0
          have hlen := congrArg List.length hpn
          rw [hjn, List.length_take] at hlen
          have hoo : outs0 = outs := by rw [← houts0, ← houts]
          rw [hoo] at hx0
          exact ⟨by omega, readReply_same_v hc hx0 hxo⟩
      · cases hx2
    | _ => cases hx2
  obtain ⟨hj0, hv0⟩ := hj0
  rw [hj0, hv0] at hfirst
  -- the place: the step's `readTag`
  have hrr' : readReply l o = some (jn, v) := by rw [hrr]; exact hfirst
  obtain ⟨t, ht⟩ := readTag_some hc hxo
  have hpl : readPlace l o = some t := by
    unfold readPlace; rw [hrr']
    simp only [Option.bind_some]
    rw [hes]; simp only; rw [hst]; exact ht
  refine ⟨t, by unfold place; rw [hi]; exact hpl, ?_, by unfold opOut; rw [hi, hrr']; rfl⟩
  -- L2: two stores after the step
  rcases readReply_src hc.ok hxo with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
  · obtain ⟨q1, q2, hne, h1, h2⟩ := reply_stores hc.run (hc.recv _ rfl) hc.ok hxo ht
    have hq : ∀ q, (if q = o.r then s' else stR cn q) = cutSt l (n + 1) q := by
      intro q; split
      · rename_i hqr; rw [hqr]; exact hR1.symm
      · rw [hR2 q (by assumption), hcs]
    rw [hq] at h1 h2
    exact le_front_of_pair hne h1 h2

/-! ## (F3) -/

/-- **(F3) Replies** (in one run): a reply output at label `n` is to an operation created earlier
at the same replica with the reply's key and kind, linearized at cut `n + 1` with the reply's
output. -/
theorem lin_reply_run {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {n : Nat}
    (hn : n < l.length) {x : Ext} (hx : x ∈ extsAt l n) :
    ∃ o ∈ ops l, o.g < n ∧ (l[n]?).map Prod.fst = some o.r ∧ (o.cid, o.rid) = x.key ∧
      x.fits o.inp ∧ o ∈ lin l (n + 1) ∧ opOut l o = x.out := by
  obtain ⟨⟨R, e⟩, hn'⟩ : ∃ y, l[n]? = some y := ⟨_, List.getElem?_eq_getElem hn⟩
  obtain ⟨cn, s', outs, hc, houts, -, -, -⟩ := label_ctx h hn'
  have hxo := ext_mem_outs houts hx
  obtain ⟨o, ho', hor, hk, hfit⟩ := reply_owner hc hxo
  rw [← ops_take, List.mem_filter] at ho'
  obtain ⟨ho, hgn⟩ := ho'
  simp only [decide_eq_true_eq] at hgn
  subst hor
  have hlab : (l[n]?).map Prod.fst = some o.r := by rw [hn']; rfl
  have hr : RepliesTo l n o := ⟨hgn, hlab, x, hx, hk.symm⟩
  have hpl : ∃ t, place l o = some t ∧ tagLe t.toP (front l (n + 1)) ∧ opOut l o = x.out := by
    cases hi : o.inp with
    | read =>
      cases x with
      | readReply cid rid v f =>
        obtain ⟨t, a, b, d⟩ := read_l2 h ho hi hr hx hk.symm
        exact ⟨t, a, b, d⟩
      | _ => rw [hi] at hfit; exact hfit.elim
    | write v =>
      obtain ⟨t, a, b⟩ := write_l2 h ho hi hr
      refine ⟨t, a, b, ?_⟩
      unfold opOut; rw [hi]
      cases x with
      | writeReply => rfl
      | _ => rw [hi] at hfit; exact hfit.elim
    | cas a b =>
      obtain ⟨t, p1, p2⟩ := rmw_l2 h ho hi hr
      refine ⟨t, p1, p2, ?_⟩
      unfold opOut; rw [hi]
      cases x with
      | rmwReply => rfl
      | _ => rw [hi] at hfit; exact hfit.elim
  obtain ⟨t, hp, htag, hout⟩ := hpl
  refine ⟨o, ho, hgn, hlab, hk, hfit, ?_, hout⟩
  unfold lin
  rw [List.mem_mergeSort, List.mem_filter]
  refine ⟨ho, ?_⟩
  simp only [placeLe, hp, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, htag⟩

end Perennial.gryff.pure
