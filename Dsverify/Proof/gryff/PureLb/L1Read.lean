/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/L1Read.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **L1 for reads** from the read-record invariant (`l1_read_of_inv`): the event that
replies to a read is its record's first `Read1Reply` (whose tag is at least the replier's and the
coordinator's stores at the read's creation), or a write's `Write2Reply` completing the write
with two appliers (each applier's store at the `Write2`s' sending, after the read's creation, was
below the write's tag). A `Write1Reply` never replies to a read, no `Read2Reply` exists.
-/
module

public import Dsverify.Proof.gryff.PureLb.RInv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem two_distinct' {α : Type} {L : List (Fin 3 × α)} (hn : (L.map Prod.fst).Nodup)
    (hl : 2 ≤ L.length) : ∃ p1 ∈ L, ∃ p2 ∈ L, p1.1 ≠ p2.1 := by
  match L, hl with
  | p1 :: p2 :: rest, _ =>
    refine ⟨p1, by simp, p2, by simp, ?_⟩
    intro h
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn
    exact hn.1 (Or.inl h)

theorem not_ext_mem_send {x : Ext} {d : Fin 3} {m : Msg} : Out.ext x ∉ [Out.send d m] := by
  simp

theorem noR_not_readReply {o : List Out} (h : NoR o) {cid rid : w32} {v : w64} {f : w8} :
    Out.ext (.readReply cid rid v f) ∉ o := fun hx => by
  have := h _ hx; simp [isROut] at this

/-- The events whose outputs can contain a read reply. -/
theorem readReply_src {r : Fin 3} {s s' : RState} {e : Ev} {outs : List Out} {cid rid : w32}
    {v : w64} {f : w8} (h : stepR r s e = .ok (s', outs))
    (hx : Out.ext (.readReply cid rid v f) ∈ outs) :
    (∃ m, e = .msg (.read1Reply m)) ∨ (∃ m, e = .msg (.write1Reply m)) ∨
    (∃ m, e = .msg (.write2Reply m)) ∨ (∃ m, e = .msg (.read2 m)) ∨
    (∃ m, e = .msg (.read2Reply m)) := by
  cases e with
  | read =>
    obtain ⟨-, -, -, -, -, ho⟩ := stepClientRead_spec' h
    obtain ⟨dd, hdd, -⟩ := ho _ hx; cases hdd
  | write => exact absurd hx (noR_not_readReply (stepClientWrite_spec' h).2.2.2.2)
  | rmw => exact absurd hx (noR_not_readReply (stepClientRMW_fr h).2.2.2.2.2)
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
    | _ => exact absurd hx (noR_not_readReply (step_fr_other h rfl).2)
  | _ => exact absurd hx (noR_not_readReply (step_fr_other h rfl).2)

/-- A reply at label `n` to read `o`, from the configuration before it: its tag is at least two
distinct stores at `o`'s creation. -/
theorem read_reply_tag {l : List Label} {cn : Cfg gNet} (hrun : GRun (Cfg.init gNet) l cn)
    {o : Op} (ho : o ∈ ops l) {m : Msg} {s' : RState} {outs : List Out}
    (hm : m ∈ infR cn o.r) (hstep : stepR o.r (stR cn o.r) (.msg m) = .ok (s', outs))
    {v : w64} {f : w8} (hx : Out.ext (.readReply o.cid o.rid v f) ∈ outs) {t : model.Tag}
    (ht : readTag (stR cn o.r) o.key (.msg m) = some t) :
    ∃ q1 q2, q1 ≠ q2 ∧ tagLe (cutSt l o.g q1).tag.toP t.toP ∧
      tagLe (cutSt l o.g q2).tag.toP t.toP := by
  obtain ⟨hM, hR, hW2⟩ := rinv hrun
  have hW := winv hrun
  have hoc := (hW.1.ops o ho).2
  rcases readReply_src hstep hx with ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ <;>
    cases he
  · -- the read's first `Read1Reply`
    cases hk : (stR cn o.r).rops.get? (shiftInts m.requestId m.clientId) with
    | none =>
      obtain ⟨-, rfl⟩ := stepRead1Reply_none hk hstep; cases hx
    | some rd =>
      obtain ⟨hfresh, hK, -, -⟩ := hR.rops o.r _ rd hk
      rw [hfresh] at hk
      obtain ⟨-, rfl⟩ := stepRead1Reply_fresh hk hstep
      simp only [List.mem_singleton, Out.ext.injEq, Ext.readReply.injEq] at hx
      obtain ⟨hc, hr, -, -⟩ := hx
      have hkey : o.key = shiftInts m.requestId m.clientId := by
        unfold Op.key; rw [hK, hc, hr]
      obtain ⟨hmu, hmc, hmt, -⟩ := hM o.r _ hm
      obtain ⟨ea, eb⟩ := shiftInts_inj hmc hoc hkey.symm
      rw [hkey] at ht
      simp only [readTag, hk, freshRead, Option.bind_some, Bool.false_eq_true, if_false,
        Option.some.injEq] at ht
      subst ht
      obtain ⟨q, hq, h1, h2⟩ := hmt o ho rfl eb.symm ea.symm
      exact ⟨q, o.r, hq, h1, h2⟩
  · -- a `Write1Reply` never replies to a read
    exfalso
    cases hk : (stR cn o.r).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite1Reply_none hk hstep; cases hx
    | some w =>
      obtain ⟨-, -, -, hwv, hwa⟩ := hR.wops o.r _ w (AMap.mem_of_get? hk)
      obtain ⟨w', -, -, -, -, -, -, -, hbr⟩ :=
        stepWrite1Reply_some hk hwv hwa (hM o.r _ hm) hstep
      rcases hbr with ⟨-, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      · cases hx
      · simp at hx
  · -- a write's `Write2Reply` short-circuits the read
    cases hk : (stR cn o.r).wops.get? (shiftInts m.requestId m.clientId) with
    | none => obtain ⟨-, rfl⟩ := stepWrite2Reply_none hk hstep; cases hx
    | some w =>
      rcases stepWrite2Reply_some hk hstep with ⟨-, rfl⟩ | ⟨wt, s1, outs', hwt, hsc, -, rfl⟩
      · cases hx
      replace hx : Out.ext (.readReply o.cid o.rid v f) ∈ outs' := by
        rcases List.mem_append.1 hx with hx | hx
        · exact hx
        · simp at hx
      obtain ⟨hge, hsc⟩ : sge (w2bump w m.applied).numWrite2Applies (NHALF + 1) = true ∧
          shortCircuit (stR cn o.r) w.n ⟨w.writeValue, wt⟩ false = some (s1, outs') := by
        rcases hsc with hsc | ⟨-, rfl⟩
        · exact hsc
        · cases hx
      obtain ⟨_, _, -, -, -, -, hsco⟩ := shortCircuit_spec hsc
      obtain ⟨cid', rid', hxe, op, hop, k, hk', e', he', hec, her, rd, hrd⟩ := hsco _ hx
      simp only [Out.ext.injEq, Ext.readReply.injEq] at hxe
      obtain ⟨hc', hr', -, -⟩ := hxe
      subst hc' hr'
      -- the tag
      have ht' : t = wt := by
        simp only [readTag, hk, Option.bind_some, hwt, Option.some.injEq] at ht; exact ht.symm
      rw [ht']
      -- the write
      obtain ⟨hK, ⟨ow, how, howr, ⟨v0, howv⟩, howc, howq⟩, -⟩ := hR.wops o.r _ w (AMap.mem_of_get? hk)
      have hkey : ow.key = shiftInts m.requestId m.clientId := by
        unfold Op.key; rw [howc, howq, hK]
      obtain ⟨hmu, hmc⟩ := hM o.r _ hm
      obtain ⟨ea, eb⟩ := shiftInts_inj hmc (hW.1.ops ow how).2 (by rw [← hkey]; rfl)
      have hwr : w2rOf ow (.write2Reply m) = true := by simp [w2rOf, ea, eb]
      obtain ⟨sent, C, I, h1, h2, h3, h4, h5, h6, h7⟩ := hW2 ow how v0 howv
      have hmf : Msg.write2Reply m ∈ (infR cn ow.r).filter (w2rOf ow) :=
        List.mem_filter.2 ⟨howr ▸ hm, hwr⟩
      obtain ⟨p, hpI, hpg⟩ := List.mem_map.1 (h2.mem_iff.1 hmf)
      have happ : m.applied = if p.2 then 1 else 0 := by
        unfold w2rep at hpg; cases hpg; rfl
      obtain ⟨a, b, d, sh, -⟩ := h7 w (by rw [howr, hkey]; exact hk)
      cases hsent : sent with
      | none => obtain ⟨-, hI⟩ := h5 hsent; rw [hI] at hpI; cases hpI
      | some gw =>
        obtain ⟨g2, wt0⟩ := gw
        have hwt0 := b g2 wt0 hsent
        rw [hwt] at hwt0; cases hwt0
        obtain ⟨hg2, hap⟩ := h6 g2 wt hsent
        -- the read was created before the `Write2`s were sent
        have hog : o.g < g2 := sh op (by rw [howr]; exact hop) k hk' e' (by rw [howr]; exact he')
          (by rw [howr, hec, her, hrd]; rfl) o ho howr.symm hec.symm her.symm g2 wt hsent
        -- two distinct appliers
        have hperm : (C ++ [p] ++ I.erase p).Perm (C ++ I) := by
          rw [List.append_assoc]
          exact List.Perm.append_left C (List.perm_cons_erase hpI).symm
        have hn3 : ((C ++ [p] ++ I.erase p).map Prod.fst).Nodup :=
          (hperm.map Prod.fst).nodup_iff.2 h1
        rw [List.map_append] at hn3
        have hnC : ((C ++ [p]).map Prod.fst).Nodup := hn3.sublist (List.sublist_append_left _ _)
        have hClen : C.length ≤ 3 := by
          have := nodup_fin3_len hnC; simp at this; omega
        have hCf : (C.filter (·.2)).length ≤ 3 := Nat.le_trans (List.length_filter_le _ _) hClen
        have h2le := sge_two hge
        simp only [w2bump, happ, sgt_applied] at h2le
        let L := (C ++ [p]).filter (·.2)
        have hLn : (L.map Prod.fst).Nodup := hnC.sublist (List.Sublist.map _ List.filter_sublist)
        have hLl : 2 ≤ L.length := by
          simp only [L, List.filter_append]
          cases hp2 : p.2
          · rw [hp2] at h2le; simp only [Bool.false_eq_true, ite_false] at h2le
            rw [d] at h2le; simp [hp2]; omega
          · rw [hp2] at h2le; simp only [ite_true] at h2le
            rw [Z_succ64 d (by omega) (by omega)] at h2le
            simp [hp2]; omega
        obtain ⟨q1, hq1, q2, hq2, hne⟩ := two_distinct' hLn hLl
        have hL : ∀ q ∈ L, tagLt (cutSt l g2 q.1).tag.toP wt.toP := by
          intro q hq
          obtain ⟨hq, hq2⟩ := List.mem_filter.1 hq
          refine (hap q ?_).1 (by simpa using hq2)
          rcases List.mem_append.1 hq with hq | hq
          · exact List.mem_append_left _ hq
          · rw [List.mem_singleton.1 hq]; exact List.mem_append_right _ hpI
        have hle : ∀ q, tagLe (cutSt l o.g q).tag.toP (cutSt l g2 q).tag.toP :=
          fun q => cut_tag_mono hrun q (Nat.le_of_lt hog)
        exact ⟨q1.1, q2.1, hne, tagLe_of_lt (tagLt_of_le_of_lt (hle _) (hL q1 hq1)),
          tagLe_of_lt (tagLt_of_le_of_lt (hle _) (hL q2 hq2))⟩
  · exact (hM o.r _ hm).elim
  · exact (hM o.r _ hm).elim

theorem op_j {l : List Label} {o : Op} (ho : o ∈ ops l) :
    o.j = (projR (l.take o.g) o.r).length := by
  obtain ⟨-, hopAt⟩ := mem_ops.1 ho
  unfold opAt at hopAt; split at hopAt
  · obtain ⟨_, _, ho'⟩ := Option.map_eq_some_iff.1 hopAt
    have h1 := congrArg Op.j ho'; have h2 := congrArg Op.r ho'
    simp only at h1 h2
    rw [← h1, ← h2]
  · cases hopAt

/-- A read's place comes from a label `n` after its creation, at its coordinator, whose step
outputs a reply with the read's key; the place is that step's `readTag`. -/
theorem readPlace_reply {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {t : model.Tag} (ht : readPlace l o = some t) :
    ∃ n e, o.g < n ∧ l[n]? = some (o.r, e) ∧ ∃ s' outs,
      stepR o.r (cutSt l n o.r) e = .ok (s', outs) ∧ outsAt l n = outs ∧
      (∃ v f, Out.ext (.readReply o.cid o.rid v f) ∈ outs) ∧
      readTag (cutSt l n o.r) o.key e = some t := by
  unfold readPlace at ht
  obtain ⟨⟨j', v⟩, hrr, hj⟩ := Option.bind_eq_some_iff.1 ht
  simp only at hj
  cases he : (projR l o.r)[j']? with
  | none => rw [he] at hj; cases hj
  | some e =>
    rw [he] at hj
    simp only at hj
    unfold readReply firstFrom at hrr
    obtain ⟨j'', hj1, hj2⟩ := List.exists_of_findSome?_eq_some hrr
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj1
    obtain ⟨x, hx, hx2⟩ := List.exists_of_findSome?_eq_some hj2
    cases x with
    | readReply cid rid v' f' =>
      simp only at hx2
      split at hx2
      · rename_i hcr
        cases hx2
        simp only [Prod.mk.injEq] at hcr
        obtain ⟨rfl, rfl⟩ := hcr
        obtain ⟨n, hn, hpn⟩ := proj_index l o.r he
        obtain ⟨s', outs, hstep, -, -, houts, -⟩ := grun_label h hn
        have hst : stOf o.r ((projR l o.r).take j') = cutSt l n o.r := by unfold cutSt; rw [hpn]
        have hout : outsOf o.r (projR l o.r) j' = outs := by
          unfold outsOf resOf; rw [he]; simp only; rw [hst, hstep]
        refine ⟨n, e, ?_, hn, s', outs, hstep, houts, ⟨v, f', ?_⟩, by rw [← hst]; exact hj⟩
        · apply Nat.lt_of_not_le; intro hc
          have h1 := proj_take_len_mono l o.r hc
          rw [hpn, ← op_j ho, List.length_take] at h1
          omega
        · rw [← hout]
          unfold extsIn at hx
          obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hx
          cases y with
          | ext y => cases hy'; exact hy
          | send _ _ => cases hy'
      · cases hx2
    | _ => cases hx2

/-- **L1 for reads** from the read-record invariant. -/
theorem l1_read_of_inv {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) (hi : o.inp = .read) {t : model.Tag}
    (ht : place l o = some t) : tagLe (front l o.g) t.toP := by
  have ht' : readPlace l o = some t := by unfold place at ht; rw [hi] at ht; exact ht
  obtain ⟨n, e, hgn, hn, s', outs, hstep, -, ⟨v, f, hx⟩, htag⟩ := readPlace_reply h ho ht'
  have hnl : n < l.length := (List.getElem?_eq_some_iff.1 hn).1
  obtain ⟨_, _, -, -, -, -, hrecv⟩ := grun_label h hn
  rcases readReply_src hstep hx with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
  · obtain ⟨cn, hm, hrun⟩ := hrecv _ rfl
    have hcs : ∀ r, cutSt l n r = stR cn r := fun r => by
      rw [← cutSt_take (l := l) (Nat.le_refl n) r]
      have := cutSt_len hrun r
      change cutSt (l.take n) (l.take n).length r = stR cn r at this
      have hlen : (l.take n).length = n := by simp; omega
      rwa [hlen] at this
    have ho' : o ∈ ops (l.take n) := by
      rw [← ops_take, List.mem_filter]; exact ⟨ho, by simp; omega⟩
    rw [hcs] at hstep htag
    obtain ⟨q1, q2, hne, h1, h2⟩ := read_reply_tag hrun ho' hm hstep hx htag
    change tagLe (cutSt (l.take n) o.g q1).tag.toP t.toP at h1
    change tagLe (cutSt (l.take n) o.g q2).tag.toP t.toP at h2
    rw [cutSt_take (l := l) (Nat.le_of_lt hgn)] at h1 h2
    exact median3_le_of_pair hne h1 h2

end Perennial.gryff.pure
