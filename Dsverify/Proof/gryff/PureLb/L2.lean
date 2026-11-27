/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/L2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **L2 for reads**: when a coordinator replies to a read, the read's place is at most the
frontier after the reply (two distinct stores hold at least the tag: the replier's and the
coordinator's, which overwrites with the reply; or, short-circuited, two `Write2` repliers').
-/
module

public import Dsverify.Proof.gryff.PureLb.L1Read

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

theorem le_front_of_pair {l : List Label} {k : Nat} {t : PTag} {w1 w2 : Fin 3} (hne : w1 ≠ w2)
    (h1 : tagLe t (cutSt l k w1).tag.toP) (h2 : tagLe t (cutSt l k w2).tag.toP) :
    tagLe t (front l k) := by
  unfold front
  apply le_median3_of_two
  match w1, w2, hne, h1, h2 with
  | 0, 0, hne, _, _ => exact absurd rfl hne
  | 1, 1, hne, _, _ => exact absurd rfl hne
  | 2, 2, hne, _, _ => exact absurd rfl hne
  | 0, 1, _, h1, h2 => exact Or.inl ⟨h1, h2⟩
  | 1, 0, _, h1, h2 => exact Or.inl ⟨h2, h1⟩
  | 0, 2, _, h1, h2 => exact Or.inr (Or.inl ⟨h1, h2⟩)
  | 2, 0, _, h1, h2 => exact Or.inr (Or.inl ⟨h2, h1⟩)
  | 1, 2, _, h1, h2 => exact Or.inr (Or.inr ⟨h1, h2⟩)
  | 2, 1, _, h1, h2 => exact Or.inr (Or.inr ⟨h2, h1⟩)

/-- At a read reply (from the configuration before it), two distinct replicas' stores after the
step hold at least the reply's tag. -/
theorem reply_stores {l : List Label} {cn : Cfg gNet} (hrun : GRun (Cfg.init gNet) l cn)
    {R : Fin 3} {m : Msg} {s' : RState} {outs : List Out}
    (hm : m ∈ infR cn R) (hstep : stepR R (stR cn R) (.msg m) = .ok (s', outs))
    {cid rid : w32} {v : w64} {f : w8} (hx : Out.ext (.readReply cid rid v f) ∈ outs)
    {t : model.Tag} (ht : readTag (stR cn R) (shiftInts rid cid) (.msg m) = some t) :
    ∃ q1 q2, q1 ≠ q2 ∧
      tagLe t.toP (if q1 = R then s' else stR cn q1).tag.toP ∧
      tagLe t.toP (if q2 = R then s' else stR cn q2).tag.toP := by
  obtain ⟨hM, hR, hW2⟩ := rinv hrun
  have hW := winv hrun
  have hmono : ∀ q, tagLe (stR cn q).tag.toP (if q = R then s' else stR cn q).tag.toP := by
    intro q; split
    · subst_vars; exact step_tag_mono hstep
    · exact tagLe_refl _
  rcases readReply_src hstep hx with ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ | ⟨m, he⟩ <;>
    cases he
  · cases hk : (stR cn R).rops.get? (shiftInts m.requestId m.clientId) with
    | none =>
      obtain ⟨-, rfl⟩ := stepRead1Reply_none hk hstep; cases hx
    | some rd =>
      obtain ⟨hfresh, hK, -, -⟩ := hR.rops R _ rd hk
      rw [hfresh] at hk
      obtain ⟨rfl, rfl⟩ := stepRead1Reply_fresh hk hstep
      simp only [List.mem_singleton, Out.ext.injEq, Ext.readReply.injEq] at hx
      obtain ⟨hc, hr, -, -⟩ := hx
      subst hc hr
      rw [← hK] at ht
      simp only [readTag, hk, freshRead, Option.bind_some, Bool.false_eq_true, if_false,
        Option.some.injEq] at ht
      subst ht
      obtain ⟨-, -, -, q, hq, hqt⟩ := hM R _ hm
      refine ⟨R, q, Ne.symm hq, ?_, ?_⟩
      · rw [if_pos rfl]; exact (overwrite_tag _ _ _).2
      · rw [if_neg hq]; exact hqt
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
      rcases stepWrite2Reply_some hk hstep with ⟨-, rfl⟩ | ⟨wt, s1, outs', hwt, hsc, -, rfl⟩
      · cases hx
      replace hx : Out.ext (.readReply cid rid v f) ∈ outs' := by
        rcases List.mem_append.1 hx with hx | hx
        · exact hx
        · simp at hx
      obtain ⟨hge, -⟩ : sge (w2bump w m.applied).numWrite2Applies (NHALF + 1) = true ∧
          shortCircuit (stR cn R) w.n ⟨w.writeValue, wt⟩ false = some (s1, outs') := by
        rcases hsc with hsc | ⟨-, rfl⟩
        · exact hsc
        · cases hx
      have ht' : t = wt := by
        simp only [readTag, hk, Option.bind_some, hwt, Option.some.injEq] at ht; exact ht.symm
      rw [ht']
      obtain ⟨hK, ⟨ow, how, howr, ⟨v0, howv⟩, howc, howq⟩, -⟩ := hR.wops R _ w (AMap.mem_of_get? hk)
      have hkey : ow.key = shiftInts m.requestId m.clientId := by
        unfold Op.key; rw [howc, howq, hK]
      obtain ⟨hmu, hmc⟩ := hM R _ hm
      obtain ⟨ea, eb⟩ := shiftInts_inj hmc (hW.1.ops ow how).2 (by rw [← hkey]; rfl)
      have hwr : w2rOf ow (.write2Reply m) = true := by simp [w2rOf, ea, eb]
      obtain ⟨sent, C, I, h1, h2, h3, h4, h5, h6, h7⟩ := hW2 ow how v0 howv
      have hmf : Msg.write2Reply m ∈ (infR cn ow.r).filter (w2rOf ow) :=
        List.mem_filter.2 ⟨howr ▸ hm, hwr⟩
      obtain ⟨p, hpI, hpg⟩ := List.mem_map.1 (h2.mem_iff.1 hmf)
      have happ : m.applied = if p.2 then 1 else 0 := by
        unfold w2rep at hpg; cases hpg; rfl
      obtain ⟨a, b, d, -⟩ := h7 w (by rw [howr, hkey]; exact hk)
      cases hsent : sent with
      | none => obtain ⟨-, hI⟩ := h5 hsent; rw [hI] at hpI; cases hpI
      | some gw =>
        obtain ⟨g2, wt0⟩ := gw
        have hwt0 := b g2 wt0 hsent
        rw [hwt] at hwt0; cases hwt0
        obtain ⟨-, hap⟩ := h6 g2 wt hsent
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
        have hL : ∀ q ∈ L, tagLe wt.toP (stR cn q.1).tag.toP := by
          intro q hq
          obtain ⟨hq, -⟩ := List.mem_filter.1 hq
          refine (hap q ?_).2
          rcases List.mem_append.1 hq with hq | hq
          · exact List.mem_append_left _ hq
          · rw [List.mem_singleton.1 hq]; exact List.mem_append_right _ hpI
        exact ⟨q1.1, q2.1, hne, tagLe_trans (hL q1 hq1) (hmono _),
          tagLe_trans (hL q2 hq2) (hmono _)⟩
  · exact (hM R _ hm).elim
  · exact (hM R _ hm).elim

/-- **L2 for reads**: a placed read is replied to at some label `n` after its creation, at its
coordinator, with its key, and its place is at most the frontier after that label. -/
theorem l2_read {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) (hi : o.inp = .read) {t : model.Tag} (ht : place l o = some t) :
    ∃ n, o.g < n ∧ (l[n]?).map Prod.fst = some o.r ∧
      (∃ v f, Ext.readReply o.cid o.rid v f ∈ extsAt l n) ∧ tagLe t.toP (front l (n + 1)) := by
  have ht' : readPlace l o = some t := by unfold place at ht; rw [hi] at ht; exact ht
  obtain ⟨n, e, hgn, hn, s', outs, hstep, houts, ⟨v, f, hx⟩, htag⟩ := readPlace_reply h ho ht'
  have hnl : n < l.length := (List.getElem?_eq_some_iff.1 hn).1
  obtain ⟨s'', o', hstep', hR1, hR2, -, hrecv⟩ := grun_label h hn
  rw [hstep] at hstep'; cases hstep'
  refine ⟨n, hgn, by rw [hn]; rfl, ⟨v, f, ?_⟩, ?_⟩
  · unfold extsAt extsIn; rw [houts]
    exact List.mem_filterMap.2 ⟨_, hx, rfl⟩
  rcases readReply_src hstep hx with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
  · obtain ⟨cn, hm, hrun⟩ := hrecv _ rfl
    have hcs : ∀ r, cutSt l n r = stR cn r := fun r => by
      rw [← cutSt_take (l := l) (Nat.le_refl n) r]
      have := cutSt_len hrun r
      change cutSt (l.take n) (l.take n).length r = stR cn r at this
      have hlen : (l.take n).length = n := by simp; omega
      rwa [hlen] at this
    rw [hcs] at hstep htag
    obtain ⟨q1, q2, hne, h1, h2⟩ := reply_stores hrun hm hstep hx htag
    have hq : ∀ q, (if q = o.r then s' else stR cn q) = cutSt l (n + 1) q := by
      intro q; split
      · rename_i hqr; rw [hqr]; exact hR1.symm
      · rw [hR2 q (by assumption), hcs]
    rw [hq] at h1 h2
    exact le_front_of_pair hne h1 h2

end Perennial.gryff.pure
