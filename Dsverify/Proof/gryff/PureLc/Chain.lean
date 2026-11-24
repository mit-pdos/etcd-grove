/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Chain.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: **the RMW chain** (`rmw_res_uniq`): each replica's execution results strictly increase
(`execSeq_sorted`: `PrevValTag` only moves at executions, to the result, which is above it), the
executed sequences are prefixes of one chain (unit A1's `exec_agree`), and distinct RMWs have
distinct instances (`rmwInst_inj`: an RMW request raises its replica's own instance counter, which
never decreases).
-/
module

public import Dsverify.Proof.gryff.PureLc.Exec
public import Dsverify.Proof.gryff.PureLc.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem mem_execSeq (r : Fin 3) {es : List Ev} {x : w32 × w32} {vt : ValTag} :
    (x, vt) ∈ execSeq r es ↔ ∃ j, es[j]? = some (.exec x.1 x.2) ∧ execRes (outsOf r es j) = some vt := by
  unfold execSeq
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, -, hj⟩
    split at hj
    · rename_i q i he
      obtain ⟨vt', hv, he'⟩ := Option.map_eq_some_iff.1 hj
      cases he'; exact ⟨j, he, hv⟩
    · cases hj
  · rintro ⟨j, hj, hv⟩
    refine ⟨j, List.mem_range.2 (List.getElem?_eq_some_iff.1 hj).1, ?_⟩
    rw [hj]; simp [hv]

section
variable {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
include h

/-- Induction along a replica's projection. -/
theorem proj_ind (P : Nat → RState → Prop) (h0 : P 0 (stOf r []))
    (hs : ∀ j e s' o, (projR l r)[j]? = some e →
      stepR r (stOf r ((projR l r).take j)) e = .ok (s', o) →
      P j (stOf r ((projR l r).take j)) → P (j + 1) s') :
    ∀ j, j ≤ (projR l r).length → P j (stOf r ((projR l r).take j)) := by
  intro j
  induction j with
  | zero => intro _; simpa using h0
  | succ j ih =>
    intro hj
    have hlt : j < (projR l r).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (projR l r)[j]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨n, s', o, -, -, hs1, hs2, -⟩ := proj_step h he
    rw [hs2]
    exact hs j e s' o he hs1 (ih (by omega))

/-- A replica's id and instance counters' length along its projection. -/
theorem proj_id (j : Nat) (hj : j ≤ (projR l r).length) :
    (stOf r ((projR l r).take j)).id = rid32 r ∧
      (stOf r ((projR l r).take j)).crtInstance.length = 3 := by
  refine proj_ind h r (fun _ s => s.id = rid32 r ∧ s.crtInstance.length = 3) ⟨rfl, rfl⟩ ?_ j hj
  intro j e s' o _ hs ih
  exact ⟨(step_pc hs).1.trans ih.1, (step_crt_len hs).trans ih.2⟩

/-- An execution with a result at index `j`: `PrevValTag` becomes the result, which is above the
previous `PrevValTag`. -/
theorem exec_at {j : Nat} {q i : w32} (hj : (projR l r)[j]? = some (.exec q i)) {vt : ValTag}
    (hv : execRes (outsOf r (projR l r) j) = some vt) :
    (stOf r ((projR l r).take (j + 1))).prevValTag = some vt ∧
      ∀ p, (stOf r ((projR l r).take j)).prevValTag = some p → tagLt p.t.toP vt.t.toP := by
  obtain ⟨n, s', o, -, hc, hs, hs2, ho⟩ := proj_step h hj
  rw [ho] at hv
  change stepExec _ q i = _ at hs
  have hp := stepExec_pc hs
  rw [hs2]
  refine ⟨?_, fun p hp' => ?_⟩
  · rcases hp.2.2 with ⟨hn, -⟩ | ⟨vt', hv', hpv⟩
    · rw [hn] at hv; cases hv
    · rw [hv] at hv'; cases hv'; exact hpv
  · obtain ⟨cp, c0, rest, hcp, -, -, vt0, hor, -, hle, htt, -⟩ := stepExec_full hs hv
    obtain ⟨hb1, hb2⟩ := rmwc_bounded h n r
    rw [hc] at hb1 hb2
    have hbound : sint.Z vt0.t.rmwc < 2 ^ 31 - 1 := by
      rcases hor with e | e
      · rw [e]; exact hb2 _ _ _ hcp
      · exact hb1 _ e
    rw [htt]
    exact tagLt_of_le_of_lt (hle p hp') (tagLt_rmwc_succ _ hbound)

/-- `PrevValTag` only grows along a projection. -/
theorem prev_mono {j : Nat} {a : ValTag} (ha : (stOf r ((projR l r).take j)).prevValTag = some a) :
    ∀ d, j + d ≤ (projR l r).length → ∃ b, (stOf r ((projR l r).take (j + d))).prevValTag = some b ∧
      tagLe a.t.toP b.t.toP := by
  intro d
  induction d with
  | zero => intro _; exact ⟨a, ha, tagLe_refl _⟩
  | succ d ih =>
    intro hd
    obtain ⟨b, hb, hab⟩ := ih (by omega)
    have hlt : j + d < (projR l r).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (projR l r)[j + d]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [← Nat.add_assoc]
    by_cases hx : ∃ q i, e = .exec q i
    · obtain ⟨q, i, rfl⟩ := hx
      cases hv : execRes (outsOf r (projR l r) (j + d)) with
      | some vt =>
        obtain ⟨h1, h2⟩ := exec_at h r he hv
        exact ⟨vt, h1, tagLe_trans hab (tagLe_of_lt (h2 b hb))⟩
      | none =>
        obtain ⟨n, s', o, -, -, hs, hs2, ho⟩ := proj_step h he
        change stepExec _ q i = _ at hs
        rw [ho] at hv
        rcases (stepExec_pc hs).2.2 with ⟨-, hpv⟩ | ⟨vt', hv', -⟩
        · rw [hs2, hpv]; exact ⟨b, hb, hab⟩
        · rw [hv] at hv'; cases hv'
    · obtain ⟨n, s', o, -, -, hs, hs2, -⟩ := proj_step h he
      have := (step_pc hs).2.2 (fun q i e' => hx ⟨q, i, e'⟩)
      rw [hs2, this]; exact ⟨b, hb, hab⟩

/-- **A replica's execution results strictly increase.** -/
theorem execSeq_sorted :
    (execSeq r (projR l r)).Pairwise fun x y => tagLt x.2.t.toP y.2.t.toP := by
  unfold execSeq
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  · intro j j' hjj x hx y hy
    split at hx
    · rename_i q i he
      split at hy
      · rename_i q' i' he'
        obtain ⟨vt, hv, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨vt', hv', rfl⟩ := Option.map_eq_some_iff.1 hy
        have hlt' : j' < (projR l r).length := (List.getElem?_eq_some_iff.1 he').1
        obtain ⟨h1, -⟩ := exec_at h r he hv
        obtain ⟨b, hb, hab⟩ := prev_mono h r h1 (j' - (j + 1)) (by omega)
        rw [show j + 1 + (j' - (j + 1)) = j' by omega] at hb
        exact tagLt_of_le_of_lt hab ((exec_at h r he' hv').2 b hb)
      · cases hy
    · cases hx

/-- The instance counters only grow along a projection. -/
theorem crt_mono {j : Nat} (q : w32) :
    ∀ d, j + d ≤ (projR l r).length → sint.Z ((stOf r ((projR l r).take j)).crt q) ≤
      sint.Z ((stOf r ((projR l r).take (j + d))).crt q) := by
  intro d
  induction d with
  | zero => intro _; exact Int.le_refl _
  | succ d ih =>
    intro hd
    have hlt : j + d < (projR l r).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (projR l r)[j + d]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨n, s', o, -, -, hs, hs2, -⟩ := proj_step h he
    rw [← Nat.add_assoc, hs2]
    exact Int.le_trans (ih (by omega)) ((step_pc hs).2.1 q)

end

theorem rid32_toNat (r : Fin 3) : (rid32 r).toNat = r.val := by revert r; decide

theorem pairwise_eq {α : Type} {R : α → α → Prop} {L : List α} (hL : L.Pairwise R) {a b : α}
    (ha : a ∈ L) (hb : b ∈ L) (h1 : ¬ R a b) (h2 : ¬ R b a) : a = b := by
  induction hL with
  | nil => cases ha
  | @cons c L' hc _ ih =>
    have ha' := List.mem_cons.1 ha; have hb' := List.mem_cons.1 hb; clear ha hb
    rcases ha' with ha | ha <;> rcases hb' with hb | hb
    · rw [ha, hb]
    · subst ha; exact absurd (hc b hb) h1
    · subst hb; exact absurd (hc a ha) h2
    · exact ih ha hb

theorem proj_cons_drop (l : List Label) (r : Fin 3) {g : Nat} {e : Ev} (hg : l[g]? = some (r, e)) :
    (projR l r)[(projR (l.take g) r).length]? = some e := by
  have hlt := (List.getElem?_eq_some_iff.1 hg).1
  have hl : l = l.take g ++ (r, e) :: l.drop (g + 1) := by
    conv => lhs; rw [← List.take_append_drop g l]
    rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hg).2]
  have e1 : projR l r = projR (l.take g ++ [(r, e)] ++ l.drop (g + 1)) r :=
    congrArg (projR · r) (by rw [List.append_assoc, List.singleton_append]; exact hl)
  rw [e1, proj_append, proj_append, proj_single, if_pos rfl,
    List.getElem?_append_left (by simp), List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem op_label {l : List Label} {o : Op} (ho : o ∈ ops l) :
    ∃ e, l[o.g]? = some (o.r, e) ∧ e.clientReq = some (o.cid, o.rid, o.inp) ∧
      o.j = (projR (l.take o.g) o.r).length := by
  have := (mem_ops.1 ho).2
  unfold opAt at this
  split at this
  · rename_i r e he
    obtain ⟨x, hx, ho'⟩ := Option.map_eq_some_iff.1 this
    have e1 : o.r = r := by rw [← ho']
    have e2 : (o.cid, o.rid, o.inp) = x := by rw [← ho']
    have e3 : o.j = (projR (l.take o.g) r).length := by rw [← ho']
    rw [e1, e3, e2]; exact ⟨e, he, hx, rfl⟩
  · cases this

theorem op_rmw {l : List Label} {o : Op} (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) :
    ∃ k d, l[o.g]? = some (o.r, .rmw o.rid o.cid k d a b) ∧
      o.j = (projR (l.take o.g) o.r).length := by
  obtain ⟨e, he, hc, hj⟩ := op_label ho
  rw [hi] at hc
  cases e with
  | rmw rid cid k d oldV newV =>
    simp only [Ev.clientReq, Option.some.injEq, Prod.mk.injEq,
      dsverify_lab.harness.RegInput.cas.injEq] at hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    exact ⟨k, d, he, hj⟩
  | _ => simp [Ev.clientReq] at hc

/-- Two operations at one replica with the same projection index are the same. -/
theorem op_j_inj {l : List Label} {o o' : Op} (ho : o ∈ ops l) (ho' : o' ∈ ops l)
    (hr : o.r = o'.r) (hj : o.j = o'.j) : o = o' := by
  obtain ⟨e, he, -, hje⟩ := op_label ho
  obtain ⟨e', he', -, hje'⟩ := op_label ho'
  have key : ∀ {a b : Op} {ea eb : Ev}, l[a.g]? = some (a.r, ea) → a.r = b.r → a.g < b.g →
      (projR (l.take a.g) a.r).length < (projR (l.take b.g) b.r).length := by
    intro a b ea eb ha hr hlt
    have et : l.take (a.g + 1) = l.take a.g ++ [(a.r, ea)] := by rw [List.take_add_one, ha]; rfl
    have := proj_take_len_mono l a.r (show a.g + 1 ≤ b.g by omega)
    rw [et, proj_snoc, if_pos rfl, List.length_append] at this
    rw [← hr]; simp at this; omega
  rcases Nat.lt_trichotomy o.g o'.g with hlt | heq | hlt
  · have := key (eb := e') he hr hlt; omega
  · exact ops_g_inj ho ho' heq
  · have := key (eb := e) he' hr.symm hlt; omega

/-- **Distinct RMWs have distinct instances.** -/
theorem rmwInst_inj {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o o' : Op}
    (ho : o ∈ ops l) (ho' : o' ∈ ops l) {a b a' b' : w64} (hi : o.inp = .cas a b)
    (hi' : o'.inp = .cas a' b') (he : rmwInst l o = rmwInst l o') : o = o' := by
  unfold rmwInst at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨hr, hc⟩ := he
  have hr := rid32_inj hr
  -- the request of `a` raises the counter strictly before `b`'s
  have key : ∀ {x y : Op} {ax bx : w64}, x ∈ ops l → x.inp = .cas ax bx → y ∈ ops l → x.r = y.r →
      x.j < y.j → sint.Z ((stOf x.r ((projR l x.r).take x.j)).crt (rid32 x.r)) <
        sint.Z ((stOf y.r ((projR l y.r).take y.j)).crt (rid32 y.r)) := by
    intro x y ax bx hx hix hy hxy hlt
    obtain ⟨k, d, hl, hj⟩ := op_rmw hx hix
    have hp := proj_cons_drop l x.r hl
    rw [← hj] at hp
    obtain ⟨n, s', o1, -, -, hs, hs2, -⟩ := proj_step h hp
    obtain ⟨hid, hlen⟩ := proj_id h x.r x.j (by have := (List.getElem?_eq_some_iff.1 hp).1; omega)
    have h1 := stepRMW_crt hs (by rw [hlen, hid, rid32_toNat]; exact x.r.isLt)
    rw [hid, ← hs2] at h1
    have hylt : y.j ≤ (projR l y.r).length := by
      obtain ⟨_, hl', hj'⟩ := op_label hy
      have := (List.getElem?_eq_some_iff.1 (proj_cons_drop l y.r hl')).1; omega
    have h2 := crt_mono h x.r (j := x.j + 1) (rid32 x.r) (y.j - (x.j + 1)) (by rw [hxy]; omega)
    rw [show x.j + 1 + (y.j - (x.j + 1)) = y.j by omega] at h2
    rw [← hxy]; omega
  rcases Nat.lt_trichotomy o.j o'.j with hlt | heq | hlt
  · have := key ho hi ho' hr hlt; rw [hc] at this; exact absurd this (Int.lt_irrefl _)
  · exact op_j_inj ho ho' hr heq
  · have := key ho' hi' ho hr.symm hlt; rw [hc] at this; exact absurd this (Int.lt_irrefl _)

theorem rmwRes_mem {l : List Label} {o : Op} {vt : ValTag} (hr : rmwRes l o = some vt) :
    ∃ r, (rmwInst l o, vt) ∈ execSeq r (projR l r) := by
  unfold rmwRes at hr
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some hr
  refine ⟨r, ?_⟩
  unfold execVT at hr
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some hr
  split at hj
  · rename_i q i he
    split at hj
    · rename_i hx
      rw [mem_execSeq r]
      refine ⟨j, ?_, hj⟩
      rw [he, ← hx]
    · cases hj
  · cases hj

/-- **RMWs' results are distinct** (the chain). -/
theorem rmw_res_uniq {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o o' : Op}
    (ho : o ∈ ops l) (ho' : o' ∈ ops l) {a b a' b' : w64} (hi : o.inp = .cas a b)
    (hi' : o'.inp = .cas a' b') {vt vt' : ValTag} (hr : rmwRes l o = some vt)
    (hr' : rmwRes l o' = some vt') (he : vt.t = vt'.t) : o = o' := by
  obtain ⟨r, hm⟩ := rmwRes_mem hr
  obtain ⟨r', hm'⟩ := rmwRes_mem hr'
  have hne : ∀ {x y : (w32 × w32) × ValTag}, x.2.t = y.2.t → ¬ tagLt x.2.t.toP y.2.t.toP :=
    fun e h' => tagLt_irrefl _ (e ▸ h')
  have key : ∀ (L : List ((w32 × w32) × ValTag)), L.Pairwise (fun x y => tagLt x.2.t.toP y.2.t.toP) →
      (rmwInst l o, vt) ∈ L → (rmwInst l o', vt') ∈ L → o = o' := by
    intro L hL h1 h2
    have := pairwise_eq hL h1 h2 (hne he) (hne he.symm)
    simp only [Prod.mk.injEq] at this
    exact rmwInst_inj h ho ho' hi hi' this.1
  rcases exec_agree h r r' with hp | hp
  · exact key _ (execSeq_sorted h r') (hp.subset hm) hm'
  · exact key _ (execSeq_sorted h r) hm (hp.subset hm')

end Perennial.gryff.pure
