/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/LinWitness.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L1, `lin_now`'s combinatorial half (notes/prophecy-client.md §3a): from a witness order `L0`
of the history (distinct invoked commands, every accepted one with its result, and real time
along conflict chains: `Witness`), a linearization. `L` is `L0` stably sorted by `tau`: the latest
invocation among a command's conflict-chain predecessors in `L0`. Sorting keeps every
conflicting pair's order (so every result: `resultIn` through the last put, `resultIn_lastPut`)
and puts an accepted command before every command invoked after its acceptance.

The protocol's half (a witness exists for a history with `HistOk`: the top ballot's leader order)
is `lin_now`'s remaining obligation (Lin.lean).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Lin
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.NewBase

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

open Classical
open scoped List

/-! ## Orders of a sequence with distinct ids -/

theorem sublist_pair_of_precedes : ∀ (s : Seq), (s.map Prod.fst).Nodup → ∀ (a b : CmdId × Cmd),
    a ∈ s → b ∈ s → precedes (s.map Prod.fst) a.1 b.1 → [a, b] <+ s
  | [], _, a, b, ha, _, _ => by simp at ha
  | c :: s, hnd, a, b, ha, hb, hp => by
    have hnd' : (s.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hc : c.1 ∉ s.map Prod.fst := (List.nodup_cons.mp (by simpa using hnd)).1
    have hab : a.1 ≠ b.1 := fun e => by rw [e] at hp; exact precedes_irrefl _ _ hp
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · exact List.Sublist.cons_cons _ (List.singleton_sublist.mpr hb)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exfalso
        unfold precedes at hp
        simp at hp
      · have hca : c.1 ≠ b.1 := fun e => hc (e ▸ List.mem_map_of_mem hb)
        have hp' : precedes (s.map Prod.fst) a.1 b.1 := by
          unfold precedes at hp ⊢
          rw [List.map_cons, List.takeWhile_cons, if_pos (by simpa using hca)] at hp
          rcases List.mem_cons.mp hp with e | h
          · exact absurd (e ▸ List.mem_map_of_mem ha) hc
          · exact h
        exact List.Sublist.cons _ (sublist_pair_of_precedes s hnd' a b ha hb hp')

theorem precedes_of_sublist_pair : ∀ (s : Seq), (s.map Prod.fst).Nodup → ∀ (a b : CmdId × Cmd),
    [a, b] <+ s → precedes (s.map Prod.fst) a.1 b.1
  | [], _, a, b, h => by simp at h
  | c :: s, hnd, a, b, h => by
    have hnd' : (s.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hc : c.1 ∉ s.map Prod.fst := (List.nodup_cons.mp (by simpa using hnd)).1
    unfold precedes
    rw [List.map_cons, List.takeWhile_cons]
    rcases List.sublist_cons_iff.mp h with h | ⟨r, hr, h⟩
    · have hb : b ∈ s := h.subset (by simp)
      have hcb : c.1 ≠ b.1 := fun e => hc (e ▸ List.mem_map_of_mem hb)
      rw [if_pos (by simpa using hcb)]
      exact List.mem_cons_of_mem _ (precedes_of_sublist_pair s hnd' a b h)
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hb : b ∈ s := List.singleton_sublist.mp h
      have hcb : a.1 ≠ b.1 := fun e => hc (e ▸ List.mem_map_of_mem hb)
      rw [if_pos (by simpa using hcb)]
      exact List.mem_cons_self ..

theorem cmdIn_of_mem : ∀ (s : Seq), (s.map Prod.fst).Nodup → ∀ p ∈ s, cmdIn s p.1 = some p.2
  | [], _, p, hp => by simp at hp
  | c :: s, hnd, p, hp => by
    have hnd' : (s.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hc : c.1 ∉ s.map Prod.fst := (List.nodup_cons.mp (by simpa using hnd)).1
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [cmdIn]
    · have hne : c.1 ≠ p.1 := fun e => hc (e ▸ List.mem_map_of_mem hp)
      have := cmdIn_of_mem s hnd' p hp
      simp only [cmdIn, List.find?_cons, show (c.1 == p.1) = false by simpa using hne] at this ⊢
      exact this

theorem mem_ids_of_cmdIn {s : Seq} {x : CmdId} {c : Cmd} (h : cmdIn s x = some c) :
    x ∈ s.map Prod.fst := by
  simp only [cmdIn, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, -⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have hx := List.find?_some hp
  simp only [beq_iff_eq] at hx
  exact List.mem_map.mpr ⟨p, hm, hx⟩

/-- A sequence with distinct ids is the sequence of its ids under any command map that agrees. -/
theorem filterMap_ids (f : CmdId → Option Cmd) : ∀ (s : Seq), (s.map Prod.fst).Nodup →
    (∀ p ∈ s, f p.1 = some p.2) → (s.map Prod.fst).filterMap (fun y => (f y).map (y, ·)) = s
  | [], _, _ => rfl
  | c :: s, hnd, hf => by
    have hnd' : (s.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    rw [List.map_cons, List.filterMap_cons, hf c (List.mem_cons_self ..)]
    simp only [Option.map_some]
    rw [filterMap_ids f s hnd' (fun p hp => hf p (List.mem_cons_of_mem _ hp))]

/-! ## The witness and its sort -/

variable (H : Hist) (L0 : Seq)

/-- One step of a conflict chain in `L0`. -/
def cstep (a b : CmdId × Cmd) : Prop := [a, b] <+ L0 ∧ Cmd.conflict a.2 b.2 = true

/-- `z` is a conflict-chain predecessor of `x` in `L0` (`x` included). -/
def CP (z x : CmdId × Cmd) : Prop := z = x ∨ Relation.TransGen (cstep L0) z x

theorem CP.refl' (x : CmdId × Cmd) : CP L0 x x := Or.inl rfl

theorem CP.tail' {z a b : CmdId × Cmd} (h : CP L0 z a) (s : cstep L0 a b) : CP L0 z b := by
  rcases h with rfl | h
  · exact Or.inr (.single s)
  · exact Or.inr (.tail h s)

/-- The first invocation of `z` in `H`. -/
def invIdx (z : CmdId) : Nat := H.findIdx (fun e => decide (∃ c, e = Ev.inv z c))

/-- The latest invocation among `x`'s conflict-chain predecessors. -/
def tau (x : CmdId × Cmd) : Nat :=
  ((L0.filter (fun z => decide (CP L0 z x))).map (fun z => invIdx H z.1)).foldr max 0

theorem le_foldr_max (l : List Nat) (n : Nat) (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem foldr_max_mem (l : List Nat) (h : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hl : l = []
    · subst hl; simp
    · rcases Nat.le_total a (l.foldr max 0) with h' | h'
      · rw [Nat.max_eq_right h']; exact List.mem_cons_of_mem _ (ih hl)
      · rw [Nat.max_eq_left h']; exact List.mem_cons_self ..

theorem foldr_max_le (l : List Nat) (m : Nat) (h : ∀ n ∈ l, n ≤ m) : l.foldr max 0 ≤ m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..), ih (fun n hn => h n (List.mem_cons_of_mem _ hn))⟩

theorem le_tau {z x : CmdId × Cmd} (hz : z ∈ L0) (h : CP L0 z x) : invIdx H z.1 ≤ tau H L0 x :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨hz, by simpa using h⟩, rfl⟩)

theorem tau_mem {x : CmdId × Cmd} (hx : x ∈ L0) :
    ∃ z ∈ L0, CP L0 z x ∧ tau H L0 x = invIdx H z.1 := by
  have hne : (L0.filter (fun z => decide (CP L0 z x))).map (fun z => invIdx H z.1) ≠ [] := by
    intro h
    have : x ∈ L0.filter (fun z => decide (CP L0 z x)) :=
      List.mem_filter.mpr ⟨hx, by simpa using (CP.refl' L0 x)⟩
    have := List.mem_map_of_mem (f := fun z => invIdx H z.1) this
    rw [h] at this; simp at this
  obtain ⟨z, hz, he⟩ := List.mem_map.mp (foldr_max_mem _ hne)
  obtain ⟨hz1, hz2⟩ := List.mem_filter.mp hz
  exact ⟨z, hz1, by simpa using hz2, he.symm⟩

theorem tau_mono {a b : CmdId × Cmd} (h : cstep L0 a b) : tau H L0 a ≤ tau H L0 b := by
  apply foldr_max_le
  intro n hn
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hn
  obtain ⟨hz1, hz2⟩ := List.mem_filter.mp hz
  exact le_tau H L0 hz1 (CP.tail' L0 (by simpa using hz2) h)

/-- **A witness** of `H`'s linearizability: distinct invoked commands with their commands, every
accepted command with its result, and real time along conflict chains: each conflict-chain
predecessor of an accepted command was invoked before the acceptance; invocations are unique. -/
structure Witness : Prop where
  nodup : (L0.map Prod.fst).Nodup
  inv : ∀ p ∈ L0, Ev.inv p.1 p.2 ∈ H
  resp : ∀ x v, Ev.resp x v ∈ H → x ∈ L0.map Prod.fst ∧ resultIn L0 x = v
  rt : ∀ (i : Nat) (x : CmdId × Cmd) (v : List w8), x ∈ L0 → H[i]? = some (Ev.resp x.1 v) →
    ∀ z ∈ L0, CP L0 z x → ∃ (j : Nat) (c : Cmd), j < i ∧ H[j]? = some (Ev.inv z.1 c)
  inv_once : ∀ (i j : Nat) (x : CmdId) (c c' : Cmd), H[i]? = some (Ev.inv x c) →
    H[j]? = some (Ev.inv x c') → i = j

theorem invIdx_le {z : CmdId} {j : Nat} {c : Cmd} (h : H[j]? = some (Ev.inv z c)) :
    invIdx H z ≤ j := by
  unfold invIdx
  have hj : j < H.length := by
    rcases Nat.lt_or_ge j H.length with e | e
    · exact e
    · rw [List.getElem?_eq_none e] at h; cases h
  have hp : (fun e => decide (∃ c, e = Ev.inv z c)) H[j] = true := by
    have : H[j] = Ev.inv z c := by rw [List.getElem?_eq_getElem hj] at h; exact Option.some.inj h
    simp [this]
  apply Classical.byContradiction
  intro hlt
  have := List.not_of_lt_findIdx (p := fun e => decide (∃ c, e = Ev.inv z c)) (xs := H)
    (i := j) (by omega)
  simp only at hp
  rw [hp] at this; cases this

theorem invIdx_eq {z : CmdId} {j : Nat} {c : Cmd} (hW : Witness H L0)
    (h : H[j]? = some (Ev.inv z c)) : invIdx H z = j := by
  have hle := invIdx_le H h
  have hj : j < H.length := by
    rcases Nat.lt_or_ge j H.length with e | e
    · exact e
    · rw [List.getElem?_eq_none e] at h; cases h
  have hlt : invIdx H z < H.length := Nat.lt_of_le_of_lt hle hj
  have hp := List.findIdx_getElem (p := fun e => decide (∃ c, e = Ev.inv z c)) (w := hlt)
  simp only [decide_eq_true_eq] at hp
  obtain ⟨c', hc'⟩ := hp
  exact hW.inv_once _ _ z c' c (by rw [List.getElem?_eq_getElem hlt]; exact congrArg some hc') h

/-- The sorted witness. -/
def sortW : Seq := L0.mergeSort (fun a b => decide (tau H L0 a ≤ tau H L0 b))

theorem sortW_perm : sortW H L0 ~ L0 := List.mergeSort_perm _ _

theorem sortW_pairwise : (sortW H L0).Pairwise (fun a b => decide (tau H L0 a ≤ tau H L0 b)) :=
  List.pairwise_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
    (fun a b => by simp; omega) _

theorem sortW_pair {a b : CmdId × Cmd} (h : cstep L0 a b) : [a, b] <+ sortW H L0 :=
  List.pair_sublist_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
    (fun a b => by simp; omega) (by simpa using tau_mono H L0 h) h.1

/-! ## The sort keeps conflicting pairs and results -/

section keep
variable {H L0}

theorem sortW_nodup (hW : Witness H L0) : ((sortW H L0).map Prod.fst).Nodup :=
  (List.Perm.map Prod.fst (sortW_perm H L0)).nodup_iff.mpr hW.nodup

theorem mem_sortW {p : CmdId × Cmd} : p ∈ sortW H L0 ↔ p ∈ L0 := (sortW_perm H L0).mem_iff

theorem ids_sortW {y : CmdId} : y ∈ (sortW H L0).map Prod.fst ↔ y ∈ L0.map Prod.fst :=
  (List.Perm.map Prod.fst (sortW_perm H L0)).mem_iff

theorem pair_of_id {s : Seq} {y : CmdId} (h : y ∈ s.map Prod.fst) : ∃ c, (y, c) ∈ s := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact ⟨p.2, hp⟩

/-- Conflicting commands keep their order. -/
theorem sortW_keep (hW : Witness H L0) {a b : CmdId × Cmd} (ha : a ∈ L0) (hb : b ∈ L0)
    (hc : Cmd.conflict a.2 b.2 = true) :
    precedes (L0.map Prod.fst) a.1 b.1 ↔ precedes ((sortW H L0).map Prod.fst) a.1 b.1 := by
  have fwd : ∀ a b, a ∈ L0 → b ∈ L0 → Cmd.conflict a.2 b.2 = true →
      precedes (L0.map Prod.fst) a.1 b.1 → precedes ((sortW H L0).map Prod.fst) a.1 b.1 := by
    intro a b ha hb hc hp
    exact precedes_of_sublist_pair _ (sortW_nodup hW) a b
      (sortW_pair H L0 ⟨sublist_pair_of_precedes L0 hW.nodup a b ha hb hp, hc⟩)
  have hcs : Cmd.conflict b.2 a.2 = true := by
    unfold Cmd.conflict at hc ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc ⊢
    exact ⟨hc.1.symm, hc.2.symm⟩
  refine ⟨fwd a b ha hb hc, fun h => ?_⟩
  have hab : a.1 ≠ b.1 := fun e => by rw [e] at h; exact precedes_irrefl _ _ h
  rcases precedes_total (L0.map Prod.fst) a.1 b.1 (List.mem_map_of_mem ha)
    (List.mem_map_of_mem hb) hab with h' | h'
  · exact h'
  · exact (precedes_antisymm _ _ _ h (fwd b a hb ha hcs h')).elim

/-- The command map of `L0` as a protocol state (to use `resultIn_lastPut`). -/
def stOf (L0 : Seq) : PState :=
  ⟨fun y => cmdIn L0 y, fun _ _ => [], fun _ => none, fun _ => RState.init, fun _ _ _ => False,
    fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ => False, fun _ _ => none, []⟩

theorem seqOf_stOf (hW : Witness H L0) {s : Seq} (hs : s ~ L0) :
    (stOf L0).seqOf (s.map Prod.fst) = s := by
  unfold PState.seqOf
  have hnd : (s.map Prod.fst).Nodup := (List.Perm.map Prod.fst hs).nodup_iff.mpr hW.nodup
  exact filterMap_ids _ s hnd (fun p hp => cmdIn_of_mem L0 hW.nodup p (hs.mem_iff.mp hp))

theorem stOf_cmds (hW : Witness H L0) {p : CmdId × Cmd} (hp : p ∈ L0) :
    (stOf L0).cmds p.1 = some p.2 := cmdIn_of_mem L0 hW.nodup p hp

/-- The sort keeps every command's result. -/
theorem sortW_result (hW : Witness H L0) {x : CmdId} (hx : x ∈ L0.map Prod.fst) :
    resultIn (sortW H L0) x = resultIn L0 x := by
  obtain ⟨cx, hcx⟩ := pair_of_id hx
  let S := stOf L0
  have hS : S.cmds x = some cx := stOf_cmds hW hcx
  have hreg : ∀ (s : Seq), s ~ L0 → ∀ y ∈ s.map Prod.fst, S.cmds y ≠ none := by
    intro s hs y hy
    obtain ⟨c, hc⟩ := pair_of_id hy
    rw [show y = (y, c).1 from rfl, stOf_cmds hW (hs.mem_iff.mp hc)]; simp
  have hndW := sortW_nodup hW
  have hxW : x ∈ (sortW H L0).map Prod.fst := ids_sortW.mpr hx
  have e1 : resultIn (sortW H L0) x = resultIn (S.seqOf ((sortW H L0).map Prod.fst)) x := by
    rw [seqOf_stOf hW (sortW_perm H L0)]
  have e2 : resultIn L0 x = resultIn (S.seqOf (L0.map Prod.fst)) x := by
    rw [seqOf_stOf hW (List.Perm.refl L0)]
  rw [e1, e2]
  by_cases hg : cx.isGet = true
  · obtain ⟨p, hp⟩ := Ctx.lastPut_exists (S := S) (L0.map Prod.fst) hW.nodup x cx.key
    rw [PState.resultIn_lastPut S _ hW.nodup (hreg L0 (List.Perm.refl _)) x cx hx hS p hp,
      PState.resultIn_lastPut S _ hndW (hreg _ (sortW_perm H L0)) x cx hxW hS p ?_]
    -- a put of `x`'s key and `x` (a get) conflict; two puts of a key conflict
    have hput : ∀ y, S.isPutOf cx.key y → ∃ c, (y, c) ∈ L0 ∧ Cmd.conflict c cx = true := by
      intro y ⟨cy, hcy, hk, hp⟩
      have hy : y ∈ L0.map Prod.fst := by
        unfold S stOf at hcy; exact mem_ids_of_cmdIn hcy
      obtain ⟨c, hc⟩ := pair_of_id hy
      have := stOf_cmds hW hc; rw [this] at hcy; cases hcy
      simp only at hk hp
      exact ⟨c, hc, by simp [Cmd.conflict, hk, hp]⟩
    have hpp : ∀ y z, S.isPutOf cx.key y → S.isPutOf cx.key z →
        ∃ cy cz, (y, cy) ∈ L0 ∧ (z, cz) ∈ L0 ∧ Cmd.conflict cy cz = true := by
      intro y z hy hz
      obtain ⟨cy, hcy, -⟩ := hput y hy
      obtain ⟨cz, hcz, -⟩ := hput z hz
      obtain ⟨cy', hcy', hky, hpy⟩ := hy
      obtain ⟨cz', hcz', hkz, hpz⟩ := hz
      rw [show y = (y, cy).1 from rfl, stOf_cmds hW hcy] at hcy'
      rw [show z = (z, cz).1 from rfl, stOf_cmds hW hcz] at hcz'
      cases hcy'; cases hcz'
      simp only at hky hkz hpy
      exact ⟨cy, cz, hcy, hcz, by simp [Cmd.conflict, hky, hkz, hpy]⟩
    -- transfer `LastPut` from `L0`'s order to the sort's
    have tr : ∀ y, S.isPutOf cx.key y → (precedes (L0.map Prod.fst) y x ↔
        precedes ((sortW H L0).map Prod.fst) y x) := by
      intro y hy
      obtain ⟨c, hc, hcf⟩ := hput y hy
      exact sortW_keep hW (a := (y, c)) (b := (x, cx)) hc hcx hcf
    cases p with
    | none =>
      intro y hy hput'
      exact hp y ((tr y hput').mpr hy) hput'
    | some p =>
      obtain ⟨hpx, hpP, hmax⟩ := hp
      refine ⟨(tr p hpP).mp hpx, hpP, fun y hy hyP => ?_⟩
      rcases hmax y ((tr y hyP).mpr hy) hyP with h | h
      · exact Or.inl h
      · obtain ⟨cy, cp, hcy, hcp, hc⟩ := hpp y p hyP hpP
        exact Or.inr ((sortW_keep hW (a := (y, cy)) (b := (p, cp)) hcy hcp hc).mp h)
  · have hg' : cx.isGet = false := by simpa using hg
    rw [Ctx.resultIn_nonget (S := S) _ (hreg _ (sortW_perm H L0)) x cx hxW hS hg',
      Ctx.resultIn_nonget (S := S) _ (hreg L0 (List.Perm.refl _)) x cx hx hS hg']

end keep

/-- **From a witness, a linearization**: the witness sorted by `tau`. -/
theorem lin_of_witness (hW : Witness H L0) : Lin H := by
  refine ⟨sortW H L0, sortW_nodup hW, fun p hp => hW.inv p (mem_sortW.mp hp),
    fun x v h => ?_, fun x y hx hy hrt => ?_⟩
  · obtain ⟨hx, hv⟩ := hW.resp x v h
    exact ⟨ids_sortW.mpr hx, by rw [sortW_result hW hx]; exact hv⟩
  · obtain ⟨i, j, v, c, hij, hi, hj⟩ := hrt
    obtain ⟨cx, hcx⟩ := pair_of_id (ids_sortW.mp hx)
    obtain ⟨cy, hcy⟩ := pair_of_id (ids_sortW.mp hy)
    -- tau x < tau y
    obtain ⟨z, hz, hcp, hτx⟩ := tau_mem H L0 hcx
    obtain ⟨j', c', hj', hz'⟩ := hW.rt i (x, cx) v hcx hi z hz hcp
    have h1 : tau H L0 (x, cx) < i := by rw [hτx]; exact Nat.lt_of_le_of_lt (invIdx_le H hz') hj'
    have h2 : j ≤ tau H L0 (y, cy) := by
      rw [← invIdx_eq H L0 hW hj]; exact le_tau H L0 hcy (CP.refl' L0 _)
    have hxy : x ≠ y := by
      intro e; subst e
      have := cmdIn_of_mem L0 hW.nodup _ hcx
      rw [cmdIn_of_mem L0 hW.nodup _ hcy] at this; cases this
      omega
    rcases precedes_total _ x y hx hy hxy with h | h
    · exact h
    · exfalso
      have hsub := sublist_pair_of_precedes _ (sortW_nodup hW) (y, cy) (x, cx)
        (mem_sortW.mpr hcy) (mem_sortW.mpr hcx) h
      have := List.pairwise_pair.mp ((sortW_pairwise H L0).sublist hsub)
      simp at this
      omega

/-! ## The protocol's witness (proved) and `lin_now` -/

/-! ### The protocol's facts about a command registered after an acceptance -/

theorem SHist.get_hist {h : SHist} {i : Nat} {e : Ev} (hi : (SHist.hist h)[i]? = some e) :
    ∃ S', h[i]? = some (e, S') := by
  unfold SHist.hist at hi; rw [List.getElem?_map] at hi
  cases hh : h[i]? with
  | none => rw [hh] at hi; cases hi
  | some p => rw [hh] at hi; simp at hi; subst hi; exact ⟨p.2, rfl⟩

namespace PState
variable {S Si : PState} {N : Nat} {fr : Bool}

/-- A command before `x` in a later state's order of a ballot that already had `x` was in the
earlier state's order, so registered then. -/
theorem prefix_new (hle : Si.le S) (hIi : Si.PInv N fr) {b : Nat} {x z : CmdId}
    (hx : x ∈ Si.ord N b) (hz : Si.cmds z = none) (h : precedes (S.ord N b) z x) : False := by
  obtain ⟨t, ht⟩ := hle.loc (leaderOf N b) b
  unfold ord at hx h
  rw [← ht] at h
  have h' := (Ctx.precedes_append_of_mem _ t z x hx).mp h
  exact (hIi.loc_ok _ _).2.1 z (precedes_mem _ _ _ h') hz

/-- **A command registered after a get's acceptance is not before the get's last put in a later
`MSync`** (L1's protocol fact; the get case by `new_base_gen`, NewBase.lean; model-checked as `lin_new`).
`x` was possibly chosen in `bx` in the earlier state `Si` (its client accepted it then), `w` its
last put in its leader's order, `z` of `x`'s key unregistered in `Si`. A put `z` conflicts with
`x`: `ballot_safety`'s third clause. -/
theorem new_base (hI : S.PInv N fr) (hle : Si.le S) (hIi : Si.PInv N fr) {bx b' : Nat}
    {x z w : CmdId} {cx cz : Cmd} (hx : Si.possiblyChosen N bx x) (hcx : S.cmds x = some cx)
    (hg : cx.isGet = true) (hw : S.LastPut (S.ord N bx) x cx.key (some w)) (hb : bx < b')
    (hs : S.sync b' ≠ none) (hz : Si.cmds z = none) (hcz : S.cmds z = some cz)
    (hk : cz.key = cx.key) : ¬ precedes (S.base b') z w := by
  intro hzw
  have hxS := (possiblyChosen_le hIi hle hx).1
  have hwb : S.LastPut (S.base b') x cx.key (some w) := ballot_safety_lastPut hI hb hs hxS hcx hg hw
  have hzx : precedes (S.base b') z x := precedes_trans _ _ _ _ hzw hwb.1
  by_cases hp : cz.isPut = true
  · have hc : S.conflicts z x := ⟨cz, cx, hcz, hcx, by simp [Cmd.conflict, hk, hp]⟩
    exact prefix_new hle hIi hx.1 hz ((ballot_safety hI hb hs hxS).2.2 z hc hzx)
  · -- a get `z`: the recovery's order of a new get and the last put of a possibly chosen get
    -- (NewBase.lean, `new_base_gen`; notes/prophecy-client.md §6a)
    have hxreg : Si.cmds x ≠ none := (hIi.loc_ok (leaderOf N bx) bx).2.1 x hx.1
    have hzx0 : z ≠ x := fun e => hxreg (e ▸ hz)
    exact new_base_gen hI b' hb hs hxS hcx hg hw hcz hk hzx0
      (fun h => prefix_new hle hIi hx.1 hz h) hzw

/-- `new_base` in every leader order from `x`'s ballot on. -/
theorem new_after_lastPut (hI : S.PInv N fr) (hle : Si.le S) (hIi : Si.PInv N fr) {bx b' : Nat}
    {x z w : CmdId} {cx cz : Cmd} (hx : Si.possiblyChosen N bx x) (hcx : S.cmds x = some cx)
    (hg : cx.isGet = true) (hw : S.LastPut (S.ord N bx) x cx.key (some w)) (hb : bx ≤ b')
    (hz : Si.cmds z = none) (hcz : S.cmds z = some cz) (hk : cz.key = cx.key) :
    ¬ precedes (S.ord N b') z w := by
  intro hzw
  rcases Nat.eq_or_lt_of_le hb with rfl | hlt
  · exact prefix_new hle hIi hx.1 hz (precedes_trans _ _ _ _ hzw hw.1)
  · have hs : S.sync b' ≠ none := sync_of_ord hI (precedes_mem _ _ _ hzw) (by omega)
    have hxS := (possiblyChosen_le hIi hle hx).1
    have hwb : S.LastPut (S.base b') x cx.key (some w) :=
      ballot_safety_lastPut hI hlt hs hxS hcx hg hw
    have hwm : w ∈ S.base b' := precedes_mem _ _ _ hwb.1
    obtain ⟨T, hT⟩ := base_prefix_ord hI b'
    rw [← hT] at hzw
    exact new_base hI hle hIi hx hcx hg hw hlt hs hz hcz hk
      ((Ctx.precedes_append_of_mem _ T z w hwm).mp hzw)

end PState

/-- The shape of a conflict chain: one key, in order, and either a direct conflict or a put in
between. -/
theorem chain_shape {L0 : Seq} (hnd : (L0.map Prod.fst).Nodup) {z x : CmdId × Cmd}
    (h : Relation.TransGen (cstep L0) z x) :
    precedes (L0.map Prod.fst) z.1 x.1 ∧ z.2.key = x.2.key ∧
    (Cmd.conflict z.2 x.2 = true ∨ ∃ w ∈ L0, w.2.isPut = true ∧ w.2.key = x.2.key ∧
      precedes (L0.map Prod.fst) z.1 w.1 ∧ precedes (L0.map Prod.fst) w.1 x.1) := by
  induction h with
  | single s =>
    exact ⟨precedes_of_sublist_pair L0 hnd _ _ s.1, ((Ctx.conflict_iff _ _).mp s.2).1, Or.inl s.2⟩
  | @tail a b h1 s ih =>
    obtain ⟨hza, hka, -⟩ := ih
    have hab := precedes_of_sublist_pair L0 hnd _ _ s.1
    have hc := (Ctx.conflict_iff _ _).mp s.2
    refine ⟨precedes_trans _ _ _ _ hza hab, hka.trans hc.1, ?_⟩
    rcases hc.2 with hp | hp
    · exact Or.inr ⟨a, s.1.subset (by simp), hp, hc.1, hza, hab⟩
    · left; rw [Ctx.conflict_iff]; exact ⟨hka.trans hc.1, Or.inr hp⟩

/-- The top ballot: one at or above every accepted command's ballot, ordered something. -/
theorem top_ballot {N : Nat} (S : PState) : ∀ (l : SHist),
    (∀ x v S', (Ev.resp x v, S') ∈ l → S'.le S ∧
      ∃ b, S'.possiblyChosen N b x ∧ resultIn (S'.ordSeq N b) x = v) →
    ∃ B, (∀ x v S', (Ev.resp x v, S') ∈ l → ∃ b ≤ B, S'.possiblyChosen N b x ∧
      resultIn (S'.ordSeq N b) x = v) ∧ (0 < B → ∃ y, y ∈ S.ord N B)
  | [], _ => ⟨0, by simp, by omega⟩
  | (e, S1) :: l, hl => by
    obtain ⟨B, hB, hBo⟩ := top_ballot S l (fun x v S' hm => hl x v S' (List.mem_cons_of_mem _ hm))
    cases e with
    | inv y c =>
      refine ⟨B, fun x v S' hm => ?_, hBo⟩
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
      · exact hB x v S' hm
    | resp y w =>
      obtain ⟨hle, b, hpc, hres⟩ := hl y w S1 (List.mem_cons_self ..)
      refine ⟨max b B, fun x v S' hm => ?_, fun hpos => ?_⟩
      · rcases List.mem_cons.mp hm with hm | hm
        · simp only [Prod.mk.injEq, Ev.resp.injEq] at hm
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
          exact ⟨b, Nat.le_max_left _ _, hpc, hres⟩
        · obtain ⟨b', hb', h'⟩ := hB x v S' hm
          exact ⟨b', Nat.le_trans hb' (Nat.le_max_right _ _), h'⟩
      · by_cases hbB : b ≤ B
        · rw [Nat.max_eq_right hbB] at hpos ⊢; exact hBo hpos
        · rw [Nat.max_eq_left (by omega)]
          exact ⟨y, (hle.loc _ _).subset hpc.1⟩

/-- **The protocol gives a witness**: `L0` = the top ballot `B`'s leader sequence `ordSeq N B`
(`B`: any ballot at or above every accepted command's ballot whose leader ordered something, as `top_ballot` gives).
* `nodup`, `inv`: `PInv.loc_ok` (distinct, registered) and `HistOk.reg` (registered ⇒ invoked);
  `inv_once`: `HistOk.inv_once`.
* `resp`: an accepted `x` was possibly chosen in some `b ≤ B` at its snapshot, so now
  (`possiblyChosen_le`); for `b < B`, `ballot_safety` puts it in `base B` with its leader's
  result, and `base B` is a prefix of `ord N B`.
* `rt`: a conflict-chain predecessor `z` of an accepted `x`, if invoked after `x`'s acceptance,
  was unregistered in `x`'s snapshot (`HistOk.fresh`, `mono`). A direct conflict: `z` precedes
  `x` in `x`'s leader order (`ballot_safety`'s third clause), so it was there at the snapshot:
  registered. A chain through a put (`x` and `z` gets): `z` precedes `x`'s last put in `ord N B`
  (`ballot_safety_lastPut`: the put is the same), against `new_after_lastPut` (proved:
  `new_base`, its get case by `new_base_gen`, NewBase.lean). -/
theorem top_witness_at {N : Nat} {fr : Bool} {h : SHist} {S : PState} (hI : S.PInv N fr)
    (hH : HistOk N fr h S) (B : Nat)
    (hB : ∀ x v S', (Ev.resp x v, S') ∈ h → ∃ b ≤ B, S'.possiblyChosen N b x ∧
      resultIn (S'.ordSeq N b) x = v)
    (hBo : 0 < B → ∃ y, y ∈ S.ord N B) : Witness (SHist.hist h) (S.ordSeq N B) := by
  classical
  have hsB : ∀ b, b < B → S.sync B ≠ none := fun b hb => by
    obtain ⟨y, hy⟩ := hBo (by omega); exact PState.sync_of_ord hI hy (by omega)
  have hreg : ∀ y ∈ S.ord N B, S.cmds y ≠ none := (hI.loc_ok _ _).2.1
  have hndo : (S.ord N B).Nodup := (hI.loc_ok _ _).1
  have hids : (S.ordSeq N B).map Prod.fst = S.ord N B := Ctx.seqOf_fst (S := S) _ hreg
  have hnd : ((S.ordSeq N B).map Prod.fst).Nodup := by rw [hids]; exact hndo
  -- an accepted command is in the top order, with its result and its last put
  have top : ∀ {Si : PState} {b : Nat} {x : CmdId}, Si.PInv N fr → Si.le S → b ≤ B →
      Si.possiblyChosen N b x →
      x ∈ S.ord N B ∧ resultIn (S.ordSeq N B) x = resultIn (Si.ordSeq N b) x ∧
      ∀ cx p, S.cmds x = some cx → cx.isGet = true → S.LastPut (S.ord N b) x cx.key p →
        S.LastPut (S.ord N B) x cx.key p := by
    intro Si b x hIi hle hb hpc
    obtain ⟨hxS, hres⟩ := PState.possiblyChosen_le hIi hle hpc
    rcases Nat.eq_or_lt_of_le hb with rfl | hlt
    · exact ⟨hxS.1, hres, fun _ _ _ _ h => h⟩
    · have hs := hsB b hlt
      obtain ⟨g1, g2, -⟩ := PState.ballot_safety hI hlt hs hxS
      obtain ⟨T, hT⟩ := base_prefix_ord hI B
      refine ⟨hT ▸ List.mem_append_left _ g1, ?_, fun cx p hcx hg hp => ?_⟩
      · rw [← hres, ← g2]
        exact PState.resultIn_prefix_of hI _ _ ⟨T, hT⟩ hndo hreg x g1
      · rw [← hT]
        exact (PState.LastPut_append_iff S _ T x cx.key p g1).mp
          (PState.ballot_safety_lastPut hI hlt hs hxS hcx hg hp)
  refine ⟨hnd, fun p hp => ?_, fun x v hm => ?_, ?_, ?_⟩
  · -- inv
    obtain ⟨y, c⟩ := p
    exact hH.reg y c (Ctx.mem_seqOf (S := S) hp).1
  · -- resp
    obtain ⟨S', hm⟩ := SHist.mem_hist.mp hm
    obtain ⟨b, hb, hpc, hv⟩ := hB x v S' hm
    obtain ⟨h1, h2, -⟩ := top (hH.resp x v S' hm).1 (hH.le_now _ hm) hb hpc
    exact ⟨by rw [hids]; exact h1, h2.trans hv⟩
  · -- rt
    intro i x v hx hi z hz hcp
    obtain ⟨Si, hhi⟩ := SHist.get_hist hi
    have hmi : (Ev.resp x.1 v, Si) ∈ h := List.mem_of_getElem? hhi
    have hIi := (hH.resp _ _ _ hmi).1
    have hlei := hH.le_now _ hmi
    obtain ⟨b, hb, hpc, -⟩ := hB _ _ _ hmi
    have hzc : S.cmds z.1 = some z.2 := (Ctx.mem_seqOf (S := S) (y := z.1) (c := z.2) hz).1
    have hcx : S.cmds x.1 = some x.2 := (Ctx.mem_seqOf (S := S) (y := x.1) (c := x.2) hx).1
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hH.reg z.1 z.2 hzc)
    refine ⟨j, z.2, ?_, hj⟩
    apply Classical.byContradiction; intro hji
    obtain ⟨Sj, hhj⟩ := SHist.get_hist hj
    have hij : i < j := by
      rcases Nat.lt_or_ge i j with e | e
      · exact e
      · exfalso
        have e' : i = j := by omega
        subst e'; rw [hhi] at hhj; simp at hhj
    have hzj := hH.fresh _ _ _ (List.mem_of_getElem? hhj)
    have hle_ij : Si.le Sj := by
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hhi
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hhj
      have := List.pairwise_iff_getElem.mp hH.mono i j hil hjl hij
      rw [hie, hje] at this; exact this
    have hzi : Si.cmds z.1 = none := by
      cases e : Si.cmds z.1 with
      | none => rfl
      | some c => rw [hle_ij.cmds _ _ e] at hzj; cases hzj
    rcases hcp with rfl | htg
    · exact (hIi.loc_ok _ _).2.1 _ hpc.1 hzi
    obtain ⟨hzx, hk, hor⟩ := chain_shape hnd htg
    rw [hids] at hzx
    obtain ⟨hxB, -, hlpB⟩ := top hIi hlei hb hpc
    have direct : Cmd.conflict z.2 x.2 = true → False := by
      intro hc
      rcases Nat.eq_or_lt_of_le hb with rfl | hlt
      · exact PState.prefix_new hlei hIi hpc.1 hzi hzx
      · have hs := hsB b hlt
        have hxS := (PState.possiblyChosen_le hIi hlei hpc).1
        obtain ⟨g1, -, g3⟩ := PState.ballot_safety hI hlt hs hxS
        obtain ⟨T, hT⟩ := base_prefix_ord hI B
        have hzx' : precedes (S.base B) z.1 x.1 := by
          rw [← hT] at hzx; exact (Ctx.precedes_append_of_mem _ T _ _ g1).mp hzx
        exact PState.prefix_new hlei hIi hpc.1 hzi (g3 z.1 ⟨z.2, x.2, hzc, hcx, hc⟩ hzx')
    rcases hor with hc | ⟨w', hw'L, hw'p, hw'k, hzw', hw'x⟩
    · exact direct hc
    by_cases hc : Cmd.conflict z.2 x.2 = true
    · exact direct hc
    have hxp : x.2.isPut = false := by
      cases e : x.2.isPut
      · rfl
      · exact absurd (by rw [Ctx.conflict_iff]; exact ⟨hk, Or.inr e⟩) hc
    have hg : x.2.isGet = true := by
      obtain ⟨S0, hm0⟩ := SHist.mem_hist.mp (hH.reg x.1 x.2 hcx)
      rcases hH.pg _ _ _ hm0 with e | e
      · rw [hxp] at e; cases e
      · exact e
    rw [hids] at hzw' hw'x
    have hw'c : S.cmds w'.1 = some w'.2 := (Ctx.mem_seqOf (S := S) (y := w'.1) (c := w'.2) hw'L).1
    obtain ⟨p, hp⟩ := Ctx.lastPut_exists (S := S) (S.ord N b) (hI.loc_ok _ _).1 x.1 x.2.key
    have hpB := hlpB x.2 p hcx hg hp
    cases p with
    | none => exact hpB w'.1 hw'x ⟨w'.2, hw'c, hw'k, hw'p⟩
    | some w =>
      obtain ⟨-, -, hmax⟩ := hpB
      have hzw : precedes (S.ord N B) z.1 w := by
        rcases hmax w'.1 hw'x ⟨w'.2, hw'c, hw'k, hw'p⟩ with e | e
        · rw [← e]; exact hzw'
        · exact precedes_trans _ _ _ _ hzw' e
      exact PState.new_after_lastPut hI hlei hIi hpc hcx hg hp hb hzi hzc hk hzw
  · -- inv_once
    intro i j x c c' hi hj
    obtain ⟨S1, h1⟩ := SHist.get_hist hi
    obtain ⟨S2, h2⟩ := SHist.get_hist hj
    exact hH.inv_once i j x c c' S1 S2 h1 h2

/-- `top_witness_at` at the top ballot of `top_ballot`. -/
theorem top_witness {N : Nat} {fr : Bool} {h : SHist} {S : PState} (hI : S.PInv N fr)
    (hH : HistOk N fr h S) : ∃ L0, Witness (SHist.hist h) L0 := by
  obtain ⟨B, hB, hBo⟩ := top_ballot (N := N) S h
    (fun x v S' hm => ⟨hH.le_now _ hm, (hH.resp x v S' hm).2⟩)
  exact ⟨_, top_witness_at hI hH B hB hBo⟩

/-- **SwiftPaxos is linearizable, now**: a history whose snapshots satisfy `HistOk` (under the
protocol invariant) is linearizable. -/
theorem lin_now {N : Nat} {fr : Bool} {h : SHist} {S : PState} (hI : S.PInv N fr)
    (hH : HistOk N fr h S) : Lin (SHist.hist h) :=
  let ⟨_, hW⟩ := top_witness hI hH
  lin_of_witness _ _ hW

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
