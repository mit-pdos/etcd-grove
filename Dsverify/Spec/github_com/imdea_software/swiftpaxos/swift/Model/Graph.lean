/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Graph.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The `MSync`'s order (`syncOrder` of `lkAlong`) keeps every conflicting pair's order; results
through the last put; the kept graph after rule 4 (`recover_graph`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Recover

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## `lkAlong` and the `MSync`'s order -/

def lkStep (acc : Seq × List (CmdId × Cmd × List CmdId)) (p : CmdId × Cmd) :
    Seq × List (CmdId × Cmd × List CmdId) := (acc.1 ++ [p], acc.2 ++ [(p.1, p.2, lkDeps acc.1 p.2)])

theorem lkAlong_eq (cs : Seq) : lkAlong cs = (cs.foldl lkStep ([], [])).2 := rfl

theorem lkFold (cs : Seq) : (cs.foldl lkStep ([], [])).1 = cs := by
  induction cs using revInd with
  | h0 => rfl
  | hs cs p ih => rw [List.foldl_append]; simp [lkStep, ih]

theorem lkAlong_snoc (cs : Seq) (p : CmdId × Cmd) :
    lkAlong (cs ++ [p]) = lkAlong cs ++ [(p.1, p.2, lkDeps cs p.2)] := by
  rw [lkAlong_eq, lkAlong_eq, List.foldl_append]; simp [lkStep, lkFold]

theorem lkAlong_ids (cs : Seq) : (lkAlong cs).map (fun p => (p.1, p.2.1)) = cs := by
  induction cs using revInd with
  | h0 => rfl
  | hs cs p ih => rw [lkAlong_snoc]; simp [ih]

theorem lkAlong_mem (cs : Seq) (m : CmdId × Cmd × List CmdId) (hm : m ∈ lkAlong cs) :
    ∃ t q u, cs = t ++ q :: u ∧ m = (q.1, q.2, lkDeps t q.2) := by
  induction cs using revInd with
  | h0 => simp [lkAlong] at hm
  | hs cs p ih =>
    rw [lkAlong_snoc] at hm
    simp at hm
    rcases hm with hm | hm
    · obtain ⟨t, q, u, rfl, rfl⟩ := ih hm
      exact ⟨t, q, u ++ [p], by simp, rfl⟩
    · exact ⟨cs, p, [], by simp, hm⟩

/-- The `MSync`'s kept list (`syncOrder`'s). -/
def syncKept (M : SyncMsg) : Kept := M.map (fun p => (p.1, ⟨3, p.2.1, p.2.2, 0⟩))

theorem syncOrder_eq (M : SyncMsg) : syncOrder M = recOrder (syncKept M) (sortIds (M.map Prod.fst)) := rfl

theorem syncKept_get (cs : Seq) (hnd : (cs.map Prod.fst).Nodup) (t u : Seq) (q : CmdId × Cmd)
    (hcs : cs = t ++ q :: u) :
    (syncKept (lkAlong cs)).get q.1 = some ⟨3, q.2, lkDeps t q.2, 0⟩ := by
  have hpre : ∀ (A B : Seq), ∃ X, lkAlong (A ++ B) = lkAlong A ++ X := by
    intro A B
    induction B using revInd with
    | h0 => exact ⟨[], by simp⟩
    | hs B b ih =>
      obtain ⟨X, hX⟩ := ih
      exact ⟨X ++ [(b.1, b.2, lkDeps (A ++ B) b.2)], by rw [← List.append_assoc, lkAlong_snoc, hX]; simp⟩
  obtain ⟨X, hX⟩ := hpre (t ++ [q]) u
  have hcs' : cs = (t ++ [q]) ++ u := by rw [hcs]; simp
  rw [hcs', hX, lkAlong_snoc]
  have hq : q.1 ∉ t.map Prod.fst := by
    rw [hcs] at hnd; rw [List.map_append, List.nodup_append] at hnd
    intro h; exact hnd.2.2 q.1 h q.1 (by simp) rfl
  unfold syncKept Kept.get
  rw [List.map_append, List.map_append, List.find?_append, List.find?_append]
  have hnone : ((lkAlong t).map (fun p => (p.1, (⟨3, p.2.1, p.2.2, 0⟩ : RecEntry)))).find?
      (fun p => p.1 == q.1) = none := by
    rw [List.find?_eq_none]
    intro m hm; simp only [List.mem_map] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    intro heq; simp at heq
    apply hq
    have := congrArg (List.map Prod.fst) (lkAlong_ids t)
    rw [List.map_map] at this
    rw [← this]; exact List.mem_map.mpr ⟨m', hm', heq⟩
  simp [hnone]

theorem transGen_mono {α : Type} {r r' : α → α → Prop} (h : ∀ a b, r a b → r' a b) {a b : α}
    (hr : Relation.TransGen r a b) : Relation.TransGen r' a b := by
  induction hr with
  | single hd => exact Relation.TransGen.single (h _ _ hd)
  | tail _ hd ih => exact Relation.TransGen.tail ih (h _ _ hd)

theorem nodup_fst_eq {β : Type} (l : List (CmdId × β)) (hnd : (l.map Prod.fst).Nodup) (a b : CmdId × β)
    (ha : a ∈ l) (hb : b ∈ l) (hab : a.1 = b.1) : a = b := by
  induction l with
  | nil => simp at ha
  | cons p l ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hab ▸ List.mem_map.mpr ⟨b, hb, rfl⟩) hnd.1
    · exact absurd (hab.symm ▸ List.mem_map.mpr ⟨a, ha, rfl⟩) hnd.1
    · exact ih hnd.2 ha hb

theorem precedes_split (t u : List CmdId) (q d : CmdId) (hq : q ∉ t) (hd : d ∈ t) :
    precedes (t ++ q :: u) d q := by
  unfold precedes
  rw [List.takeWhile_append_of_pos]
  · simp [hd]
  · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; intro h; subst h; exact hq ha

theorem depsIn_mem (s : Seq) (z d : CmdId) (h : d ∈ depsIn s z) :
    ∃ t q u, s = t ++ q :: u ∧ q.1 = z ∧ d ∈ t.map Prod.fst := by
  unfold depsIn at h
  cases hc : cmdIn s z with
  | none => rw [hc] at h; simp at h
  | some c =>
    rw [hc] at h; simp only at h
    unfold cmdIn at hc
    cases hf : s.find? (fun p => p.1 == z) with
    | none => rw [hf] at hc; simp at hc
    | some q =>
      rw [hf] at hc; simp at hc
      obtain ⟨hqz, t, u, hs, ht⟩ := List.find?_eq_some_iff_append.mp hf
      simp at hqz
      have hq' : q.1 ∉ t.map Prod.fst := by
        intro hm; obtain ⟨a, ha, hae⟩ := List.mem_map.mp hm
        have := ht a ha; simp [hae, hqz] at this
      have hb : before s z = t := by rw [hs, ← hqz]; exact before_split t u q hq'
      rw [hb] at h
      obtain ⟨t1, q', t2, ht1, rfl, -⟩ := (mem_lkDeps t c d).mp h
      exact ⟨t, q, u, hs, hqz, by rw [ht1]; simp⟩

theorem syncOrder_lkAlong (cs : Seq) (hnd : (cs.map Prod.fst).Nodup) :
    (∀ y, y ∈ syncOrder (lkAlong cs) ↔ y ∈ cs.map Prod.fst) ∧ (syncOrder (lkAlong cs)).Nodup ∧
    (∀ y z (cy cz : Cmd), (y, cy) ∈ cs → (z, cz) ∈ cs → y ≠ z → cy.key = cz.key →
      (cy.isPut ∨ cz.isPut) → (precedes (syncOrder (lkAlong cs)) y z ↔ precedes (cs.map Prod.fst) y z)) := by
  let k := syncKept (lkAlong cs)
  have hids : (lkAlong cs).map Prod.fst = cs.map Prod.fst := by
    have := congrArg (List.map Prod.fst) (lkAlong_ids cs); rw [List.map_map] at this; exact this
  let ids := sortIds ((lkAlong cs).map Prod.fst)
  have hperm : ids.Perm (cs.map Prod.fst) := by rw [← hids]; exact List.mergeSort_perm _ _
  -- the kept dependencies are the sequence's
  have hk : ∀ t q u, cs = t ++ q :: u → kdeps k q.1 = lkDeps t q.2 := by
    intro t q u hcs; unfold kdeps; rw [syncKept_get cs hnd t u q hcs]; rfl
  have hkd : ∀ z, z ∈ cs.map Prod.fst → kdeps k z = depsIn cs z := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    obtain ⟨t, u, hcs⟩ := List.append_of_mem hq
    have hq' : q.1 ∉ t.map Prod.fst := by
      rw [hcs, List.map_append, List.nodup_append] at hnd
      intro h; exact hnd.2.2 q.1 h q.1 (by simp) rfl
    rw [hk t q u hcs, hcs, depsIn_split t u q hq']
  have hkeys : ∀ y, (k.get y).isSome ↔ y ∈ cs.map Prod.fst := by
    intro y; rw [Kept.get_isSome_iff]; unfold k syncKept; rw [List.map_map]
    show y ∈ (lkAlong cs).map Prod.fst ↔ _; rw [hids]
  have hφ : ∀ c ∈ ids, ∀ d ∈ kdeps k c, (k.get d).isSome →
      d ∈ ids ∧ (cs.map Prod.fst).idxOf d < (cs.map Prod.fst).idxOf c := by
    intro c hc d hd _
    have hc' := hperm.mem_iff.mp hc
    rw [hkd c hc'] at hd
    obtain ⟨t, q, u, hcs, hqc, hdt⟩ := depsIn_mem cs c d hd
    subst hqc
    have hq' : q.1 ∉ t.map Prod.fst := by
      rw [hcs, List.map_append, List.nodup_append] at hnd
      intro h; exact hnd.2.2 q.1 h q.1 (by simp) rfl
    have hp := precedes_split (t.map Prod.fst) (u.map Prod.fst) q.1 d hq' hdt
    have : cs.map Prod.fst = t.map Prod.fst ++ q.1 :: u.map Prod.fst := by rw [hcs]; simp
    rw [this]
    refine ⟨hperm.mem_iff.mpr (by rw [this]; exact precedes_mem _ _ _ hp), ((precedes_iff _ _ _).mp hp).2⟩
  have hidsnd : ids.Nodup := hperm.nodup_iff.mpr hnd
  obtain ⟨hmem, hnd', hbefore⟩ := recOrder_spec k ids hidsnd _ hφ
  rw [syncOrder_eq]
  refine ⟨fun y => (hmem y).trans hperm.mem_iff, hnd', ?_⟩
  have hkept : ∀ c ∈ recOrder k ids, ∀ d ∈ kdeps k c, (k.get d).isSome := by
    intro c hc d hd
    have hc' := hperm.mem_iff.mp ((hmem c).mp hc)
    rw [hkd c hc'] at hd
    obtain ⟨t, q, u, hcs, -, hdt⟩ := depsIn_mem cs c d hd
    rw [hkeys, hcs]; simp only [List.map_append, List.map_cons, List.mem_append]; exact Or.inl hdt
  -- a conflicting earlier command is reached, so placed earlier
  have fwd : ∀ y z (cy cz : Cmd), (y, cy) ∈ cs → (z, cz) ∈ cs → cy.key = cz.key →
      (cy.isPut ∨ cz.isPut) → precedes (cs.map Prod.fst) y z → precedes (recOrder k ids) y z := by
    intro y z cy cz hy hz hkey hput hp
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem hz
    have hyl : (y, cy) ∈ l1 := by
      have hyz : y ∈ (l1.map Prod.fst) := by
        have hz' : z ∉ l1.map Prod.fst := by
          rw [hl, List.map_append, List.nodup_append] at hnd
          intro h; exact hnd.2.2 z h z (by simp) rfl
        unfold precedes at hp; rw [hl, List.map_append, List.map_cons,
          List.takeWhile_append_of_pos] at hp
        · simpa using hp
        · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; intro h; subst h; exact hz' ha
      obtain ⟨p, hp', hpe⟩ := List.mem_map.mp hyz
      have : p = (y, cy) := nodup_fst_eq cs hnd p (y, cy) (by rw [hl]; simp [hp']) hy hpe
      rw [← this]; exact hp'
    obtain ⟨a, b, hab⟩ := List.append_of_mem hyl
    have hch := chain cs hnd b.length a b l2 (y, cy) (z, cz) rfl (by rw [hl, hab]; try simp) hkey hput
    have hreach : Relation.TransGen (fun y d => d ∈ kdeps k y) z y := by
      refine transGen_mono ?_ hch
      intro a d hd
      obtain ⟨t, q, u, hcs, hqa, -⟩ := depsIn_mem cs a d hd
      rw [hkd a (by rw [hcs, ← hqa]; simp)]; exact hd
    exact order_reach k _ hnd' hbefore hkept z y ((hmem z).mpr (hperm.mem_iff.mpr (List.mem_map.mpr ⟨_, hz, rfl⟩))) hreach
  intro y z cy cz hy hz hne hkey hput
  show precedes (recOrder k ids) y z ↔ _
  constructor
  · intro hO
    have hyc : y ∈ cs.map Prod.fst := List.mem_map.mpr ⟨_, hy, rfl⟩
    have hzc : z ∈ cs.map Prod.fst := List.mem_map.mpr ⟨_, hz, rfl⟩
    rcases precedes_total _ y z hyc hzc hne with h | h
    · exact h
    · have := fwd z y cz cy hz hy hkey.symm (hput.symm) h
      rw [precedes_iff] at this hO; omega
  · exact fwd y z cy cz hy hz hkey hput

/-! ## Results through the last put -/

theorem precedes_antisymm (O : List CmdId) (a b : CmdId) (h1 : precedes O a b) (h2 : precedes O b a) :
    False := by
  rw [precedes_iff] at h1 h2; omega

theorem precedes_of_split (A B : List CmdId) (p y : CmdId) (hp : p ∈ A) (hy : y ∉ A) :
    precedes (A ++ y :: B) p y := precedes_split A B y p hy hp

namespace PState
variable (S : PState)

/-- `y` is a put of key `k`. -/
def isPutOf (k : w64) (y : CmdId) : Prop := ∃ cy, S.cmds y = some cy ∧ cy.key = k ∧ cy.isPut = true

/-- `p` is the last put of key `k` before `x` in `O` (`none`: there is none). -/
def LastPut (O : List CmdId) (x : CmdId) (k : w64) : Option CmdId → Prop
  | none => ∀ y, precedes O y x → ¬ S.isPutOf k y
  | some p => precedes O p x ∧ S.isPutOf k p ∧ ∀ y, precedes O y x → S.isPutOf k y → y = p ∨ precedes O y p

theorem seqOf_cons (y : CmdId) (l : List CmdId) (c : Cmd) (h : S.cmds y = some c) :
    S.seqOf (y :: l) = (y, c) :: S.seqOf l := by
  simp [seqOf, h]

theorem seqOf_append (l1 l2 : List CmdId) : S.seqOf (l1 ++ l2) = S.seqOf l1 ++ S.seqOf l2 := by
  simp [seqOf]

theorem seqOf_takeWhile (O : List CmdId) (x : CmdId) (hreg : ∀ y ∈ O, S.cmds y ≠ none) :
    before (S.seqOf O) x = S.seqOf (O.takeWhile (· != x)) := by
  induction O with
  | nil => rfl
  | cons y O ih =>
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg y (by simp))
    rw [seqOf_cons S y O c hc]
    unfold before at *
    rw [List.takeWhile_cons, List.takeWhile_cons]
    by_cases hyx : y = x
    · subst hyx; simp [seqOf]
    · simp [hyx, seqOf_cons S y _ c hc, ih (fun z hz => hreg z (by simp [hz]))]

theorem cmdIn_seqOf (O : List CmdId) (x : CmdId) (c : Cmd) (hx : x ∈ O) (h : S.cmds x = some c)
    (hreg : ∀ y ∈ O, S.cmds y ≠ none) : cmdIn (S.seqOf O) x = some c := by
  induction O with
  | nil => simp at hx
  | cons y O ih =>
    obtain ⟨cy, hcy⟩ := Option.ne_none_iff_exists'.mp (hreg y (by simp))
    rw [seqOf_cons S y O cy hcy]
    unfold cmdIn at *
    by_cases hyx : y = x
    · subst hyx; rw [h] at hcy; cases hcy; simp
    · simp at hx; rcases hx with hx | hx
      · exact absurd hx.symm hyx
      · simp [hyx, ih hx (fun z hz => hreg z (by simp [hz]))]

theorem resultIn_lastPut (O : List CmdId) (hnd : O.Nodup) (hreg : ∀ y ∈ O, S.cmds y ≠ none)
    (x : CmdId) (cx : Cmd) (hx : x ∈ O) (hcx : S.cmds x = some cx) (p : Option CmdId)
    (hp : S.LastPut O x cx.key p) :
    resultIn (S.seqOf O) x = if cx.isGet then ((p.bind S.cmds).map Cmd.val).getD [] else [] := by
  unfold resultIn putsBefore
  rw [cmdIn_seqOf S O x cx hx hcx hreg]
  simp only
  split
  · rename_i hg
    rw [seqOf_takeWhile S O x hreg]
    have hT : ∀ y ∈ O.takeWhile (· != x), S.cmds y ≠ none :=
      fun y hy => hreg y (List.takeWhile_subset _ hy)
    cases p with
    | none =>
      have : (S.seqOf (O.takeWhile (· != x))).filter (fun q => q.2.key == cx.key && q.2.isPut) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq
        simp only [seqOf, List.mem_filterMap, Option.map_eq_some_iff] at hq
        obtain ⟨y, hy, c, hc, rfl⟩ := hq
        have := hp y hy
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro hk hput; exact this ⟨c, hc, hk, hput⟩
      simp [this]
    | some p =>
      obtain ⟨hpx, ⟨cp, hcp, hkp, hpp⟩, hlast⟩ := hp
      have hpT : p ∈ O.takeWhile (· != x) := hpx
      obtain ⟨T1, T2, hT12⟩ := List.append_of_mem hpT
      have hOdec : O = O.takeWhile (· != x) ++ O.dropWhile (· != x) := (List.takeWhile_append_dropWhile).symm
      have hT2 : ∀ y ∈ T2, ¬ S.isPutOf cx.key y := by
        intro y hy hput
        have hyT : y ∈ O.takeWhile (· != x) := by rw [hT12]; simp [hy]
        rcases hlast y hyT hput with rfl | hyp
        · -- p twice in the prefix
          have hnd' : (O.takeWhile (· != x)).Nodup := (List.takeWhile_prefix _).sublist.nodup hnd
          rw [hT12] at hnd'
          rw [List.nodup_append] at hnd'
          exact (List.nodup_cons.mp hnd'.2.1).1 hy
        · -- y after p
          obtain ⟨T21, T22, hT2'⟩ := List.append_of_mem hy
          have hO : O = (T1 ++ p :: T21) ++ y :: (T22 ++ O.dropWhile (· != x)) := by
            have e := hOdec
            generalize O.dropWhile (· != x) = D at e ⊢
            rw [hT12, hT2'] at e
            rw [e]; simp
          have hyA : y ∉ T1 ++ p :: T21 := by
            intro hm
            rw [hO] at hnd
            rw [List.nodup_append] at hnd
            exact hnd.2.2 y hm y (by simp) rfl
          have := precedes_of_split (T1 ++ p :: T21) (T22 ++ O.dropWhile (· != x)) p y (by simp) hyA
          rw [← hO] at this
          exact precedes_antisymm O y p hyp this
      have hf2 : (S.seqOf T2).filter (fun q => q.2.key == cx.key && q.2.isPut) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq
        simp only [seqOf, List.mem_filterMap, Option.map_eq_some_iff] at hq
        obtain ⟨y, hy, c, hc, rfl⟩ := hq
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro hk hput; exact hT2 y hy ⟨c, hc, hk, hput⟩
      rw [hT12, seqOf_append, seqOf_cons S p T2 cp hcp, List.filter_append, List.filter_cons, hf2]
      simp [hkp, hpp, hcp]
  · rfl
end PState

/-! ## The recovery's kept graph -/

theorem Struct.cls {oldL U leaderInU R acks k} (h : Struct oldL U leaderInU R acks k) {y re}
    (hy : k.get y = some re) : (re.cls = 0 ↔ K0ok oldL U y) := by
  rcases h.2.1 y re hy with h1 | h1 | h1
  · obtain ⟨h0, a, ha, e, he, rfl, hok, -⟩ := h1
    exact ⟨fun _ => ⟨a, ha, e, he, rfl, hok⟩, fun _ => h0⟩
  · obtain ⟨h0, -, r0, rs, -, e, -, -, -, -, hn⟩ := h1
    exact ⟨fun h => absurd h h0, fun hk => absurd hk hn⟩
  · obtain ⟨h0, -, hn, -⟩ := h1
    exact ⟨fun h => absurd h h0, fun hk => absurd hk hn⟩

/-- The kept graph's facts after rule 4. -/
structure Graph (oldL : Nat) (U : List (Nat × Report)) (leaderInU : Bool) (R : List (Nat × Report))
    (acks : List (Nat × Report)) (k3 k3b k4 : Kept) : Prop where
  s3 : Struct oldL U leaderInU R acks k3
  keys : ∀ y, (k4.get y).isSome ↔ (k3.get y).isSome
  keysOk : KeysOk k3b
  keys3b : ∀ y, (k3b.get y).isSome ↔ (k3.get y).isSome
  m3b : Mono k3 k3b
  m4 : Mono k3b k4
  complete : ∀ y re, k4.get y = some re → ∀ d ∈ re.dep, (k4.get d).isSome
  k0 : ∀ y re, k4.get y = some re → K0ok oldL U y → re.cls = 0 ∧ K0entry oldL U y re
  nk0 : ∀ y re, k4.get y = some re → ¬ K0ok oldL U y → re.cls ≠ 0 ∧ (leaderInU = false →
    ∃ r0 rs, R = r0 :: rs ∧ ∃ e ∈ r0.2.entries, e.id = y ∧ re.cmd = e.cmd ∧
      ∃ ex3 ex4, re.dep = e.dep ++ ex3 ++ ex4 ∧ (∀ w ∈ ex3, P3b k3 r0 y w) ∧ (∀ a ∈ ex4, P4 k3b y a))
  d3b : leaderInU = false → ∀ r0 rs, R = r0 :: rs → ∀ c w, (k3.get c).isSome → D3b k3 r0 k4 c w
  d4 : ∀ c a, (k3b.get c).isSome → (k3b.get a).isSome → D4 k3b k4 c a

theorem rule3b_facts (leaderInU : Bool) (R : List (Nat × Report)) (k3 : Kept) :
    (Mono k3 (rule3b leaderInU R k3) ∧ ∀ y re, (rule3b leaderInU R k3).get y = some re →
      ∃ re0, k3.get y = some re0 ∧
      ∃ ex, re.dep = re0.dep ++ ex ∧ ∀ w ∈ ex, ∃ r0 rs, R = r0 :: rs ∧ P3b k3 r0 y w) ∧
    (leaderInU = false → ∀ r0 rs, R = r0 :: rs → ∀ c w, (k3.get c).isSome →
      D3b k3 r0 (rule3b leaderInU R k3) c w) := by
  obtain ⟨ha, hb⟩ := rule3b_spec leaderInU R k3
  cases leaderInU
  · cases R with
    | nil =>
      rw [ha (Or.inr rfl)]
      exact ⟨⟨Mono.refl _, fun y re h => ⟨re, h, [], by simp, by simp⟩⟩, fun _ _ _ h => by simp at h⟩
    | cons r0 rs =>
      obtain ⟨e1, e2, e3⟩ := hb rfl r0 rs rfl
      refine ⟨⟨e2, ?_⟩, ?_⟩
      · intro y re hy
        obtain ⟨re0, h0, ex, hd, hex⟩ := e1.2 y re hy
        exact ⟨re0, h0, ex, hd, fun w hw => ⟨r0, rs, rfl, hex w hw⟩⟩
      · intro _ r0' rs' hr' c w hc
        simp at hr'; obtain ⟨rfl, rfl⟩ := hr'
        exact e3 c w hc
  · rw [ha (Or.inl rfl)]
    exact ⟨⟨Mono.refl _, fun y re h => ⟨re, h, [], by simp, by simp⟩⟩, fun h => by simp at h⟩

theorem keysOk_of_mono {k k' : Kept} (h : Mono k k') (hk : KeysOk k) : KeysOk k' := by
  unfold KeysOk; rw [h.1]; exact hk

theorem recover_graph (N : Nat) (reps : List (Nat × Report))
    (acks U R : List (Nat × Report)) (oldL : Nat) (leaderInU : Bool) (k1 k2 k3 k3b k4 : Kept)
    (ids : List CmdId)
    (hacks : acks = recAcks reps) (hU : U = recU acks) (hL : oldL = leaderOf N (recMaxC acks))
    (hlU : leaderInU = U.any (·.1 == oldL)) (hR : R = U.filter (fun a => a.1 ∈ AQ N (recMaxC acks)))
    (h1 : k1 = rule1 oldL U) (h2 : k2 = rule2 k1 leaderInU R)
    (h3 : k3 = closure (recBest leaderInU R U acks) ((reps.flatMap (·.2.entries)).length + k2.length + 1) k2)
    (h3b : k3b = rule3b leaderInU R k3) (hids : ids = sortIds (k3b.map Prod.fst)) (h4 : k4 = rule4 ids k3b)
    (H : RecHyp oldL U leaderInU R) :
    Graph oldL U leaderInU R acks k3 k3b k4 ∧ ids.Nodup ∧ (∀ y, y ∈ ids ↔ (k4.get y).isSome) ∧
    (∀ y, (k2.get y).isSome → (k3.get y).isSome) := by
  have hRU : ∀ a ∈ R, a ∈ U := by intro a ha; rw [hR] at ha; exact (List.mem_filter.mp ha).1
  have hUa : ∀ a ∈ U, a ∈ acks := by intro a ha; rw [hU] at ha; exact (List.mem_filter.mp ha).1
  have hS1 := Struct_rule1 oldL U leaderInU R acks
  rw [← h1] at hS1
  obtain ⟨hS2, -, -⟩ := rule2_spec oldL U leaderInU R acks k1 hS1
  rw [← h2] at hS2
  obtain ⟨A, hAnd, hAmem, hAlen⟩ := exists_nodup_cover ((reps.flatMap (·.2.entries)).map (·.id))
  have hAcov : ∀ a ∈ acks, ∀ e ∈ a.2.entries, e.id ∈ A := by
    intro a ha e he
    rw [hAmem]; rw [hacks] at ha
    have ha' : a ∈ reps := List.mem_mergeSort.mp ha
    exact List.mem_map.mpr ⟨e, List.mem_flatMap.mpr ⟨a, ha', he⟩, rfl⟩
  have hfuel : k2.length + A.length < (reps.flatMap (·.2.entries)).length + k2.length + 1 := by
    rw [List.length_map] at hAlen; omega
  obtain ⟨hS3, hk23, hcomp⟩ := closure_spec H hRU hUa A hAnd hAcov k2 hS2 _ hfuel
  rw [← h3] at hS3 hk23 hcomp
  -- rule 3b
  have h3bcases := rule3b_facts leaderInU R k3
  rw [← h3b] at h3bcases
  obtain ⟨⟨hm3b, hex3b⟩, hd3b⟩ := h3bcases
  have hkeys3b : ∀ y, (k3b.get y).isSome ↔ (k3.get y).isSome := hm3b.2.1
  obtain ⟨he4, hm4, hd4⟩ := rule4_spec ids k3b (fun c hc => by
    rw [hids]; exact (List.mergeSort_perm _ _).mem_iff.mpr ((Kept.get_isSome_iff _ _).mp hc))
  rw [← h4] at he4 hm4 hd4
  have hko3b : KeysOk k3b := keysOk_of_mono hm3b hS3.1
  have hidsnd : ids.Nodup := by rw [hids]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hko3b
  refine ⟨⟨hS3, fun y => (hm4.2.1 y).trans (hkeys3b y), hko3b, hkeys3b, hm3b, hm4, ?_, ?_, ?_, ?_, ?_⟩,
    hidsnd, ?_, ?_⟩
  · -- completeness
    intro y re hy d hd
    obtain ⟨re3b, hy3b, -, -, ex4, hdep4⟩ := hm4.back hy
    obtain ⟨_, hy3b', ex4', hdep4', hex4⟩ := he4.2 y re hy
    rw [hy3b] at hy3b'; cases hy3b'
    rw [hdep4'] at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨re3, hy3, ex3, hdep3, hex3⟩ := hex3b y _ hy3b
      rw [hdep3] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact (hm4.2.1 d).mpr ((hkeys3b d).mpr (hcomp y re3 hy3 d hd))
      · obtain ⟨r0, rs, -, hP⟩ := hex3 d hd
        exact (hm4.2.1 d).mpr ((hkeys3b d).mpr hP.1)
    · obtain ⟨⟨_, _, _⟩, ⟨ea, hea, _⟩, _⟩ := hex4 d hd
      exact (hm4.2.1 d).mpr (by rw [hea]; rfl)
  · -- class-0 entries are rule 1's
    intro y re hy hK
    obtain ⟨re3b, hy3b, hc4, hm4c, -⟩ := hm4.back hy
    obtain ⟨re3, hy3, hc3, hm3c, -⟩ := hm3b.back hy3b
    have hcls : re.cls = 0 := by rw [hc4, hc3]; exact (hS3.cls hy3).mpr hK
    -- no dependency was appended (rules 3b and 4 append to class ≠ 0 only)
    obtain ⟨_, hy3b', ex4, hdep4, hex4⟩ := he4.2 y re hy
    rw [hy3b] at hy3b'; cases hy3b'
    have hex4e : ex4 = [] := by
      cases ex4 with
      | nil => rfl
      | cons a _ =>
        obtain ⟨⟨r, hr, hr0⟩, -⟩ := hex4 a (by simp)
        rw [hy3b] at hr; cases hr; rw [hc3] at hr0; exact absurd ((hS3.cls hy3).mpr hK) hr0
    obtain ⟨re3', hy3', ex3, hdep3, hex3⟩ := hex3b y _ hy3b
    rw [hy3] at hy3'; cases hy3'
    have hex3e : ex3 = [] := by
      cases ex3 with
      | nil => rfl
      | cons a _ =>
        obtain ⟨r0, rs, -, -, ⟨r, hr, hr0⟩, -⟩ := hex3 a (by simp)
        rw [hy3] at hr; cases hr; exact absurd ((hS3.cls hy3).mpr hK) hr0
    rcases hS3.2.1 y re3 hy3 with hK0 | hN | hN
    · obtain ⟨-, a, ha, e, he, hid, hok, hcmd, hdep⟩ := hK0
      refine ⟨hcls, hcls, a, ha, e, he, hid, hok, by rw [hm4c, hm3c, hcmd], ?_⟩
      rw [hdep4, hex4e, hdep3, hex3e, hdep]; simp
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, hn⟩ := hN; exact absurd hK hn
    · obtain ⟨-, -, hn, -⟩ := hN; exact absurd hK hn
  · -- the other entries are R[0]'s
    intro y re hy hK
    obtain ⟨re3b, hy3b, hc4, hm4c, -⟩ := hm4.back hy
    obtain ⟨re3, hy3, hc3, hm3c, -⟩ := hm3b.back hy3b
    obtain ⟨_, hy3b', ex4, hdep4, hex4⟩ := he4.2 y re hy
    rw [hy3b] at hy3b'; cases hy3b'
    obtain ⟨re3', hy3', ex3, hdep3, hex3⟩ := hex3b y _ hy3b
    rw [hy3] at hy3'; cases hy3'
    rcases hS3.2.1 y re3 hy3 with hK0 | hN | hN
    · obtain ⟨-, a, ha, e, he, hid, hok, -⟩ := hK0
      exact absurd ⟨a, ha, e, he, hid, hok⟩ hK
    · obtain ⟨hcl, hl, r0, rs, hR0, e, he, hid, hcmd, hdep, -⟩ := hN
      refine ⟨by rw [hc4, hc3]; exact hcl, fun _ => ⟨r0, rs, hR0, e, he, hid, by rw [hm4c, hm3c, hcmd],
        ex3, ex4, by rw [hdep4, hdep3, hdep], ?_, hex4⟩⟩
      intro w hw
      obtain ⟨r0', rs', hR', hP⟩ := hex3 w hw
      rw [hR0] at hR'; simp at hR'; obtain ⟨rfl, rfl⟩ := hR'
      exact hP
    · obtain ⟨hcl, hl, -⟩ := hN
      exact ⟨by rw [hc4, hc3]; exact hcl, fun h => by rw [hl] at h; simp at h⟩
  · intro hl r0 rs hR0 c w hc
    exact (hd3b hl r0 rs hR0 c w hc).mono hm4
  · exact hd4
  · intro y
    rw [hids]; unfold sortIds; rw [List.mem_mergeSort, ← Kept.get_isSome_iff]
    exact (hm4.2.1 y).symm
  · exact fun y h => by
      obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp h
      exact hk23 y (by rw [hre]; rfl)

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
