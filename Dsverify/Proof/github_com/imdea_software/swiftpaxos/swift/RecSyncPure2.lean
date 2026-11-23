/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecSyncPure2.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
More pure lemmas for `recoveredSync`'s proof (the reports' subsets `U`, `R`; the rules' loops
against the model's folds).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFacts

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace swift.rec

/-- `U`: the pairs of the highest `cballot`. -/
theorem recU_eq (prsA : List Pr) (maxC : Nat) (h : sp.recMaxC (prsA.map Prod.snd) = maxC) :
    sp.recU (prsA.map Prod.snd) = (prsA.filter (fun q => q.2.2.cbal == maxC)).map Prod.snd := by
  unfold sp.recU
  rw [h, List.filter_map]
  rfl

/-- Rule 1's step on one entry `e` of the report `a` (the model's inner function). -/
def r1e (oldL : Nat) (a : Nat × sp.Report) (k : sp.Kept) (e : sp.RepEntry) : sp.Kept :=
  if !sp.okPhase oldL a e then k else
  match k.get e.id with
  | some old => if old.phase != 3 && e.phase.toNat == 3 then k.set e.id ⟨3, e.cmd, e.dep, 0⟩
      else k
  | none => k.set e.id ⟨e.phase.toNat, e.cmd, e.dep, 0⟩

theorem rule1_eq (oldL : Nat) (prsU : List Pr) :
    sp.rule1 oldL (prsU.map Prod.snd) =
      prsU.foldl (fun k q => q.2.2.entries.foldl (r1e oldL q.2) k) [] := by
  unfold sp.rule1; rw [List.foldl_map]; rfl

/-- Rule 1 sets `e`'s entry (Go's `!exists || (e.phase != COMMIT && ph == COMMIT)`). -/
def setIt1 (k : sp.Kept) (e : sp.RepEntry) : Bool :=
  match k.get e.id with
  | none => true
  | some old => old.phase != 3 && e.phase.toNat == 3

theorem r1e_set {oldL : Nat} {a : Nat × sp.Report} {k : sp.Kept} {e : sp.RepEntry}
    (hok : sp.okPhase oldL a e = true) (hs : setIt1 k e = true) :
    r1e oldL a k e = k.set e.id ⟨e.phase.toNat, e.cmd, e.dep, 0⟩ := by
  unfold r1e setIt1 at *
  rw [hok]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h : k.get e.id with
  | none => rfl
  | some old =>
    rw [h] at hs
    simp only at hs ⊢
    rw [hs]
    simp only [↓reduceIte]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs
    rw [hs.2]

theorem r1e_keep {oldL : Nat} {a : Nat × sp.Report} {k : sp.Kept} {e : sp.RepEntry}
    (hok : sp.okPhase oldL a e = true) (hs : setIt1 k e = false) : r1e oldL a k e = k := by
  unfold r1e setIt1 at *
  rw [hok]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h : k.get e.id with
  | none => rw [h] at hs; cases hs
  | some old => rw [h] at hs; simp only at hs ⊢; rw [hs]; rfl

theorem foldl_take_succ {α β : Type} (f : β → α → β) (l : List α) (b : β) (n : Nat) (x : α)
    (h : l[n]? = some x) : (l.take (n + 1)).foldl f b = f ((l.take n).foldl f b) x := by
  rw [List.take_add_one, h]; simp


/-- `aq.Contains(rep)` for a replica `n < N`: membership in the model's `AQ`. -/
theorem mem_aq_iff (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (rep : w32) (n : Nat) (hn : n < N)
    (hr : sint.Z rep = n) :
    decide (rep ∈ (replica.quorum.aqOf N b).map replica.quorum.w32n) = decide (n ∈ sp.AQ N b) := by
  rw [replica.quorum.aqOf_eq_AQ]
  have hlt : ∀ x ∈ sp.AQ N b, x < N := (sp.AQ_majority N b (by omega)).1.2.1
  apply decide_eq_decide.mpr
  constructor
  · rintro hm
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
    have hx' := hlt x hx
    have h1 : sint.Z (replica.quorum.w32n x) = x :=
      replica.quorum.sint_W32 _ (by omega) (by omega)
    rw [hxe, hr] at h1
    have : x = n := by omega
    rw [← this]; exact hx
  · intro hm
    refine List.mem_map.mpr ⟨n, hm, ?_⟩
    apply BitVec.eq_of_toInt_eq
    have h1 : sint.Z (replica.quorum.w32n n) = n :=
      replica.quorum.sint_W32 _ (by omega) (by omega)
    change sint.Z _ = sint.Z rep
    rw [h1, hr]

/-- Rule 2's test of another reporter's entry `e'` against `R[0]`'s entry `e`. -/
def r2test (e e' : sp.RepEntry) : Bool :=
  (e'.id == e.id) && ((e'.phase.toNat == 1) && sp.depEq e.dep e'.dep)

/-- Rule 2's step on one entry `e` of `R[0]` (`rs`: the other reporters of `R`). -/
def r2e (rs : List (Nat × sp.Report)) (k : sp.Kept) (e : sp.RepEntry) : sp.Kept :=
  if (e.phase.toNat != 1) || (k.get e.id).isSome then k
  else if rs.all (fun a => a.2.entries.any (r2test e)) then k.set e.id ⟨2, e.cmd, e.dep, 1⟩
  else k

theorem rule2_eq (k1 : sp.Kept) (r0 : Nat × sp.Report) (rs : List (Nat × sp.Report)) :
    sp.rule2 k1 false (r0 :: rs) = r0.2.entries.foldl (r2e rs) k1 := by
  unfold sp.rule2 r2e r2test; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_assoc]

theorem r2e_skip {rs : List (Nat × sp.Report)} {k : sp.Kept} {e : sp.RepEntry}
    (h : e.phase.toNat ≠ 1 ∨ (k.get e.id).isSome = true) : r2e rs k e = k := by
  unfold r2e
  rcases h with h | h
  · have : (e.phase.toNat != 1) = true := by simpa using h
    simp [this]
  · simp [h]

theorem r2e_go {rs : List (Nat × sp.Report)} {k : sp.Kept} {e : sp.RepEntry}
    (h1 : e.phase.toNat = 1) (h2 : k.get e.id = none) :
    r2e rs k e = if rs.all (fun a => a.2.entries.any (r2test e)) then
      k.set e.id ⟨2, e.cmd, e.dep, 1⟩ else k := by
  unfold r2e
  simp [h1, h2]

theorem nat_lt_of_lt (a b : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z b) :
    sint.nat a < sint.nat b := by word

theorem nat_succ_of_lt (a b : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z b) :
    sint.nat (a + W64 1) = sint.nat a + 1 := by word

theorem map_to_of (l : List sp.CmdId) : (l.map ofCmdId).map toCmdId = l := by
  induction l <;> simp_all

theorem nodup_map_of {l : List sp.CmdId} (h : l.Nodup) : (l.map ofCmdId).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    refine ⟨?_, ih h.2⟩
    rintro ⟨b, hb, hba⟩
    have : b = a := by simpa using congrArg toCmdId hba
    exact h.1 (this ▸ hb)

theorem ofCmdId_eq_iff (a b : sp.CmdId) : ofCmdId a = ofCmdId b ↔ a = b :=
  ⟨fun h => by simpa using congrArg toCmdId h, fun h => h ▸ rfl⟩

/-! ### The closure (rule 3): the Go loop against the model's `closure` -/

theorem iter_add {α : Type} (f : α → α) (n m : Nat) (a : α) :
    sp.iter f (n + m) a = sp.iter f m (sp.iter f n a) := by
  induction n generalizing a with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    show sp.iter f (n + m) (f a) = sp.iter f m (sp.iter f n (f a))
    exact ih (f a)

theorem iter_fix {α : Type} (f : α → α) (a : α) (h : f a = a) : ∀ m, sp.iter f m a = a := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => show sp.iter f m (f a) = a; rw [h, ih]

/-- The inner fold of `closeStep` in general: the newly kept commands are appended to the work
list, each previously not kept, with a `best` entry. -/
theorem closeInner' (best : sp.CmdId → Option sp.RecEntry) (c : sp.CmdId) :
    ∀ (ds : List sp.CmdId) (k : sp.Kept) (w l : List sp.CmdId),
      ∃ news, (ds.foldl (sp.closeDep best c) (k, w, l)).2.1 = w ++ news ∧ news.Nodup ∧
        (∀ y ∈ news, k.get y = none ∧ (best y).isSome) ∧
        (∀ y, (ds.foldl (sp.closeDep best c) (k, w, l)).1.get y =
          if y ∈ news then best y else k.get y) := by
  intro ds
  induction ds with
  | nil => intro k w l; exact ⟨[], by simp, List.nodup_nil, by simp, by simp⟩
  | cons d ds ih =>
    intro k w l
    simp only [List.foldl_cons]
    by_cases hdc : d = c
    · have hstep : sp.closeDep best c (k, w, l) d = (k, w, l) := by
        unfold sp.closeDep; simp [hdc]
      rw [hstep]; exact ih k w l
    have hne : (d == c) = false := by simpa using hdc
    by_cases hk : (k.get d).isSome = true
    · have hstep : sp.closeDep best c (k, w, l) d = (k, w, l ++ [d]) := by
        unfold sp.closeDep; simp [hne, hk]
      rw [hstep]; exact ih k w (l ++ [d])
    · cases hb : best d with
      | none =>
        have hstep : sp.closeDep best c (k, w, l) d = (k, w, l) := by
          unfold sp.closeDep; simp [hne, hk, hb]
        rw [hstep]; exact ih k w l
      | some bd =>
        have hstep : sp.closeDep best c (k, w, l) d = (k.set d bd, w ++ [d], l ++ [d]) := by
          unfold sp.closeDep; simp [hne, hk, hb]
        rw [hstep]
        obtain ⟨news, h2, h3, h4, h5⟩ := ih (k.set d bd) (w ++ [d]) (l ++ [d])
        have hdn : d ∉ news := by
          intro h; have := (h4 d h).1; rw [sp.Kept.get_set] at this; simp at this
        refine ⟨d :: news, by rw [h2]; simp, List.nodup_cons.mpr ⟨hdn, h3⟩, ?_, ?_⟩
        · intro y hy; simp at hy; rcases hy with rfl | hy
          · exact ⟨by simpa using hk, by rw [hb]; rfl⟩
          · obtain ⟨a, b⟩ := h4 y hy
            rw [sp.Kept.get_set] at a
            by_cases e : y = d
            · subst e; simp at a
            · simp [e] at a; exact ⟨a, b⟩
        · intro y; rw [h5, sp.Kept.get_set]
          by_cases e : y = d
          · subst e; simp [hdn, hb]
          · by_cases hy : y ∈ news <;> simp [e, hy]

/-- The Go closure loop's invariant: the state after `n` steps of the model's `closeStep`, the
measure (`n` + work + unkept reported ids) constant, the work list without duplicates and kept,
and the ownership flags (`o`): the processed entries (kept, out of the work list) own their
dependency slices. -/
def CI (best : sp.CmdId → Option sp.RecEntry) (A : List sp.CmdId) (k2 : sp.Kept)
    (w0 : List sp.CmdId) (μ n : Nat) (k : sp.Kept) (w : List sp.CmdId) (o : sp.CmdId → Bool) :
    Prop :=
  sp.iter (sp.closeStep best) n (k2, w0) = (k, w) ∧ n + w.length + sp.unkept A k = μ ∧
  w.Nodup ∧ (∀ y ∈ w, (k.get y).isSome) ∧ (∀ y ∈ w, o y = false) ∧
  (∀ y, (k.get y).isSome → y ∉ w → o y = true)

theorem CI_init (best : sp.CmdId → Option sp.RecEntry) (A : List sp.CmdId) (k2 : sp.Kept)
    (w0 : List sp.CmdId) (hp : w0.Perm (k2.map Prod.fst)) (hnd : (k2.map Prod.fst).Nodup) :
    CI best A k2 w0 (w0.length + sp.unkept A k2) 0 k2 w0 (fun _ => false) := by
  refine ⟨rfl, by omega, hp.nodup_iff.mpr hnd, ?_, fun _ _ => rfl, ?_⟩
  · intro y hy; rw [sp.Kept.get_isSome_iff]; exact hp.mem_iff.mp hy
  · intro y hy hyw; exfalso; apply hyw; rw [sp.Kept.get_isSome_iff] at hy; exact hp.mem_iff.mpr hy

theorem CI_step {best : sp.CmdId → Option sp.RecEntry} {A : List sp.CmdId} {k2 : sp.Kept}
    {w0 : List sp.CmdId} {μ n : Nat} {k : sp.Kept} {c : sp.CmdId} {w : List sp.CmdId}
    {o : sp.CmdId → Bool} (hA : A.Nodup) (hcov : ∀ y, (best y).isSome → y ∈ A)
    (h : CI best A k2 w0 μ n k (c :: w) o) {e : sp.RecEntry} (hc : k.get c = some e)
    (o' : sp.CmdId → Bool)
    (ho1 : ∀ y ∈ (e.dep.foldl (sp.closeDep best c) (k, w, [])).2.1, o' y = false)
    (ho2 : ∀ y, y ∉ (e.dep.foldl (sp.closeDep best c) (k, w, [])).2.1 → o' y = o y) :
    CI best A k2 w0 μ (n + 1)
      ((e.dep.foldl (sp.closeDep best c) (k, w, [])).1.set c
        { e with dep := (e.dep.foldl (sp.closeDep best c) (k, w, [])).2.2 })
      (e.dep.foldl (sp.closeDep best c) (k, w, [])).2.1
      (fun y => if y = c then true else o' y) := by
  obtain ⟨hit, hμ, hnd, hwk, hof, hot⟩ := h
  obtain ⟨news, h2, h3, h4, h5⟩ := closeInner' best c e.dep k w []
  generalize hr : e.dep.foldl (sp.closeDep best c) (k, w, []) = r at h2 h5 ho1 ho2 ⊢
  have hcn : c ∉ news := fun hn => by have := (h4 c hn).1; rw [hc] at this; cases this
  have hnd' := List.nodup_cons.mp hnd
  have hget : ∀ y, (r.1.set c { e with dep := r.2.2 }).get y =
      if y = c then some { e with dep := r.2.2 } else if y ∈ news then best y else k.get y := by
    intro y; rw [sp.Kept.get_set, h5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp.iter_succ', hit]
    unfold sp.closeStep; simp only [hc]; rw [hr]
  · have hu := sp.unkept_step A k (r.1.set c { e with dep := r.2.2 }) news hA h3
      (fun y hy => hcov y (h4 y hy).2)
      (fun y hy => by
        refine ⟨by simpa using (h4 y hy).1, ?_⟩
        rw [hget]
        have : y ≠ c := fun hyc => hcn (hyc ▸ hy)
        simp [this, hy, (h4 y hy).2])
      (fun y hy => by
        rw [hget]
        by_cases hyc : y = c
        · subst hyc; simp [hc]
        · simp [hyc, hy])
    rw [h2, List.length_append]
    simp only [List.length_cons] at hμ
    omega
  · rw [h2, List.nodup_append]
    refine ⟨hnd'.2, h3, ?_⟩
    intro a ha b hb hab; subst hab
    have := (h4 a hb).1; have := hwk a (by simp [ha]); simp_all
  · intro y hy; rw [h2] at hy; rw [hget]
    by_cases hyc : y = c
    · simp [hyc]
    · simp only [hyc, ↓reduceIte]
      rcases List.mem_append.mp hy with hy | hy
      · have hk := hwk y (by simp [hy])
        have : y ∉ news := fun hn => by have := (h4 y hn).1; simp_all
        simp [this, hk]
      · simp [hy, (h4 y hy).2]
  · intro y hy
    have hyc : y ≠ c := by
      intro hyc; subst hyc; rw [h2] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hnd'.1 hy
      · exact hcn hy
    simp only [hyc, ↓reduceIte]; exact ho1 y hy
  · intro y hy hyw
    by_cases hyc : y = c
    · simp [hyc]
    · simp only [hyc, ↓reduceIte]
      rw [ho2 y hyw]
      rw [hget] at hy; simp only [hyc, ↓reduceIte] at hy
      have hyn : y ∉ news := fun hn => hyw (by rw [h2]; exact List.mem_append_right _ hn)
      simp only [hyn, ↓reduceIte] at hy
      apply hot y hy
      intro hm; rcases List.mem_cons.mp hm with hm | hm
      · exact hyc hm
      · exact hyw (by rw [h2]; exact List.mem_append_left _ hm)

theorem CI_done {best : sp.CmdId → Option sp.RecEntry} {A : List sp.CmdId} {k2 : sp.Kept}
    {μ n : Nat} {k : sp.Kept} {o : sp.CmdId → Bool}
    (h : CI best A k2 (sp.sortIds (k2.map Prod.fst)) μ n k [] o) (fuel : Nat) (hf : μ < fuel) :
    sp.closure best fuel k2 = k ∧ ∀ y, (k.get y).isSome → o y = true := by
  obtain ⟨hit, hμ, -, -, -, hot⟩ := h
  refine ⟨?_, fun y hy => hot y hy (by simp)⟩
  unfold sp.closure
  have hn : n ≤ fuel := by simp at hμ; omega
  rw [show fuel = n + (fuel - n) by omega, iter_add, hit]
  rw [iter_fix _ _ (by unfold sp.closeStep; rfl)]

/-- The reported ids (without duplicates) cover `best`'s commands; the fuel suffices. -/
theorem closure_setup (reps : List (Nat × sp.Report)) (li : Bool)
    (R U acks : List (Nat × sp.Report)) (hRU : ∀ a ∈ R, a ∈ U) (hUa : ∀ a ∈ U, a ∈ acks)
    (hacks : acks.Perm reps) (k2 : sp.Kept) (hk2 : sp.CmdFrom acks k2)
    (hnd2 : (k2.map Prod.fst).Nodup) :
    ∃ A : List sp.CmdId, A.Nodup ∧ (∀ y, (sp.recBest li R U acks y).isSome → y ∈ A) ∧
      k2.length + A.length < (reps.flatMap (·.2.entries)).length + k2.length + 1 ∧
      k2.length ≤ (reps.flatMap (·.2.entries)).length := by
  obtain ⟨A, hA, hAm, hAl⟩ := sp.exists_nodup_cover ((reps.flatMap (·.2.entries)).map (·.id))
  have hcov : ∀ a ∈ acks, ∀ e ∈ a.2.entries, e.id ∈ A := by
    intro a ha e he
    rw [hAm]
    exact List.mem_map.mpr ⟨e, List.mem_flatMap.mpr ⟨a, hacks.mem_iff.mp ha, he⟩, rfl⟩
  have hlen : A.length ≤ (reps.flatMap (·.2.entries)).length := by
    simpa using hAl
  have hk : k2.length ≤ A.length := by
    have hsub : (k2.map Prod.fst).Subperm A := by
      apply List.subperm_of_subset hnd2
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      have hg : (k2.get p.1).isSome := by
        rw [sp.Kept.get_isSome_iff]; exact List.mem_map_of_mem hp
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hg
      obtain ⟨a, ha, re, hre, h1, -⟩ := hk2 p.1 e he
      rw [← h1]; exact hcov a ha re hre
    simpa using hsub.length_le
  refine ⟨A, hA, ?_, by omega, by omega⟩
  intro y hy
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hy
  obtain ⟨a, ha, e, he, rfl⟩ := sp.recBest_mem hRU hUa hb
  exact hcov a ha e he

theorem unkept_le (A : List sp.CmdId) (k : sp.Kept) : sp.unkept A k ≤ A.length :=
  List.length_filter_le _ _


theorem closeDep_self (best : sp.CmdId → Option sp.RecEntry) (c : sp.CmdId)
    (acc : sp.Kept × List sp.CmdId × List sp.CmdId) : sp.closeDep best c acc c = acc := by
  unfold sp.closeDep; simp

theorem closeDep_kept {best : sp.CmdId → Option sp.RecEntry} {c d : sp.CmdId} {k : sp.Kept}
    {w l : List sp.CmdId} (hdc : d ≠ c) (hk : (k.get d).isSome = true) :
    sp.closeDep best c (k, w, l) d = (k, w, l ++ [d]) := by
  unfold sp.closeDep; simp [hdc, hk]

theorem closeDep_none {best : sp.CmdId → Option sp.RecEntry} {c d : sp.CmdId} {k : sp.Kept}
    {w l : List sp.CmdId} (hdc : d ≠ c) (hk : k.get d = none) (hb : best d = none) :
    sp.closeDep best c (k, w, l) d = (k, w, l) := by
  unfold sp.closeDep; simp [hdc, hk, hb]

theorem closeDep_new {best : sp.CmdId → Option sp.RecEntry} {c d : sp.CmdId} {k : sp.Kept}
    {w l : List sp.CmdId} {bd : sp.RecEntry} (hdc : d ≠ c) (hk : k.get d = none)
    (hb : best d = some bd) :
    sp.closeDep best c (k, w, l) d = (k.set d bd, w ++ [d], l ++ [d]) := by
  unfold sp.closeDep; simp [hdc, hk, hb]

/-! ### `best` (rule 3's `recBest`) -/

/-- `best`'s first part: `R[0]`'s entry of `d` when rule 2 applies. -/
def r0find (li : Bool) (R : List (Nat × sp.Report)) (d : sp.CmdId) : Option sp.RepEntry :=
  if li then none else match R with
    | [] => none
    | r0 :: _ => r0.2.entries.find? (·.id == d)

theorem recBest_found {li : Bool} {R U acks : List (Nat × sp.Report)} {d : sp.CmdId}
    {e : sp.RepEntry} (h : r0find li R d = some e) :
    sp.recBest li R U acks d = some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩ := by
  unfold sp.recBest
  generalize hx : (if li = true then none else match R with
    | [] => none
    | r0 :: _ => r0.2.entries.find? (·.id == d)) = x
  unfold r0find at h; rw [hx] at h; subst h; rfl

theorem recBest_nf {li : Bool} {R U acks : List (Nat × sp.Report)} {d : sp.CmdId}
    (h : r0find li R d = none) :
    sp.recBest li R U acks d = match sp.recPick U d with
      | some b => some b
      | none => sp.recPick acks d := by
  unfold sp.recBest
  generalize hx : (if li = true then none else match R with
    | [] => none
    | r0 :: _ => r0.2.entries.find? (·.id == d)) = x
  unfold r0find at h; rw [hx] at h; subst h; rfl

/-- `best`'s second part, one entry (Go's `b == nil || a.Phases[i] > b.phase`). -/
def pickStep (d : sp.CmdId) (b : Option sp.RecEntry) (e : sp.RepEntry) : Option sp.RecEntry :=
  if e.id != d then b else match b with
    | none => some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
    | some b0 => if e.phase.toNat > b0.phase then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩
        else some b0

theorem recPick_eq2 (l : List (Nat × sp.Report)) (d : sp.CmdId) :
    sp.recPick l d = l.foldl (fun b a => a.2.entries.foldl (pickStep d) b) none := rfl

theorem find_take_succ_none {l : List sp.RepEntry} {n : Nat} {e : sp.RepEntry} {d : sp.CmdId}
    (h : (l.take n).find? (·.id == d) = none) (he : l[n]? = some e) (hne : e.id ≠ d) :
    (l.take (n + 1)).find? (·.id == d) = none := by
  rw [List.take_add_one, he]; simp [List.find?_append, h, hne]

theorem find_take_succ_some {l : List sp.RepEntry} {n : Nat} {e : sp.RepEntry} {d : sp.CmdId}
    (h : (l.take n).find? (·.id == d) = none) (he : l[n]? = some e) (hid : e.id = d) :
    l.find? (·.id == d) = some e := by
  rw [← List.take_append_drop (n + 1) l, List.find?_append, List.take_add_one, he]
  simp [List.find?_append, h, hid]

theorem pickStep_ne {d : sp.CmdId} {b : Option sp.RecEntry} {e : sp.RepEntry} (h : e.id ≠ d) :
    pickStep d b e = b := by
  unfold pickStep; simp [h]

/-- `best`'s test: `b == nil || a.Phases[i] > b.phase`. -/
def pickCond (b : Option sp.RecEntry) (e : sp.RepEntry) : Bool :=
  match b with
  | none => true
  | some b0 => decide (e.phase.toNat > b0.phase)

theorem pickStep_eq {d : sp.CmdId} {b : Option sp.RecEntry} {e : sp.RepEntry} (h : e.id = d) :
    pickStep d b e = if pickCond b e then some ⟨e.phase.toNat, e.cmd, e.dep, 2⟩ else b := by
  unfold pickStep pickCond; cases b with
  | none => simp [h]
  | some b0 => by_cases hg : e.phase.toNat > b0.phase <;> simp [h, hg]

theorem recPick_pr (Lp : List Pr) (d : sp.CmdId) :
    sp.recPick (Lp.map Prod.snd) d =
      Lp.foldl (fun b q => q.2.2.entries.foldl (pickStep d) b) none := by
  rw [recPick_eq2, List.foldl_map]

theorem lt_two_of {x t : w64} (h1 : 0 + 1 + 1 = sint.nat x) (h2 : sint.Z t < sint.Z x) :
    sint.Z t < 2 := by
  have : sint.Z x = 2 := by
    have h3 : sint.nat x = (sint.Z x).toNat := rfl
    rw [h3] at h1; omega
  omega

theorem ge_two_of {x t : w64} (h1 : 0 + 1 + 1 = sint.nat x) (h2 : ¬ sint.Z t < sint.Z x) :
    2 ≤ sint.Z t := by
  have : sint.Z x = 2 := by
    have h3 : sint.nat x = (sint.Z x).toNat := rfl
    rw [h3] at h1; omega
  omega

theorem sint_small (x : w64) (h : x.toNat ≤ 3) : sint.Z x = (x.toNat : Int) := by
  have : x = W64 (x.toNat : Int) := by word
  rw [this]; word

/-! ### Rules 3b and 4 -/

theorem findIdx_take_succ (l : List sp.RepEntry) (n : Nat) (e : sp.RepEntry) (he : l[n]? = some e)
    (y : sp.CmdId) :
    (l.take (n + 1)).findIdx? (·.id == y) = match (l.take n).findIdx? (·.id == y) with
      | some i => some i
      | none => if e.id == y then some n else none := by
  have hn : n < l.length := by
    rcases Nat.lt_or_ge n l.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at he; cases he
  rw [List.take_add_one, he, Option.toList_some, List.findIdx?_append]
  have hl : (l.take n).length = n := by simp; omega
  cases h : (l.take n).findIdx? (·.id == y) <;> simp [List.findIdx?_cons, hl]

/-- The kept list keeps its keys and its commands (no `SCAN`). -/
def KS (k3 k : sp.Kept) : Prop :=
  (∀ y, (k.get y).isSome = (k3.get y).isSome) ∧ (k.map Prod.fst).Nodup ∧
  ∀ y e, k.get y = some e → e.cmd.op ≠ swift.opSCAN

theorem KS.setDep {k3 k : sp.Kept} (h : KS k3 k) {c : sp.CmdId} {ec : sp.RecEntry}
    (hc : k.get c = some ec) (D : List sp.CmdId) : KS k3 (k.set c { ec with dep := D }) := by
  refine ⟨fun y => ?_, sp.Kept.keys_set_nodup _ _ _ h.2.1, fun y e hy => ?_⟩
  · rw [sp.Kept.get_set]; by_cases hyc : y = c
    · subst hyc; simp [← h.1 y, hc]
    · simp [hyc, h.1 y]
  · rw [sp.Kept.get_set] at hy; by_cases hyc : y = c
    · subst hyc; simp at hy; subst hy; exact h.2.2 y ec hc
    · simp [hyc] at hy; exact h.2.2 y e hy

theorem r3pair_eq {r0 : Nat × sp.Report} {c : sp.CmdId} {pc : Nat} {k : sp.Kept} {w : sp.CmdId}
    {ew ec : sp.RecEntry} (hw : k.get w = some ew) (hc : k.get c = some ec) :
    sp.rule3bPair r0 c pc k w = match sp.recPos r0 w with
      | none => k
      | some pw => if (Bool.or (Bool.or (w == c) (decide (pw > pc))) (!(sp.Cmd.conflict ew.cmd ec.cmd))) then k
          else if Bool.or (ec.dep.contains w) (sp.recReaches k w c) then k
          else k.set c { ec with dep := ec.dep ++ [w] } := by
  unfold sp.rule3bPair; rw [hw, hc]; cases sp.recPos r0 w <;> rfl

theorem r3cmd_eq {r0 : Nat × sp.Report} {ids : List sp.CmdId} {k : sp.Kept} {c : sp.CmdId}
    {ec : sp.RecEntry} (hc : k.get c = some ec) :
    sp.rule3bCmd r0 ids k c = match sp.recPos r0 c with
      | none => k
      | some pc => if ec.cls == 0 then k else ids.foldl (sp.rule3bPair r0 c pc) k := by
  unfold sp.rule3bCmd; rw [hc]; cases sp.recPos r0 c <;> rfl

theorem r3pair_KS {r0 : Nat × sp.Report} {c : sp.CmdId} {pc : Nat} {k3 k : sp.Kept} {w : sp.CmdId}
    (h : KS k3 k) : KS k3 (sp.rule3bPair r0 c pc k w) := by
  unfold sp.rule3bPair
  split
  · rename_i ew ec pw _ hc _
    split
    · exact h
    · split
      · exact h
      · exact h.setDep hc _
  · exact h

theorem noscan_of {N : Nat} {reps : List (Nat × sp.Report)} (hok : swift.RepsOk N reps)
    {Am : List (Nat × sp.Report)} (hA : ∀ a ∈ Am, a ∈ reps) {k : sp.Kept} (hc : sp.CmdFrom Am k) :
    ∀ y e, k.get y = some e → e.cmd.op ≠ swift.opSCAN := by
  intro y e hy
  obtain ⟨a, ha, re, hre, -, h2⟩ := hc y e hy
  rw [← h2]; exact (hok.ents a (hA a ha) re hre).2.1

theorem r4cmd_eq {ids : List sp.CmdId} {k : sp.Kept} {c : sp.CmdId} {ec : sp.RecEntry}
    (hc : k.get c = some ec) :
    sp.rule4Cmd ids k c = if ec.cls == 0 then k else ids.foldl (sp.rule4Pair c) k := by
  unfold sp.rule4Cmd; rw [hc]

theorem r4pair_KS {c : sp.CmdId} {k3 k : sp.Kept} {a : sp.CmdId} (h : KS k3 k) :
    KS k3 (sp.rule4Pair c k a) := by
  unfold sp.rule4Pair
  split
  · rename_i ea ec _ hc
    split
    · exact h
    · split
      · exact h.setDep hc _
      · exact h
  · exact h

theorem KS_len {k3 k : sp.Kept} (h : KS k3 k) (h3 : (k3.map Prod.fst).Nodup) :
    k.length = k3.length := by
  have hp : (k.map Prod.fst).Perm (k3.map Prod.fst) := by
    rw [List.perm_ext_iff_of_nodup h.2.1 h3]
    intro x; rw [← sp.Kept.get_isSome_iff, ← sp.Kept.get_isSome_iff, h.1 x]
  simpa using hp.length_eq

end swift.rec

end Perennial.github_com.imdea_software.swiftpaxos
