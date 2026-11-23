/-
The conflicts map and attribute computation: `updateConflicts` only raises entries and covers the
recorded instance (`uc_le`, `uc_cov`); `updateAttributes` returns deps of length `N`, at least the
input, covering every conflicts entry it reads (`ua_spec`). Generic `foldl` lemmas.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HLocal

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace ConfProof

open HLocal AuxProof

/-! ## `foldl` -/

theorem foldl_inv {α β : Type} (f : α → β → α) (I : α → Prop) (l : List β)
    (hstep : ∀ a x, x ∈ l → I a → I (f a x)) (a : α) (ha : I a) : I (l.foldl f a) := by
  induction l generalizing a with
  | nil => exact ha
  | cons y ys ih =>
    rw [List.foldl_cons]
    exact ih (fun a x hx => hstep a x (List.mem_cons_of_mem _ hx)) _
      (hstep a y List.mem_cons_self ha)

theorem foldl_rel {α β : Type} (f : α → β → α) (R : α → α → Prop) (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c) (l : List β)
    (hstep : ∀ a x, x ∈ l → R a (f a x)) (a : α) : R a (l.foldl f a) := by
  induction l generalizing a with
  | nil => exact hrefl a
  | cons y ys ih =>
    rw [List.foldl_cons]
    exact htrans _ _ _ (hstep a y List.mem_cons_self)
      (ih (fun a x hx => hstep a x (List.mem_cons_of_mem _ hx)) _)

theorem foldl_mem {α β : Type} (f : α → β → α) (R : α → α → Prop) (G : α → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c) (l : List β)
    (hstep : ∀ a x, x ∈ l → R a (f a x)) (x0 : β) (hx0 : x0 ∈ l) (hG : ∀ a, G (f a x0))
    (hGR : ∀ a b, G a → R a b → G b) (a : α) : G (l.foldl f a) := by
  induction l generalizing a with
  | nil => cases hx0
  | cons y ys ih =>
    rw [List.foldl_cons]
    by_cases hy : x0 = y
    · subst hy
      exact hGR _ _ (hG a) (foldl_rel f R hrefl htrans ys
        (fun a x hx => hstep a x (List.mem_cons_of_mem _ hx)) _)
    · have : x0 ∈ ys := by
        rcases List.mem_cons.mp hx0 with h | h
        · exact absurd h hy
        · exact h
      exact ih (fun a x hx => hstep a x (List.mem_cons_of_mem _ hx)) this _

/-! ## `updateConflicts` -/

/-- Every entry of `σ` is still there in `σ'`, at least as high. -/
def confLe (σ σ' : RState) : Prop :=
  ∀ q k p, σ.conflicts q k = some p → ∃ p', σ'.conflicts q k = some p' ∧
    zz p.last ≤ zz p'.last ∧ zz p.lastWrite ≤ zz p'.lastWrite

theorem confLe_refl (σ : RState) : confLe σ σ :=
  fun _ _ p h => ⟨p, h, Int.le_refl _, Int.le_refl _⟩

theorem confLe_trans {σ σ' σ'' : RState} (h1 : confLe σ σ') (h2 : confLe σ' σ'') :
    confLe σ σ'' := by
  intro q k p h
  obtain ⟨p', h', a1, a2⟩ := h1 q k p h
  obtain ⟨p'', h'', b1, b2⟩ := h2 q k p' h'
  exact ⟨p'', h'', Int.le_trans a1 b1, Int.le_trans a2 b2⟩

theorem confLe_of_eq {σ σ' : RState} (h : σ'.conflicts = σ.conflicts) : confLe σ σ' := by
  intro q k p hp; rw [← h] at hp; exact ⟨p, hp, Int.le_refl _, Int.le_refl _⟩

/-- The entry `updateConflicts` writes for command `c`. -/
def ucEnt (σ : RState) (q0 : Nat) (n : w32) (c : WCmd) : InstPair :=
  match σ.conflicts q0 c.key with
  | some p =>
    ⟨if p.last.slt n then n else p.last,
     if p.lastWrite.slt n ∧ c.op ≠ opGET then n else p.lastWrite⟩
  | none => ⟨n, if c.op ≠ opGET then n else W32 (-1)⟩

/-- One step of `updateConflicts`. -/
def ucStep (q0 : Nat) (n seq : w32) (σ : RState) (c : WCmd) : RState :=
  let s' : w32 :=
    match σ.maxSeqPerKey c.key with
    | some s => if s.slt seq then seq else s
    | none => seq
  { σ with conflicts := upd σ.conflicts q0 (upd (σ.conflicts q0) c.key (some (ucEnt σ q0 n c))),
           lastScan := if c.op = opSCAN ∧ (σ.lastScan q0).slt n then upd σ.lastScan q0 n
             else σ.lastScan,
           lastPut := if c.op = opPUT ∧ (σ.lastPut q0).slt n then upd σ.lastPut q0 n
             else σ.lastPut,
           maxSeqPerKey := upd σ.maxSeqPerKey c.key (some s') }

theorem uc_eq (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) :
    updateConflicts σ cmds q0 n seq = cmds.foldl (ucStep q0 n seq) σ := rfl

theorem ucStep_conf (q0 : Nat) (n seq : w32) (σ : RState) (c : WCmd) (q : Nat) (k : w64) :
    (ucStep q0 n seq σ c).conflicts q k =
      if q = q0 ∧ k = c.key then some (ucEnt σ q0 n c) else σ.conflicts q k := by
  simp only [ucStep, upd_apply]
  by_cases h1 : q = q0
  · subst h1; by_cases h2 : k = c.key <;> simp [h2]
  · simp [h1]

theorem ucEnt_ge (σ : RState) (q0 : Nat) (n : w32) (c : WCmd) (p : InstPair)
    (h : σ.conflicts q0 c.key = some p) :
    zz p.last ≤ zz (ucEnt σ q0 n c).last ∧ zz p.lastWrite ≤ zz (ucEnt σ q0 n c).lastWrite := by
  simp only [ucEnt, h]
  constructor
  · split
    · rename_i h1; exact Int.le_of_lt ((slt_iff _ _).mp h1)
    · exact Int.le_refl _
  · split
    · rename_i h1; exact Int.le_of_lt ((slt_iff _ _).mp (by simpa using h1.1))
    · exact Int.le_refl _

theorem ucEnt_cov (σ : RState) (q0 : Nat) (n : w32) (c : WCmd) :
    zz n ≤ zz (ucEnt σ q0 n c).last ∧ (c.op ≠ opGET → zz n ≤ zz (ucEnt σ q0 n c).lastWrite) := by
  unfold ucEnt
  cases hp : σ.conflicts q0 c.key with
  | some p =>
    simp only
    refine ⟨?_, fun h => ?_⟩
    · by_cases h1 : p.last.slt n = true
      · rw [if_pos h1]; exact Int.le_refl _
      · rw [if_neg h1]; exact (slt_false _ _).mp (by simpa using h1)
    · by_cases h1 : p.lastWrite.slt n = true
      · rw [if_pos ⟨h1, h⟩]; exact Int.le_refl _
      · rw [if_neg (fun h' => h1 h'.1)]; exact (slt_false _ _).mp (by simpa using h1)
  | none =>
    simp only
    exact ⟨Int.le_refl _, fun h => by rw [if_pos h]; exact Int.le_refl _⟩

theorem ucStep_le (q0 : Nat) (n seq : w32) (σ : RState) (c : WCmd) :
    confLe σ (ucStep q0 n seq σ c) := by
  intro q k p h
  rw [ucStep_conf]
  split
  · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
    exact ⟨_, rfl, ucEnt_ge σ q n c p h⟩
  · exact ⟨p, h, Int.le_refl _, Int.le_refl _⟩

theorem confLe_cover {σ σ' : RState} (h : confLe σ σ') {q : Nat} {k : w64} {j : Int} {c : WCmd}
    (hp : ∃ p, σ.conflicts q k = some p ∧ j ≤ zz p.last ∧ (c.op ≠ opGET → j ≤ zz p.lastWrite)) :
    ∃ p, σ'.conflicts q k = some p ∧ j ≤ zz p.last ∧ (c.op ≠ opGET → j ≤ zz p.lastWrite) := by
  obtain ⟨p, hp, a1, a2⟩ := hp
  obtain ⟨p', hp', b1, b2⟩ := h q k p hp
  exact ⟨p', hp', Int.le_trans a1 b1, fun hc => Int.le_trans (a2 hc) b2⟩

theorem uc_le (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) :
    confLe σ (updateConflicts σ cmds q0 n seq) := by
  rw [uc_eq]
  exact foldl_rel (ucStep q0 n seq) confLe confLe_refl (fun _ _ _ => confLe_trans) cmds
    (fun a c _ => ucStep_le q0 n seq a c) σ

theorem uc_cov (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) :
    ∀ c ∈ cmds, ∃ p, (updateConflicts σ cmds q0 n seq).conflicts q0 c.key = some p ∧
      zz n ≤ zz p.last ∧ (c.op ≠ opGET → zz n ≤ zz p.lastWrite) := by
  intro c hc
  rw [uc_eq]
  let G : RState → Prop := fun σ => ∃ p, σ.conflicts q0 c.key = some p ∧
      zz n ≤ zz p.last ∧ (c.op ≠ opGET → zz n ≤ zz p.lastWrite)
  refine foldl_mem (ucStep q0 n seq) confLe G confLe_refl (fun _ _ _ => confLe_trans) cmds
    (fun a c _ => ucStep_le q0 n seq a c) c hc (fun a => ?_) (fun a b ha hab => ?_) σ
  · refine ⟨_, ?_, ucEnt_cov a q0 n c⟩
    rw [ucStep_conf, if_pos ⟨rfl, rfl⟩]
  · obtain ⟨p, hp, h1, h2⟩ := ha
    obtain ⟨p', hp', b1, b2⟩ := hab _ _ _ hp
    exact ⟨p', hp', Int.le_trans h1 b1, fun h => Int.le_trans (h2 h) b2⟩

/-! ### `updateConflicts`' class arrays (stage 2, fix S1) -/

theorem ucStep_scan (q0 : Nat) (n seq : w32) (σ : RState) (c : WCmd) (q : Nat) :
    (ucStep q0 n seq σ c).lastScan q =
      if q = q0 ∧ c.op = opSCAN ∧ (σ.lastScan q0).slt n then n else σ.lastScan q := by
  simp only [ucStep]
  by_cases h : c.op = opSCAN ∧ (σ.lastScan q0).slt n = true
  · rw [if_pos h]; by_cases hq : q = q0
    · subst hq; simp [h]
    · simp [hq]
  · rw [if_neg h]; simp only [if_neg (fun h' : _ ∧ _ => h h'.2)]

theorem ucStep_put (q0 : Nat) (n seq : w32) (σ : RState) (c : WCmd) (q : Nat) :
    (ucStep q0 n seq σ c).lastPut q =
      if q = q0 ∧ c.op = opPUT ∧ (σ.lastPut q0).slt n then n else σ.lastPut q := by
  simp only [ucStep]
  by_cases h : c.op = opPUT ∧ (σ.lastPut q0).slt n = true
  · rw [if_pos h]; by_cases hq : q = q0
    · subst hq; simp [h]
    · simp [hq]
  · rw [if_neg h]; simp only [if_neg (fun h' : _ ∧ _ => h h'.2)]

theorem ucStep_clsLe (q0 : Nat) (n seq : w32) (σ : RState) (c : WCmd) :
    clsLe σ (ucStep q0 n seq σ c) := by
  intro q
  rw [ucStep_scan, ucStep_put]
  constructor
  · split
    · rename_i h; obtain ⟨rfl, -, h⟩ := h; exact Int.le_of_lt ((slt_iff _ _).mp h)
    · exact Int.le_refl _
  · split
    · rename_i h; obtain ⟨rfl, -, h⟩ := h; exact Int.le_of_lt ((slt_iff _ _).mp h)
    · exact Int.le_refl _

theorem uc_clsLe (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) :
    clsLe σ (updateConflicts σ cmds q0 n seq) := by
  rw [uc_eq]
  exact foldl_rel (ucStep q0 n seq) clsLe clsLe_refl (fun _ _ _ => clsLe_trans) cmds
    (fun a c _ => ucStep_clsLe q0 n seq a c) σ

/-- A recorded SCAN / PUT raises its row's last SCAN / last PUT to at least the instance. -/
theorem uc_cls_cov (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) :
    ∀ c ∈ cmds, (c.op = opSCAN → zz n ≤ zz ((updateConflicts σ cmds q0 n seq).lastScan q0)) ∧
      (c.op = opPUT → zz n ≤ zz ((updateConflicts σ cmds q0 n seq).lastPut q0)) := by
  intro c hc
  rw [uc_eq]
  let G : RState → Prop := fun σ => (c.op = opSCAN → zz n ≤ zz (σ.lastScan q0)) ∧
      (c.op = opPUT → zz n ≤ zz (σ.lastPut q0))
  refine foldl_mem (ucStep q0 n seq) clsLe G clsLe_refl (fun _ _ _ => clsLe_trans) cmds
    (fun a c _ => ucStep_clsLe q0 n seq a c) c hc (fun a => ⟨fun hs => ?_, fun hp => ?_⟩)
    (fun a b ha hab => ⟨fun h => Int.le_trans (ha.1 h) (hab q0).1,
      fun h => Int.le_trans (ha.2 h) (hab q0).2⟩) σ
  · rw [ucStep_scan]
    by_cases h : (a.lastScan q0).slt n = true
    · rw [if_pos ⟨rfl, hs, h⟩]; exact Int.le_refl _
    · rw [if_neg (fun h' => h h'.2.2)]; exact (slt_false _ _).mp (by simpa using h)
  · rw [ucStep_put]
    by_cases h : (a.lastPut q0).slt n = true
    · rw [if_pos ⟨rfl, hp, h⟩]; exact Int.le_refl _
    · rw [if_neg (fun h' => h h'.2.2)]; exact (slt_false _ _).mp (by simpa using h)

/-- Every class entry after `updateConflicts` is an entry before, or the instance in its row. -/
theorem uc_cls_src (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) (q : Nat) :
    ((updateConflicts σ cmds q0 n seq).lastScan q = σ.lastScan q ∨
      (q = q0 ∧ (updateConflicts σ cmds q0 n seq).lastScan q = n)) ∧
    ((updateConflicts σ cmds q0 n seq).lastPut q = σ.lastPut q ∨
      (q = q0 ∧ (updateConflicts σ cmds q0 n seq).lastPut q = n)) := by
  rw [uc_eq]
  refine foldl_inv (ucStep q0 n seq) (fun a => (a.lastScan q = σ.lastScan q ∨
      (q = q0 ∧ a.lastScan q = n)) ∧ (a.lastPut q = σ.lastPut q ∨ (q = q0 ∧ a.lastPut q = n)))
    cmds (fun a c _ h => ⟨?_, ?_⟩) σ ⟨Or.inl rfl, Or.inl rfl⟩
  · rw [ucStep_scan]; split
    · rename_i h'; exact Or.inr ⟨h'.1, rfl⟩
    · exact h.1
  · rw [ucStep_put]; split
    · rename_i h'; exact Or.inr ⟨h'.1, rfl⟩
    · exact h.2

/-- `updateConflicts` keeps the instances. -/
theorem uc_inst (σ : RState) (cmds : List WCmd) (q0 : Nat) (n seq : w32) :
    (updateConflicts σ cmds q0 n seq).inst = σ.inst := by
  rw [uc_eq]
  exact foldl_inv (ucStep q0 n seq) (fun a => a.inst = σ.inst) cmds (fun a c _ h => h) σ rfl

theorem clsWf_uc {σ : RState} (h : ClsWf σ) (cmds : List WCmd) (q0 : Nat) (n seq : w32)
    (hn : 0 ≤ zz n → σ.inst ⟨q0, toN n⟩ ≠ none) : ClsWf (updateConflicts σ cmds q0 n seq) := by
  intro q hq
  obtain ⟨a1, a2, a3, a4⟩ := h q hq
  obtain ⟨s1, s2⟩ := uc_cls_src σ cmds q0 n seq q
  obtain ⟨l1, l2⟩ := uc_clsLe σ cmds q0 n seq q
  rw [uc_inst]
  refine ⟨fun h0 => ?_, fun h0 => ?_, Int.le_trans a3 l1, Int.le_trans a4 l2⟩
  · rcases s1 with e | ⟨rfl, e⟩ <;> rw [e] at h0 ⊢
    · exact a1 h0
    · exact hn h0
  · rcases s2 with e | ⟨rfl, e⟩ <;> rw [e] at h0 ⊢
    · exact a2 h0
    · exact hn h0

theorem clsCov_uc (σ : RState) (cx : List WCmd) (n seq : w32) (x : InstId)
    (hn : zz n = (x.i : Int)) : ClsCov (updateConflicts σ cx x.q n seq) x cx := by
  intro c hc
  obtain ⟨h1, h2⟩ := uc_cls_cov σ cx x.q n seq c hc
  exact ⟨fun e => hn ▸ h1 e, fun e => hn ▸ h2 e⟩


/-! ## `updateAttributes` -/

/-- The entry `updateAttributes` reads for command `c`. -/
def uaD (p : InstPair) (c : WCmd) : w32 := if c.op ≠ opGET then p.last else p.lastWrite

theorem uaD_cases (p : InstPair) (c : WCmd) : uaD p c = p.last ∨ uaD p c = p.lastWrite := by
  unfold uaD; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- One raise of `updateAttributes`' first loop over row `q`'s entry `d`. -/
def uaStep (σ : RState) (q : Nat) (acc : w32 × List w32 × Bool) (d : w32) :
    w32 × List w32 × Bool :=
  if (acc.2.1.getD q (W32 0)).slt d then
    (if acc.1.sle (((σ.inst ⟨q, toN d⟩).map (·.seq)).getD (W32 0))
      then (((σ.inst ⟨q, toN d⟩).map (·.seq)).getD (W32 0)) + 1 else acc.1,
     acc.2.1.set q d, true)
  else acc

/-- The class entry (fix S1) `updateAttributes` reads for command `c` in row `q`. -/
def uaClass (σ : RState) (q : Nat) (c : WCmd) : w32 :=
  if c.op = opSCAN then σ.lastPut q else if c.op = opPUT then σ.lastScan q else W32 (-1)

/-- The inner step of `updateAttributes`' first loop (row `q`, command `c`): the key's entry,
then the class entry (stage 2). -/
def uaG (σ : RState) (q : Nat) (acc : w32 × List w32 × Bool) (c : WCmd) :
    w32 × List w32 × Bool :=
  uaStep σ q (match σ.conflicts q c.key with
    | none => acc
    | some p => uaStep σ q acc (uaD p c)) (uaClass σ q c)

/-- The step of `updateAttributes`' second loop. -/
def uaH (σ : RState) (acc : w32 × List w32 × Bool) (c : WCmd) : w32 × List w32 × Bool :=
  match σ.maxSeqPerKey c.key with
  | some s => if acc.1.sle s then (s + 1, acc.2.1, true) else acc
  | none => acc

theorem ua_eq (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) :
    updateAttributes σ cmds seq deps =
      cmds.foldl (uaH σ) ((List.range nR).foldl (fun acc q => cmds.foldl (uaG σ q) acc)
        (seq, deps, false)) := rfl

/-- Deps only grow, in place. -/
def DR (a b : w32 × List w32 × Bool) : Prop :=
  b.2.1.length = a.2.1.length ∧ ∀ q, zz (a.2.1.getD q (W32 0)) ≤ zz (b.2.1.getD q (W32 0))

theorem DR_refl (a : w32 × List w32 × Bool) : DR a a := ⟨rfl, fun _ => Int.le_refl _⟩

theorem DR_trans (a b c : w32 × List w32 × Bool) (h1 : DR a b) (h2 : DR b c) : DR a c :=
  ⟨by rw [h2.1, h1.1], fun q => Int.le_trans (h1.2 q) (h2.2 q)⟩

theorem getD_set (l : List w32) (q q' : Nat) (d : w32) :
    (l.set q d).getD q' (W32 0) = if q' = q ∧ q < l.length then d else l.getD q' (W32 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : q = q'
  · subst h
    by_cases hl : q < l.length
    · simp [hl]
    · simp [hl]
  · simp [h, Ne.symm h]

theorem uaStep_DR (σ : RState) (q : Nat) (a : w32 × List w32 × Bool) (d : w32) :
    DR a (uaStep σ q a d) := by
  unfold uaStep
  by_cases h : (a.2.1.getD q (W32 0)).slt d = true
  · rw [if_pos h]
    refine ⟨by simp, fun q' => ?_⟩
    simp only [getD_set]
    split
    · rename_i hq; obtain ⟨rfl, -⟩ := hq; exact Int.le_of_lt ((slt_iff _ _).mp h)
    · exact Int.le_refl _
  · rw [if_neg h]; exact DR_refl a

/-- After a raise over `d`, row `q`'s entry is at least `d` (deps of length `N`). -/
theorem uaStep_cov (σ : RState) (q : Nat) (hq : q < nR) (a : w32 × List w32 × Bool) (d : w32)
    (hl : a.2.1.length = nR) : zz d ≤ zz ((uaStep σ q a d).2.1.getD q (W32 0)) := by
  unfold uaStep
  by_cases h : (a.2.1.getD q (W32 0)).slt d = true
  · rw [if_pos h]
    simp only [getD_set]
    simp [hl, hq]
  · rw [if_neg h]
    exact (slt_false _ _).mp (by simpa using h)

/-- A raise changes at most row `q`'s entry, to `d`, from below. -/
theorem uaStep_src (σ : RState) (q : Nat) (a : w32 × List w32 × Bool) (d : w32) (q' : Nat) :
    (uaStep σ q a d).2.1.getD q' (W32 0) = a.2.1.getD q' (W32 0) ∨
    ((uaStep σ q a d).2.1.getD q' (W32 0) = d ∧ zz (a.2.1.getD q' (W32 0)) < zz d ∧ q' = q) := by
  unfold uaStep
  by_cases h : (a.2.1.getD q (W32 0)).slt d = true
  · rw [if_pos h]
    simp only [getD_set]
    split
    · rename_i hq; obtain ⟨rfl, -⟩ := hq
      exact Or.inr ⟨rfl, (slt_iff _ _).mp h, rfl⟩
    · exact Or.inl rfl
  · rw [if_neg h]; exact Or.inl rfl

/-- The key step of `uaG`. -/
def uaK (σ : RState) (q : Nat) (acc : w32 × List w32 × Bool) (c : WCmd) :
    w32 × List w32 × Bool :=
  match σ.conflicts q c.key with
  | none => acc
  | some p => uaStep σ q acc (uaD p c)

theorem uaG_eq (σ : RState) (q : Nat) (a : w32 × List w32 × Bool) (c : WCmd) :
    uaG σ q a c = uaStep σ q (uaK σ q a c) (uaClass σ q c) := rfl

theorem uaK_DR (σ : RState) (q : Nat) (a : w32 × List w32 × Bool) (c : WCmd) :
    DR a (uaK σ q a c) := by
  unfold uaK
  cases σ.conflicts q c.key with
  | none => exact DR_refl a
  | some p => exact uaStep_DR σ q a _

theorem uaG_DR (σ : RState) (q : Nat) (a : w32 × List w32 × Bool) (c : WCmd) :
    DR a (uaG σ q a c) := by
  rw [uaG_eq]
  exact DR_trans _ _ _ (uaK_DR σ q a c) (uaStep_DR σ q _ _)

theorem uaH_deps (σ : RState) (a : w32 × List w32 × Bool) (c : WCmd) :
    (uaH σ a c).2.1 = a.2.1 := by
  unfold uaH; split
  · split <;> rfl
  · rfl

/-- Where an entry of the result comes from: a conflicts entry, the row's last SCAN or last PUT,
or `-1` (the class step of a command neither SCAN nor PUT). -/
def ASrc (σ : RState) (q : Nat) (d : w32) : Prop :=
  (∃ k p, σ.conflicts q k = some p ∧ (d = p.last ∨ d = p.lastWrite)) ∨
    d = σ.lastScan q ∨ d = σ.lastPut q ∨ d = W32 (-1)

theorem uaClass_src (σ : RState) (q : Nat) (c : WCmd) : ASrc σ q (uaClass σ q c) := by
  unfold uaClass ASrc
  split
  · exact Or.inr (Or.inr (Or.inl rfl))
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- The entries of the result: an input entry, or a higher entry of a source (`ASrc`). -/
def DSrc (σ : RState) (deps : List w32) (a : w32 × List w32 × Bool) : Prop :=
  DR (W32 0, deps, false) a ∧
  ∀ q, a.2.1.getD q (W32 0) = deps.getD q (W32 0) ∨
    (ASrc σ q (a.2.1.getD q (W32 0)) ∧
     zz (deps.getD q (W32 0)) < zz (a.2.1.getD q (W32 0)))

theorem uaStep_DSrc (σ : RState) (deps : List w32) (q : Nat) (a : w32 × List w32 × Bool)
    (d : w32) (hd : ASrc σ q d) (h : DSrc σ deps a) : DSrc σ deps (uaStep σ q a d) := by
  refine ⟨DR_trans _ _ _ h.1 (uaStep_DR σ q a d), fun q' => ?_⟩
  rcases uaStep_src σ q a d q' with e | ⟨e, hlt, rfl⟩
  · rw [e]; exact h.2 q'
  · rw [e]
    exact Or.inr ⟨hd, Int.lt_of_le_of_lt (h.1.2 q') hlt⟩

theorem uaG_DSrc (σ : RState) (deps : List w32) (q : Nat) (a : w32 × List w32 × Bool)
    (c : WCmd) (h : DSrc σ deps a) : DSrc σ deps (uaG σ q a c) := by
  rw [uaG_eq]
  refine uaStep_DSrc σ deps q _ _ (uaClass_src σ q c) ?_
  unfold uaK
  cases hp : σ.conflicts q c.key with
  | none => exact h
  | some p => exact uaStep_DSrc σ deps q a _ (Or.inl ⟨c.key, p, hp, uaD_cases p c⟩) h

/-- The attributes `updateAttributes` returns (`ua_spec`): the deps keep their length, only grow,
cover every conflicts entry read and (stage 2, fix S1) every class entry read (`uaClass`), and
each entry is the input's or a higher source entry (`ASrc`). -/
theorem ua_spec (σ : RState) (cmds : List WCmd) (seq : w32) (deps : List w32) :
    (updateAttributes σ cmds seq deps).2.1.length = deps.length ∧
    (∀ q, zz (deps.getD q (W32 0)) ≤ zz ((updateAttributes σ cmds seq deps).2.1.getD q (W32 0))) ∧
    (deps.length = nR → ∀ q < nR, ∀ c ∈ cmds,
      (∀ p, σ.conflicts q c.key = some p →
        zz (uaD p c) ≤ zz ((updateAttributes σ cmds seq deps).2.1.getD q (W32 0))) ∧
      zz (uaClass σ q c) ≤ zz ((updateAttributes σ cmds seq deps).2.1.getD q (W32 0))) ∧
    (∀ q, (updateAttributes σ cmds seq deps).2.1.getD q (W32 0) = deps.getD q (W32 0) ∨
      (ASrc σ q ((updateAttributes σ cmds seq deps).2.1.getD q (W32 0)) ∧
       zz (deps.getD q (W32 0)) < zz ((updateAttributes σ cmds seq deps).2.1.getD q (W32 0)))) := by
  rw [ua_eq]
  generalize hF : (fun acc q => cmds.foldl (uaG σ q) acc) = F
  have hH : (cmds.foldl (uaH σ) ((List.range nR).foldl F (seq, deps, false))).2.1 =
      ((List.range nR).foldl F (seq, deps, false)).2.1 :=
    foldl_inv (uaH σ) (fun a => a.2.1 = ((List.range nR).foldl F (seq, deps, false)).2.1) cmds
      (fun a c _ h => by rw [uaH_deps]; exact h) _ rfl
  rw [hH]
  have hFR : ∀ a q, DR a (F a q) := by
    intro a q; rw [← hF]
    exact foldl_rel (uaG σ q) DR DR_refl DR_trans cmds (fun a c _ => uaG_DR σ q a c) a
  have hR := foldl_rel F DR DR_refl DR_trans (List.range nR) (fun a q _ => hFR a q)
    (seq, deps, false)
  -- a lower bound on row `q` reached by one inner step persists
  have hlow : ∀ q < nR, ∀ c ∈ cmds, ∀ (j : w32), (∀ a, a.2.1.length = nR →
      zz j ≤ zz ((uaG σ q a c).2.1.getD q (W32 0))) → deps.length = nR →
      zz j ≤ zz (((List.range nR).foldl F (seq, deps, false)).2.1.getD q (W32 0)) := by
    intro q hq c hc j hj hl
    let G : w32 × List w32 × Bool → Prop := fun a => a.2.1.length = nR →
      zz j ≤ zz (a.2.1.getD q (W32 0))
    have hGR : ∀ a b, G a → DR a b → G b := by
      intro a b ha hab hb
      exact Int.le_trans (ha (by rw [← hab.1]; exact hb)) (hab.2 q)
    have hGq : ∀ a, G (F a q) := by
      intro a; rw [← hF]
      exact foldl_mem (uaG σ q) DR G DR_refl DR_trans cmds (fun a c _ => uaG_DR σ q a c) c hc
        (fun a ha => hj a (by rw [← (uaG_DR σ q a c).1]; exact ha)) hGR a
    exact foldl_mem F DR G DR_refl DR_trans (List.range nR) (fun a q _ => hFR a q) q
      (List.mem_range.mpr hq) hGq hGR _ (by rw [hR.1, hl])
  refine ⟨hR.1, hR.2, fun hl q hq c hc => ⟨fun p hp => ?_, ?_⟩, ?_⟩
  · refine hlow q hq c hc _ (fun a hla => ?_) hl
    rw [uaG_eq]
    have hK : zz (uaD p c) ≤ zz ((uaK σ q a c).2.1.getD q (W32 0)) := by
      unfold uaK; rw [hp]; exact uaStep_cov σ q hq a _ hla
    exact Int.le_trans hK ((uaStep_DR σ q _ _).2 q)
  · refine hlow q hq c hc _ (fun a hla => ?_) hl
    rw [uaG_eq]
    exact uaStep_cov σ q hq _ _ (by rw [(uaK_DR σ q a c).1]; exact hla)
  · have hS : DSrc σ deps ((List.range nR).foldl F (seq, deps, false)) := by
      refine foldl_inv F (DSrc σ deps) (List.range nR) (fun a q _ h => ?_) _
        ⟨DR_refl _, fun q => Or.inl rfl⟩
      rw [← hF]
      exact foldl_inv (uaG σ q) (DSrc σ deps) cmds (fun a c _ h => uaG_DSrc σ deps q a c h) a h
    exact hS.2

theorem getD_irrel (l : List w32) (q : Nat) (a b : w32) (h : q < l.length) :
    l.getD q a = l.getD q b := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- (stage 2) The attributes computed by a replica cover every instance it recorded whose
commands interfere (`interfereCode`, with the class clause of fix S1): the key clause by
`confCover`, the class clause by `classCover`. -/
theorem ua_covers {S : Sys} (hA : InvAux S) {i : Nat} (hi : i < nR) {e : Event} {y : InstId}
    {cy : List WCmd} (he : S.ev i e) (hrec : e.recorded = some (y, cy)) (hyq : y.q < nR)
    (σu : RState) (hσu : σu.conflicts = (S.rep i).conflicts)
    (hus : σu.lastScan = (S.rep i).lastScan) (hup : σu.lastPut = (S.rep i).lastPut)
    (cmds : List WCmd) (seq : w32) (deps0 : List w32) (hlen : deps0.length = nR)
    (hint : interfereCode cmds cy) :
    covers (updateAttributes σu cmds seq deps0).2.1 y := by
  obtain ⟨c, hc, c', hc', hint⟩ := hint
  obtain ⟨u1, -, u3, -⟩ := ua_spec σu cmds seq deps0
  unfold covers
  rw [getD_irrel _ _ _ (W32 0) (by rw [u1, hlen]; exact hyq)]
  rcases hint with ⟨hk, hop⟩ | ⟨hs, hpt⟩ | ⟨hpt, hs⟩
  · obtain ⟨pe, hpe, hl, hlw⟩ := hA.confCover i hi e y cy he hrec c' hc'
    have hcov := (u3 hlen y.q hyq c hc).1 pe (by rw [hσu, hk]; exact hpe)
    refine Int.le_trans ?_ hcov
    unfold uaD
    by_cases hg : c.op ≠ opGET
    · rw [if_pos hg]; exact hl
    · rw [if_neg hg]
      exact hlw (by rcases hop with h | h; exact absurd h hg; exact h)
  · have hcov := (u3 hlen y.q hyq c hc).2
    have hcl := (hA.classCover i hi e y cy he hrec c' hc').2 hpt
    refine Int.le_trans hcl (Int.le_trans (Int.le_of_eq ?_) hcov)
    simp only [uaClass, if_pos hs, hup]
  · have hcov := (u3 hlen y.q hyq c hc).2
    have hcl := (hA.classCover i hi e y cy he hrec c' hc').1 hs
    refine Int.le_trans hcl (Int.le_trans (Int.le_of_eq ?_) hcov)
    have hns : c.op ≠ opSCAN := by rw [hpt]; decide
    simp only [uaClass, if_neg hns, if_pos hpt, hus]

end ConfProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
