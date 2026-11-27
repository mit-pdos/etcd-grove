/- Lean-first (no Rocq counterpart).

# `etcd/dist/deployment`: what Go's `WellFormed` checks means `Deployment.WellFormed`

`goWellFormed d` is what `WellFormed` has checked when it returns `nil` (clause by clause, over the
Go values: `Defs.lean`'s vocabulary); `goWellFormed_sound` builds the typed deployment it encodes
(`typedOf`) and proves it well formed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

/-- **What `WellFormed(d)` returning `nil` has checked** (its clauses in Go's order). -/
def goWellFormed (d : Deployment) : Prop :=
  -- 1. a member; the names valid and distinct
  d.members ≠ [] ∧ (d.members.map Member.name).Nodup ∧
  (∀ m ∈ d.members, typed.nameOk m.name = true) ∧
  -- 5 (first): every kind known, every workload within its bounds
  (∀ w ∈ d.workloads, kindKnown w.kind ∧ w.goBoundsOk) ∧
  -- 2. the client machines' lists, the addresses
  d.nodes.length = d.workloads.length ∧
  (∀ a ∈ d.addrs, Net.addrOk a = true) ∧ d.addrs.Nodup ∧
  (∀ (j : Nat) (w : Workload) (ns : List GoString), d.workloads[j]? = some w →
    d.nodes[j]? = some ns → W64 ns.length = w.goNodeCount ∧ ns.length < 2 ^ 63) ∧
  -- 3. the member ids
  goIdsOk d.ids d.workloads ∧
  -- 4. the token, the server configuration
  d.token ≠ [] ∧ 1 ≤ uint.Z d.cfg.snapCount ∧ 1 ≤ uint.Z d.cfg.catchUp ∧
  (d.cfg.retention ≠ W64 0 →
    (d.cfg.compactorMode = go!"revision" ∧ 1 ≤ sint.Z d.cfg.retention) ∨
    (d.cfg.compactorMode = go!"periodic" ∧ 10 ≤ sint.Z d.cfg.retention)) ∧
  -- 5. compatible, the token provider, compact, leaseExpiry
  goCompatible d.workloads ∧
  (∀ w ∈ d.workloads, kindAlone w.kind = true → d.cfg.auth = true) ∧
  (∀ w ∈ d.workloads, w.kind = W64 3 →
    ¬ (d.cfg.retention ≠ W64 0 ∧ d.cfg.compactorMode = go!"periodic")) ∧
  (∀ w ∈ d.workloads, w.kind = W64 9 → d.cfg.auth = false) ∧
  -- the token provider only with a workload that needs it
  (d.cfg.auth = true → ∃ w ∈ d.workloads, kindAlone w.kind = true) ∧
  -- the token provider only with the compactor off
  (d.cfg.auth = true → d.cfg.retention = W64 0) ∧
  -- the sizes (1, 2, 4)
  d.members.length ≤ typed.maxMembers ∧ (∀ m ∈ d.members, m.name.length ≤ typed.maxNameLen) ∧
  (∀ a ∈ d.addrs, a.length ≤ typed.maxLen) ∧ d.token.length ≤ typed.maxLen

/-- The typed workload a Go workload of a known kind encodes. -/
def typedW (w : Workload) : typed.Workload :=
  let c := (sint.Z w.clients).toNat
  let o := (sint.Z w.ops).toNat
  if w.kind = W64 0 then .kv c o
  else if w.kind = W64 1 then .watch c o
  else if w.kind = W64 2 then .cache c o
  else if w.kind = W64 3 then .compact
  else if w.kind = W64 4 then .putget
  else if w.kind = W64 5 then .auth
  else if w.kind = W64 6 then .authLease
  else if w.kind = W64 7 then .leaseRead
  else if w.kind = W64 8 then .leaseCatchup
  else if w.kind = W64 9 then .leaseExpiry
  else .durable c

/-- The typed server configuration. -/
def typedCfg (c : ServerCfg) : typed.ServerCfg where
  compactor :=
    if c.retention = W64 0 then .off
    else if c.compactorMode = go!"revision" then .revision (sint.Z c.retention).toNat
    else .periodic (sint.Z c.retention).toNat
  snapCount := uint.nat c.snapCount
  catchUp := uint.nat c.catchUp
  auth := c.auth

/-- The typed deployment. -/
def typedOf (d : Deployment) : typed.Deployment where
  members := d.members
  token := d.token
  cfg := typedCfg d.cfg
  workloads := d.workloads.map typedW
  nodes := d.nodes

/-- A known kind is one of `0, ..., 10`. -/
theorem kindKnown_cases (k : w64) (h : kindKnown k) :
    k = W64 0 ∨ k = W64 1 ∨ k = W64 2 ∨ k = W64 3 ∨ k = W64 4 ∨ k = W64 5 ∨ k = W64 6 ∨
    k = W64 7 ∨ k = W64 8 ∨ k = W64 9 ∨ k = W64 10 := by
  unfold kindKnown at h
  have h' : uint.nat k < 11 := by word
  rcases (by omega : uint.nat k = 0 ∨ uint.nat k = 1 ∨ uint.nat k = 2 ∨ uint.nat k = 3 ∨
    uint.nat k = 4 ∨ uint.nat k = 5 ∨ uint.nat k = 6 ∨ uint.nat k = 7 ∨ uint.nat k = 8 ∨
    uint.nat k = 9 ∨ uint.nat k = 10) with e | e | e | e | e | e | e | e | e | e | e
  · left; word
  · right; left; word
  · right; right; left; word
  · right; right; right; left; word
  · right; right; right; right; left; word
  · right; right; right; right; right; left; word
  · right; right; right; right; right; right; left; word
  · right; right; right; right; right; right; right; left; word
  · right; right; right; right; right; right; right; right; left; word
  · right; right; right; right; right; right; right; right; right; left; word
  · right; right; right; right; right; right; right; right; right; right; word

/-- The typed workload's kind is the Go kind's number. -/
theorem typedW_kind (w : Workload) (h : kindKnown w.kind) : (typedW w).kind = uint.nat w.kind := by
  rcases kindKnown_cases _ h with e | e | e | e | e | e | e | e | e | e | e <;>
    simp [typedW, e, typed.Workload.kind]

/-- The typed workload's predicates are the Go kind's. -/
theorem typedW_preds (w : Workload) (h : kindKnown w.kind) :
    (typedW w).writesKeys = kindWritesKeys w.kind ∧
    (typedW w).needsSoleWriter = kindNeedsSoleWriter w.kind ∧
    (typedW w).alone = kindAlone w.kind ∧ (typedW w).needsAuth = kindAlone w.kind ∧
    (typedW w).grantsLeases = kindGrantsLeases w.kind ∧
    (typedW w).needsNoExpiry = kindNeedsNoExpiry w.kind ∧
    ((typedW w = .compact) ↔ w.kind = W64 3) ∧ ((typedW w = .leaseExpiry) ↔ w.kind = W64 9) := by
  rcases kindKnown_cases _ h with e | e | e | e | e | e | e | e | e | e | e <;>
    simp [typedW, e, typed.Workload.writesKeys, typed.Workload.needsSoleWriter,
      typed.Workload.alone, typed.Workload.needsAuth, typed.Workload.grantsLeases,
      typed.Workload.needsNoExpiry, kindWritesKeys, kindNeedsSoleWriter, kindAlone,
      kindGrantsLeases, kindNeedsNoExpiry]

/-- `c * o ≤ m` from Go's `c == 0 || o <= m/c` (`c, o ≥ 0`). -/
theorem mul_le_of_div {c o m : Int} (hc : 0 ≤ c) (h : c = 0 ∨ o ≤ m / c) : c * o ≤ m ∨ c = 0 := by
  by_cases hc0 : c = 0
  · exact Or.inr hc0
  rcases h with h | h
  · exact Or.inr h
  · left
    have hc' : 0 < c := by omega
    calc c * o ≤ c * (m / c) := Int.mul_le_mul_of_nonneg_left h hc
      _ ≤ m := Int.mul_ediv_self_le (by omega)

/-- `c.toNat * o.toNat < B` from Go's `c == 0 || o <= (B-1)/c` (`c, o ≥ 0`). -/
theorem toNat_mul_lt (c o : Int) (B : Nat) (hB : 0 < B) (hc : 0 ≤ c) (ho : 0 ≤ o)
    (h : c = 0 ∨ o ≤ ((B : Int) - 1) / c) : c.toNat * o.toNat < B := by
  have e : ((c.toNat * o.toNat : Nat) : Int) = c * o := by
    push_cast; rw [Int.toNat_of_nonneg hc, Int.toNat_of_nonneg ho]
  rcases mul_le_of_div hc h with h' | h'
  · generalize c * o = p at e h'
    omega
  · subst h'; simp [hB]

/-- A known kind's workload within Go's bounds encodes its typed workload, which is within its
bounds. -/
theorem typedW_encodes (w : Workload) (h : kindKnown w.kind) (hb : w.goBoundsOk) :
    (typedW w).Encodes w ∧ (typedW w).BoundsOk := by
  unfold Workload.goBoundsOk at hb
  rcases kindKnown_cases _ h with e | e | e | e | e | e | e | e | e | e | e <;>
    simp (config := { decide := true }) only [e, typedW, ↓reduceIte, true_or, or_true] at hb ⊢ <;>
    simp only [typed.Workload.Encodes, typed.Workload.BoundsOk, e, true_and, and_true]
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact ⟨⟨by omega, by omega⟩, by omega, toNat_mul_lt _ _ (2 ^ 60) (by decide) h1 h3 h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact ⟨⟨by omega, by omega⟩, by omega, toNat_mul_lt _ _ (2 ^ 62) (by decide) h1 h3 h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    exact ⟨⟨by omega, by omega⟩, by omega, toNat_mul_lt _ _ (2 ^ 62) (by decide) h1 h3 h4⟩
  · obtain ⟨h1, h2⟩ := hb
    exact ⟨by omega, by omega⟩

/-- The server configuration Go accepts encodes its typed configuration, which is supported. -/
theorem typedCfg_encodes (c : ServerCfg) (hs : 1 ≤ uint.Z c.snapCount) (hc : 1 ≤ uint.Z c.catchUp)
    (hr : c.retention ≠ W64 0 →
      (c.compactorMode = go!"revision" ∧ 1 ≤ sint.Z c.retention) ∨
      (c.compactorMode = go!"periodic" ∧ 10 ≤ sint.Z c.retention)) :
    (typedCfg c).Encodes c ∧ (typedCfg c).Supported := by
  have hsn : ((uint.nat c.snapCount : Nat) : Int) = uint.Z c.snapCount := by word
  have hcn : ((uint.nat c.catchUp : Nat) : Int) = uint.Z c.catchUp := by word
  have hsb : uint.nat c.snapCount < 2 ^ 64 := by word
  have hcb : uint.nat c.catchUp < 2 ^ 64 := by word
  have hrb : sint.Z c.retention < 2 ^ 63 := by word
  refine ⟨⟨?_, hsn.symm, hcn.symm, rfl⟩, ⟨?_, show 1 ≤ uint.nat c.snapCount by word, hsb,
    show 1 ≤ uint.nat c.catchUp by word, hcb⟩⟩
  · unfold typedCfg
    by_cases h0 : c.retention = W64 0
    · rw [if_pos h0, h0]; rfl
    · rw [if_neg h0]
      rcases hr h0 with ⟨hm, hp⟩ | ⟨hm, hp⟩
      · rw [if_pos hm]; exact ⟨hm, by omega, by omega⟩
      · have hne : ¬ c.compactorMode = go!"revision" := by rw [hm]; decide
        rw [if_neg hne]; exact ⟨hm, by omega, by omega⟩
  · unfold typedCfg
    by_cases h0 : c.retention = W64 0
    · rw [if_pos h0]; trivial
    · rw [if_neg h0]
      rcases hr h0 with ⟨hm, hp⟩ | ⟨hm, hp⟩
      · rw [if_pos hm]; exact ⟨by omega, by omega⟩
      · have hne : ¬ c.compactorMode = go!"revision" := by rw [hm]; decide
        rw [if_neg hne]; exact ⟨by omega, by omega⟩

/-- The typed workload's client machines: Go's `len(d.Nodes[j]) == NodeCount(w)`. -/
theorem typedW_nodeCount (w : Workload) (h : kindKnown w.kind) (hb : w.goBoundsOk) (n : Nat)
    (hn : W64 n = w.goNodeCount) (hlt : n < 2 ^ 63) : (typedW w).nodeCount = n := by
  unfold Workload.goNodeCount at hn
  unfold Workload.goBoundsOk at hb
  rcases kindKnown_cases _ h with e | e | e | e | e | e | e | e | e | e | e <;>
    simp (config := { decide := true }) only [e, typedW, typed.Workload.nodeCount, ↓reduceIte,
      true_or, or_true] at hn hb ⊢
  · obtain ⟨h1, -⟩ := hb
    rw [← hn] at h1 ⊢
    have : sint.Z (W64 n) = n := by word
    omega
  · obtain ⟨h1, -⟩ := hb
    rw [← hn] at h1 ⊢
    have : sint.Z (W64 n) = n := by word
    omega
  · obtain ⟨h1, -⟩ := hb
    rw [← hn] at h1 ⊢
    have : sint.Z (W64 n) = n := by word
    omega
  all_goals word

/-- `R (f x) x` for every `x` of `l`: `l.map f` and `l` are related by `R`. -/
theorem forall₂_map_self {α β : Type} (l : List α) (f : α → β) (R : β → α → Prop)
    (h : ∀ x ∈ l, R (f x) x) : List.Forall₂ R (l.map f) l := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    exact .cons (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- **Soundness of Go's check**: a deployment that passes it is well formed. -/
theorem goWellFormed_sound (d : Deployment) (h : goWellFormed d) : d.WellFormed := by
  obtain ⟨hmem, hnames, hnameOk, hkinds, hnl, haddrOk, haddrNd, hnodes, hids, htok, hsc, hcu, hret,
    hcompat, hauth, hcompact, hexp, hneed, hacmp, hsz⟩ := h
  obtain ⟨hcE, hcS⟩ := typedCfg_encodes d.cfg hsc hcu hret
  have hwE : ∀ w ∈ d.workloads, (typedW w).Encodes w ∧ (typedW w).BoundsOk :=
    fun w hw => typedW_encodes w (hkinds w hw).1 (hkinds w hw).2
  refine ⟨typedOf d, ⟨rfl, rfl, hcE, ?_, rfl⟩, ?_⟩
  · exact forall₂_map_self d.workloads typedW _ (fun w hw => (hwE w hw).1)
  obtain ⟨hnd, halone, hsole, hnoexp⟩ := hcompat
  have haddrs : (typedOf d).addrs = d.addrs := rfl
  refine ⟨hmem, hnames, hnameOk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htok, hcS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [haddrs]; exact haddrOk
  · rw [haddrs]; exact haddrNd
  · simp only [typedOf, List.length_map]; exact hnl
  · intro p hp
    simp only [typedOf] at hp
    rw [List.zip_map_left, List.mem_map] at hp
    obtain ⟨⟨w, ns⟩, hm, rfl⟩ := hp
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
    rw [List.getElem?_zip_eq_some] at hj
    obtain ⟨hw, hns⟩ := hj
    have hwm : w ∈ d.workloads := List.mem_of_getElem? hw
    obtain ⟨hc, hlt⟩ := hnodes j w ns hw hns
    exact (typedW_nodeCount w (hkinds w hwm).1 (hkinds w hwm).2 _ hc hlt).symm
  · exact hids.1
  · exact hids.2.1
  · exact hids.2.2.1
  · intro ⟨w, hw, hg⟩
    simp only [typedOf, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact hids.2.2.2 ⟨w', hw', by rw [← (typedW_preds w' (hkinds w' hw').1).2.2.2.2.1]; exact hg⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have e : (typedOf d).workloads.map typed.Workload.kind =
          d.workloads.map (fun w => uint.nat w.kind) := by
        simp only [typedOf, List.map_map]
        apply List.map_congr_left
        intro w hw
        exact typedW_kind w (hkinds w hw).1
      rw [e]
      unfold List.Nodup at hnd ⊢
      rw [List.pairwise_map] at hnd ⊢
      exact hnd.imp (fun {a b} hne heq => hne (by word))
    · intro ⟨w, hw, ha⟩
      simp only [typedOf, List.mem_map] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      simp only [typedOf, List.length_map]
      exact halone w' hw' (by rw [← (typedW_preds w' (hkinds w' hw').1).2.2.1]; exact ha)
    · intro w hw hs w2 hw2 hne
      simp only [typedOf, List.mem_map] at hw hw2
      obtain ⟨x, hx, rfl⟩ := hw
      obtain ⟨y, hy, rfl⟩ := hw2
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hy
      have hij : j ≠ i := by
        rintro rfl
        rw [hi] at hj
        cases hj
        exact hne rfl
      rw [(typedW_preds y (hkinds y hy).1).1]
      exact hsole i j x y hi hj (Ne.symm hij)
        (Or.inl (by rw [← (typedW_preds x (hkinds x hx).1).2.1]; exact hs))
    · intro ⟨he, w, hw, hn⟩
      simp only [typedOf, List.mem_map] at he hw
      obtain ⟨x, hx, hxe⟩ := he
      obtain ⟨y, hy, rfl⟩ := hw
      exact hnoexp ⟨⟨x, hx, ((typedW_preds x (hkinds x hx).1).2.2.2.2.2.2.2).1 hxe⟩, y, hy,
        by rw [← (typedW_preds y (hkinds y hy).1).2.2.2.2.2.1]; exact hn⟩
    · intro w hw hg w2 hw2 hne
      simp only [typedOf, List.mem_map] at hw hw2
      obtain ⟨x, hx, rfl⟩ := hw
      obtain ⟨y, hy, rfl⟩ := hw2
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hy
      have hij : j ≠ i := by
        rintro rfl
        rw [hi] at hj
        cases hj
        exact hne rfl
      rw [(typedW_preds y (hkinds y hy).1).1]
      exact hsole i j x y hi hj (Ne.symm hij)
        (Or.inr (by rw [← (typedW_preds x (hkinds x hx).1).2.2.2.2.1]; exact hg))
  · intro w hw
    simp only [typedOf, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact (hwE w' hw').2
  · intro w hw hna
    simp only [typedOf, List.mem_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    exact hauth w' hw' (by rw [← (typedW_preds w' (hkinds w' hw').1).2.2.2.1]; exact hna)
  · intro ha
    obtain ⟨w, hw, hal⟩ := hneed ha
    exact ⟨typedW w, List.mem_map.2 ⟨w, hw, rfl⟩,
      by rw [(typedW_preds w (hkinds w hw).1).2.2.2.1]; exact hal⟩
  · intro ha
    simp only [typedOf, typedCfg] at ha ⊢
    rw [if_pos (hacmp ha)]
  · intro hc
    simp only [typedOf, List.mem_map] at hc
    obtain ⟨x, hx, hxe⟩ := hc
    have h3 := ((typedW_preds x (hkinds x hx).1).2.2.2.2.2.2.1).1 hxe
    have hno := hcompact x hx h3
    simp only [typedOf, typedCfg, typed.Compactor.isPeriodic]
    by_cases h0 : d.cfg.retention = W64 0
    · simp [h0]
    · by_cases hm : d.cfg.compactorMode = go!"revision"
      · simp [show ¬ d.cfg.retention = 0#64 from h0, hm]
      · exfalso
        rcases hret h0 with ⟨hm', -⟩ | ⟨hm', -⟩
        · exact hm hm'
        · exact hno ⟨h0, hm'⟩
  · intro ⟨ha, hle⟩
    simp only [typedOf, List.mem_map] at hle
    obtain ⟨x, hx, hxe⟩ := hle
    have h9 := ((typedW_preds x (hkinds x hx).1).2.2.2.2.2.2.2).1 hxe
    have := hexp x hx h9
    simp only [typedOf, typedCfg] at ha
    rw [this] at ha
    cases ha
  · rw [haddrs]; exact hsz

end etcd_dist
end EtcdGrove
end Perennial

end
