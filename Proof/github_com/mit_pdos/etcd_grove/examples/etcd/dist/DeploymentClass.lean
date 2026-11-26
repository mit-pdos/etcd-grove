/- Lean-first (no Rocq counterpart).

# `etcd/dist`: a well-formed deployment's class, lease mode and compaction setting (`notes/etcd-dist-plan.md` §27.1-27.2, F8)

The full start (`dist/Start.lean`) allocates a deployment's cluster and its workloads' shares by the deployment's
**class** (§27.1, decision D1): with auth off, a well-formed deployment's workloads are
- E: none;
- Ls: lease kinds only (`leaseRead` 7, `leaseCatchup` 8, `leaseExpiry` 9), at least one;
- S: one sole writer `s` (`kv` 0, `watch` 1, `cache` 2) and otherwise at most `leaseRead`;
- P: `compact` 3, `putget` 4, `durable` 10 (at least one) and maybe `leaseRead`;
and with auth on they are `[auth]` (5) or `[authLease]` (6) (`auth_class`; decisions Q1/Q2 of §27.7, which
`Compatible`/`WellFormed` carry). Here, over Go's deployment value:
- `lmOf d` (D4): the cluster's lease mode, `.revocable` with a `leaseExpiry` workload, `.mono` with a
  `leaseCatchup` one, `.none` otherwise; its side conditions as `clusterAllocN` (`lmOf_revocable_apart`) and
  `member_boot_dist` (`lmOf_mono_noExpiry`, `lmOf_auth_revocable`) take them;
- `cmpOf d` (D4): the KV's compaction mode and the cluster's retention, `(true, 1)` with a `compact` workload,
  otherwise by the compactor (off `(false, 0)`, revision `r` `(true, r)`, periodic `(true, 0)`): `cmpOf_bootCfg`
  (the compactor's slot `v3compactor.bootCfg`), `cmpOf_auth` (with auth on `(false, 0)`, `clusterAllocN`'s `Hon`),
  `cmpOf_compact`;
- `class_authOff`: the four auth-off classes with the pure facts the start needs (§27.2 `classOf_spec`): the
  client machines only at the sole writer (every other workload's node list empty), the sole writer's bounds
  (`SoleBounds`, as `kvOnly_shape` gives kv's), `lmOf d = .none` in S and P;
- `kinds_nodup`: the workloads' kinds are distinct; `pfxs_apart`: the shared-KV prefixes `[pg/, du/, cw/]` (P's)
  none a prefix of another (`kvPfx_alloc`'s premise).

No axiom, no `sorry`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.BootCfg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

/-! ## Lists -/

section lists

theorem cls_forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ {i : Nat} {b : β}, l2[i]? = some b →
      ∃ a, l1[i]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hab⟩
  | _, _, .cons _ t, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact cls_forall₂_get t h

theorem cls_forall₂_get_left {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ {i : Nat} {a : α}, l1[i]? = some a →
      ∃ b, l2[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hab⟩
  | _, _, .cons _ t, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact cls_forall₂_get_left t h

theorem cls_forall₂_mem {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {b : β} (hb : b ∈ l2) : ∃ a ∈ l1, R a b := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
  obtain ⟨a, ha, hr⟩ := cls_forall₂_get h hi
  exact ⟨a, List.mem_of_getElem? ha, hr⟩

theorem cls_forall₂_map {α β γ : Type} {R : α → β → Prop} (f : α → γ) (g : β → γ)
    (hfg : ∀ a b, R a b → g b = f a) :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → l2.map g = l1.map f
  | _, _, .nil => rfl
  | _, _, .cons hab t => by
      simp only [List.map_cons, hfg _ _ hab, cls_forall₂_map f g hfg t]

/-- A list of lists empty but at `j` flattens to its `j`-th. -/
theorem cls_flatten_single {α : Type} :
    ∀ (L : List (List α)) (j : Nat) (x : List α), L[j]? = some x →
      (∀ (j' : Nat) (y : List α), L[j']? = some y → j' ≠ j → y = []) → L.flatten = x
  | [], _, _, h, _ => by simp at h
  | a :: L, 0, x, h, ho => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have : L.flatten = [] := List.flatten_eq_nil_iff.2 (fun y hy => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
      exact ho (i + 1) y (by simpa using hi) (by omega))
    simp [this]
  | a :: L, j + 1, x, h, ho => by
    simp only [List.getElem?_cons_succ] at h
    have ha : a = [] := ho 0 a rfl (by omega)
    subst ha
    simp only [List.flatten_cons, List.nil_append]
    exact cls_flatten_single L j x h (fun j' y hy hne => ho (j' + 1) y (by simpa using hy) (by omega))

theorem cls_nodeList_length {α β : Type} : ∀ (ws : List α) (ns : List (List β)), ws.length = ns.length →
    ((ws.zip ns).flatMap (fun p => p.2.zipIdx.map (fun q => (p.1, q.2, q.1)))).length = ns.flatten.length
  | [], [], _ => rfl
  | _ :: ws, n :: ns, h => by
    simp only [List.zip_cons_cons, List.flatMap_cons, List.length_append, List.length_map, List.length_zipIdx,
      List.flatten_cons]
    rw [cls_nodeList_length ws ns (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end lists

/-! ## The typed deployment's classes -/

namespace typed

/-- A typed workload's kind as Go's `deployment.Kind` value. -/
def Workload.kindW (w : Workload) : w64 := W64 (w.kind : Int)

theorem Workload.Encodes.kind {tw : Workload} {w : etcd_dist.Workload} (h : tw.Encodes w) :
    w.kind = tw.kindW := by
  cases tw <;> simp only [Workload.Encodes] at h <;> first | exact h | exact h.1

/-- **A typed deployment's classes with auth off** (§27.1). -/
theorem class_typed {t : Deployment} (hw : t.WellFormed) (ha : t.cfg.auth = false) :
    t.workloads = [] ∨
    (t.workloads ≠ [] ∧ ∀ w ∈ t.workloads, w = .leaseRead ∨ w = .leaseCatchup ∨ w = .leaseExpiry) ∨
    (∃ (j : Nat) (s : Workload), t.workloads[j]? = some s ∧
      ((∃ c o, s = .kv c o) ∨ (∃ n o, s = .watch n o) ∨ (∃ n o, s = .cache n o)) ∧
      ∀ (j' : Nat) (w' : Workload), t.workloads[j']? = some w' → j' ≠ j → w' = .leaseRead) ∨
    ((∃ w ∈ t.workloads, w = .compact ∨ w = .putget ∨ ∃ n, w = .durable n) ∧
      ∀ w ∈ t.workloads, w = .compact ∨ w = .putget ∨ w = .leaseRead ∨ ∃ n, w = .durable n) := by
  -- `WellFormed`'s conjuncts by their statements, not their positions
  have hcomp : Compatible t.workloads := by grind [Deployment.WellFormed]
  have hauth : ∀ w ∈ t.workloads, w.needsAuth = true → t.cfg.auth = true := by
    grind [Deployment.WellFormed]
  obtain ⟨hnd, -, hsole, -, hgr⟩ := hcomp
  have hna : ∀ w ∈ t.workloads, w.needsAuth = false := fun w hw => by
    cases h : w.needsAuth
    · rfl
    · have := hauth w hw h
      rw [ha] at this
      cases this
  have hwnd : t.workloads.Nodup := List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) hnd
  by_cases hs : ∃ s ∈ t.workloads, s.needsSoleWriter = true
  · obtain ⟨s, hsm, hss⟩ := hs
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hsm
    have hsa := hna s hsm
    have hsk : (∃ c o, s = .kv c o) ∨ (∃ n o, s = .watch n o) ∨ (∃ n o, s = .cache n o) := by
      revert hss hsa
      cases s <;> simp [Workload.needsSoleWriter, Workload.needsAuth]
    have hsw : s.writesKeys = true := by
      rcases hsk with ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ <;> rfl
    refine Or.inr (Or.inr (Or.inl ⟨j, s, hj, hsk, ?_⟩))
    intro j' w' hj' hne
    have hw'm := List.mem_of_getElem? hj'
    have hne' : w' ≠ s := by
      intro e
      subst e
      exact hne ((List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hj').1 hwnd).1
        (by rw [hj', hj]))
    have hwk := hsole s hsm hss w' hw'm hne'
    have hg : w'.grantsLeases = false := by
      cases h : w'.grantsLeases
      · rfl
      · have := hgr w' hw'm h s hsm (Ne.symm hne')
        rw [hsw] at this
        cases this
    revert hwk hg
    cases w' <;> simp [Workload.writesKeys, Workload.grantsLeases]
  · have hs' : ∀ s ∈ t.workloads, s.needsSoleWriter = false := fun s hm => by
      cases h : s.needsSoleWriter
      · rfl
      · exact absurd ⟨s, hm, h⟩ hs
    by_cases hp : ∃ w ∈ t.workloads, w.writesKeys = true
    · obtain ⟨w, hwm, hwk⟩ := hp
      refine Or.inr (Or.inr (Or.inr ⟨⟨w, hwm, ?_⟩, ?_⟩))
      · have := hs' w hwm
        revert hwk this
        cases w <;> simp [Workload.writesKeys, Workload.needsSoleWriter]
      · intro w' hw'm
        have h1 := hs' w' hw'm
        have hg : w'.grantsLeases = false := by
          cases h : w'.grantsLeases
          · rfl
          · by_cases he : w = w'
            · subst he
              revert hwk h h1
              cases w <;> simp [Workload.writesKeys, Workload.grantsLeases, Workload.needsSoleWriter]
            · have := hgr w' hw'm h w hwm he
              rw [hwk] at this
              cases this
        revert h1 hg
        cases w' <;> simp [Workload.needsSoleWriter, Workload.grantsLeases]
    · have hp' : ∀ w ∈ t.workloads, w.writesKeys = false := fun w hm => by
        cases h : w.writesKeys
        · rfl
        · exact absurd ⟨w, hm, h⟩ hp
      by_cases he : t.workloads = []
      · exact Or.inl he
      · refine Or.inr (Or.inl ⟨he, fun w hw => ?_⟩)
        have := hp' w hw
        revert this
        cases w <;> simp [Workload.writesKeys]

/-- A typed deployment's node list at a workload's index has the workload's client machines. -/
theorem node_at {t : Deployment} (hw : t.WellFormed) {j : Nat} {ns : List GoString}
    (hn : t.nodes[j]? = some ns) : ∃ tw, t.workloads[j]? = some tw ∧ ns.length = tw.nodeCount := by
  have hcnt : ∀ p ∈ t.workloads.zip t.nodes, p.2.length = p.1.nodeCount := by
    grind [Deployment.WellFormed]
  have hl : t.nodes.length = t.workloads.length := by grind [Deployment.WellFormed]
  have hj : j < t.workloads.length := by
    rw [← hl]; exact (List.getElem?_eq_some_iff.1 hn).1
  refine ⟨t.workloads[j], List.getElem?_eq_getElem hj, ?_⟩
  exact hcnt (t.workloads[j], ns)
    (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨List.getElem?_eq_getElem hj, hn⟩))

end typed

/-! ## The deployment's parameters (Go's value) -/

/-- **The deployment has a workload of kind `k`.** -/
def Deployment.hasKind (d : Deployment) (k : w64) : Bool :=
  d.workloads.any (fun w => decide (w.kind = k))

theorem Deployment.hasKind_iff (d : Deployment) (k : w64) :
    d.hasKind k = true ↔ ∃ w ∈ d.workloads, w.kind = k := by
  simp [Deployment.hasKind]

theorem Deployment.hasKind_false (d : Deployment) (k : w64) (h : ∀ w ∈ d.workloads, w.kind ≠ k) :
    d.hasKind k = false := by
  cases hk : d.hasKind k
  · rfl
  · obtain ⟨w, hw, e⟩ := (d.hasKind_iff k).1 hk
    exact absurd e (h w hw)

/-- **The cluster's lease mode** (D4): `.revocable` with a `leaseExpiry` workload (kind 9) or an `authLease` one
(kind 6: it revokes `Lu`; started with auth on, F7 fork), `.mono` with a `leaseCatchup` one (kind 8), `.none`
otherwise (the `auth` class is started with auth on at `.none`). -/
def lmOf (d : Deployment) : lease.Mode :=
  if d.hasKind (W64 9) then .revocable else if d.hasKind (W64 6) then .revocable
  else if d.hasKind (W64 8) then .mono else .none

/-- **The KV's compaction mode and the cluster's retention** (D4, §27.2's table): `(true, 1)` with a `compact`
workload (kind 3); otherwise by the compactor: off (the retention `0`) `(false, 0)`, revision mode at the
retention `r` `(true, r)`, periodic mode `(true, 0)`. -/
def cmpOf (d : Deployment) : Bool × Nat :=
  if d.hasKind (W64 3) then (true, 1)
  else if sint.Z d.cfg.retention = 0 then (false, 0)
  else if d.cfg.compactorMode = go!"revision" then (true, (sint.Z d.cfg.retention).toNat)
  else (true, 0)

theorem lmOf_none {d : Deployment}
    (h : ∀ w ∈ d.workloads, w.kind ≠ W64 8 ∧ w.kind ≠ W64 9 ∧ w.kind ≠ W64 6) :
    lmOf d = .none := by
  unfold lmOf
  rw [d.hasKind_false _ (fun w hw => (h w hw).2.1), d.hasKind_false _ (fun w hw => (h w hw).2.2),
    d.hasKind_false _ (fun w hw => (h w hw).1)]
  rfl

/-! ## Facts of a well-formed deployment -/

section facts

/-- A Go workload of a well-formed deployment encodes a typed one of it. -/
theorem wf_mem {d : Deployment} {t : typed.Deployment} (he : t.Encodes d) {w : Workload}
    (hw : w ∈ d.workloads) : ∃ tw ∈ t.workloads, tw.Encodes w :=
  cls_forall₂_mem he.2.2.2.1 hw

/-- **The workloads' kinds are distinct.** -/
theorem kinds_nodup {d : Deployment} (Hd : d.WellFormed) : (d.workloads.map (·.kind)).Nodup := by
  obtain ⟨t, he, hw⟩ := Hd
  have hcomp : typed.Compatible t.workloads := by grind [typed.Deployment.WellFormed]
  rw [cls_forall₂_map typed.Workload.kindW (·.kind) (fun _ _ h => h.kind) he.2.2.2.1]
  have hk : (t.workloads.map typed.Workload.kind).Nodup := hcomp.1
  refine List.Pairwise.map _ ?_ (List.pairwise_map.1 hk)
  intro a b hab e
  apply hab
  cases a <;> cases b <;> simp only [typed.Workload.kindW, typed.Workload.kind] at e ⊢ <;>
    first | rfl | exact absurd e (by decide)

/-- **The deployment with auth on is `[auth]` or `[authLease]`** (Q1: the token provider only with a workload that
needs it; such a workload runs alone). -/
theorem auth_class {d : Deployment} (Hd : d.WellFormed) (h : d.cfg.auth = true) :
    d.workloads.map (·.kind) = [W64 5] ∨ d.workloads.map (·.kind) = [W64 6] := by
  obtain ⟨t, he, hw⟩ := Hd
  have ha : t.cfg.auth = true := by rw [← he.2.2.1.2.2.2]; exact h
  have hq1 : t.cfg.auth = true → ∃ w ∈ t.workloads, w.needsAuth = true := by
    grind [typed.Deployment.WellFormed]
  have hcomp : typed.Compatible t.workloads := by grind [typed.Deployment.WellFormed]
  obtain ⟨w, hwm, hwa⟩ := hq1 ha
  have hal : w.alone = true := by revert hwa; cases w <;> simp [typed.Workload.needsAuth, typed.Workload.alone]
  have hl1 := hcomp.2.1 ⟨w, hwm, hal⟩
  obtain ⟨w', hw'⟩ := List.length_eq_one_iff.1 hl1
  have e : w = w' := List.mem_singleton.1 (hw' ▸ hwm)
  rw [cls_forall₂_map typed.Workload.kindW (·.kind) (fun _ _ h => h.kind) he.2.2.2.1, hw', ← e]
  clear hwm hw' e hl1 hal
  revert hwa
  cases w <;> simp [typed.Workload.needsAuth, typed.Workload.kindW, typed.Workload.kind]

/-- **The `auth` class** (F7 S14): a deployment whose one workload is `auth` has auth on, that workload alone and
one node list, of the four principals' machines (`nodeCount .auth = 4`). -/
theorem class_auth {d : Deployment} (Hd : d.WellFormed) (h5 : d.workloads.map (·.kind) = [W64 5]) :
    d.cfg.auth = true ∧ ∃ (w : Workload) (ns : List GoString), d.workloads = [w] ∧ w.kind = W64 5 ∧
      d.nodes = [ns] ∧ ns.length = 4 := by
  obtain ⟨w, hw⟩ : ∃ w, d.workloads = [w] := by
    have hl := congrArg List.length h5
    rw [List.length_map] at hl
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.1 hl
    exact ⟨w, hw⟩
  have hk : w.kind = W64 5 := by rw [hw] at h5; simpa using h5
  obtain ⟨t, he, htw⟩ := Hd
  have hws := he.2.2.2.1
  have hnn : t.nodes = d.nodes := he.2.2.2.2
  obtain ⟨tw, htwm, hen⟩ := wf_mem he (show w ∈ d.workloads by rw [hw]; exact List.mem_singleton_self w)
  have htk : tw = .auth := by
    have e := hen.kind
    rw [hk] at e
    clear htwm hen
    cases tw <;> simp only [typed.Workload.kindW, typed.Workload.kind] at e ⊢ <;> first | rfl | exact absurd e (by decide)
  subst htk
  have hauth : ∀ w ∈ t.workloads, w.needsAuth = true → t.cfg.auth = true := by
    grind [typed.Deployment.WellFormed]
  have hta : t.cfg.auth = true := hauth _ htwm rfl
  have hda : d.cfg.auth = true := by rw [he.2.2.1.2.2.2]; exact hta
  have htl : t.workloads.length = 1 := by rw [hws.length_eq, hw]; rfl
  have hl' : t.nodes.length = t.workloads.length := by grind [typed.Deployment.WellFormed]
  obtain ⟨ns, hns⟩ := List.length_eq_one_iff.1 (show d.nodes.length = 1 by rw [← hnn, hl', htl])
  obtain ⟨tw', htw'⟩ := List.length_eq_one_iff.1 htl
  have e' : typed.Workload.auth = tw' := List.mem_singleton.1 (htw' ▸ htwm)
  obtain ⟨tw0, h0, hl0⟩ := typed.node_at htw (j := 0) (ns := ns) (by rw [hnn, hns]; rfl)
  rw [htw'] at h0
  cases h0
  refine ⟨hda, w, ns, hw, hk, hns, ?_⟩
  rw [hl0, ← e']
  rfl

/-- **The `authLease` class** (F7 fork): a deployment whose one workload is `authLease` has auth on, that workload
alone and one empty node list (`nodeCount .authLease = 0`). -/
theorem class_authLease {d : Deployment} (Hd : d.WellFormed) (h6 : d.workloads.map (·.kind) = [W64 6]) :
    d.cfg.auth = true ∧ ∃ w : Workload, d.workloads = [w] ∧ w.kind = W64 6 ∧ d.nodes = [[]] := by
  obtain ⟨w, hw⟩ : ∃ w, d.workloads = [w] := by
    have hl := congrArg List.length h6
    rw [List.length_map] at hl
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.1 hl
    exact ⟨w, hw⟩
  have hk : w.kind = W64 6 := by rw [hw] at h6; simpa using h6
  obtain ⟨t, he, htw⟩ := Hd
  have hws := he.2.2.2.1
  have hnn : t.nodes = d.nodes := he.2.2.2.2
  obtain ⟨tw, htwm, hen⟩ := wf_mem he (show w ∈ d.workloads by rw [hw]; exact List.mem_singleton_self w)
  have htk : tw = .authLease := by
    have e := hen.kind
    rw [hk] at e
    clear htwm hen
    cases tw <;> simp only [typed.Workload.kindW, typed.Workload.kind] at e ⊢ <;> first | rfl | exact absurd e (by decide)
  subst htk
  have hauth : ∀ w ∈ t.workloads, w.needsAuth = true → t.cfg.auth = true := by
    grind [typed.Deployment.WellFormed]
  have hta : t.cfg.auth = true := hauth _ htwm rfl
  have hda : d.cfg.auth = true := by rw [he.2.2.1.2.2.2]; exact hta
  have htl : t.workloads.length = 1 := by rw [hws.length_eq, hw]; rfl
  have hl' : t.nodes.length = t.workloads.length := by grind [typed.Deployment.WellFormed]
  obtain ⟨ns, hns⟩ := List.length_eq_one_iff.1 (show d.nodes.length = 1 by rw [← hnn, hl', htl])
  obtain ⟨tw', htw'⟩ := List.length_eq_one_iff.1 htl
  have e' : typed.Workload.authLease = tw' := List.mem_singleton.1 (htw' ▸ htwm)
  obtain ⟨tw0, h0, hl0⟩ := typed.node_at htw (j := 0) (ns := ns) (by rw [hnn, hns]; rfl)
  rw [htw'] at h0
  cases h0
  have hl : ns.length = 0 := by rw [hl0, ← e']; rfl
  refine ⟨hda, w, hw, hk, ?_⟩
  rw [hns, List.eq_nil_of_length_eq_zero hl]

/-- **An `authLease` workload runs alone** (it needs auth, so the class is `[auth]` or `[authLease]`). -/
theorem kinds_of_authLease {d : Deployment} (Hd : d.WellFormed) (h : ∃ w ∈ d.workloads, w.kind = W64 6) :
    d.workloads.map (·.kind) = [W64 6] := by
  obtain ⟨w, hwm, hk⟩ := h
  have ha : d.cfg.auth = true := by
    obtain ⟨t, he, htw⟩ := Hd
    obtain ⟨tw, htwm, hen⟩ := wf_mem he hwm
    have htk : tw = .authLease := by
      have e := hen.kind
      rw [hk] at e
      clear htwm hen
      cases tw <;> simp only [typed.Workload.kindW, typed.Workload.kind] at e ⊢ <;>
        first | rfl | exact absurd e (by decide)
    subst htk
    have hauth : ∀ w ∈ t.workloads, w.needsAuth = true → t.cfg.auth = true := by
      grind [typed.Deployment.WellFormed]
    rw [he.2.2.1.2.2.2]; exact hauth _ htwm rfl
  rcases auth_class Hd ha with h5 | h6
  · exfalso
    have hm : W64 6 ∈ d.workloads.map (·.kind) := List.mem_map.2 ⟨w, hwm, hk⟩
    rw [h5] at hm
    simp at hm
    exact absurd hm (by decide)
  · exact h6

/-- **The lease-granting mode's ids** (`clusterAllocN`'s `hap`): with a `leaseExpiry` workload (a lease-granting
one) the members' ids are apart in 15 bits (`WellFormed`'s `grantsLeases` clause). -/
theorem lmOf_revocable_apart {d : Deployment} (Hd : d.WellFormed) :
    lmOf d = .revocable → leaseIdsApart d.ids := by
  intro hlm
  obtain ⟨t, he, hw⟩ := Hd
  have hap : (∃ w ∈ t.workloads, w.grantsLeases = true) → leaseIdsApart t.ids := by
    grind [typed.Deployment.WellFormed]
  have e : t.ids = d.ids := by simp only [typed.Deployment.ids, Deployment.ids, he.1, he.2.1]
  rw [← e]
  apply hap
  have h96 : d.hasKind (W64 9) = true ∨ d.hasKind (W64 6) = true := by
    unfold lmOf at hlm
    cases h : d.hasKind (W64 9)
    · cases h6 : d.hasKind (W64 6)
      · rw [h, h6] at hlm
        simp only [Bool.false_eq_true, ↓reduceIte] at hlm
        split at hlm <;> cases hlm
      · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨w, hwm, hk⟩ : ∃ w ∈ d.workloads, w.kind = W64 9 ∨ w.kind = W64 6 := by
    rcases h96 with h9 | h6
    · obtain ⟨w, hwm, hk⟩ := (d.hasKind_iff _).1 h9; exact ⟨w, hwm, Or.inl hk⟩
    · obtain ⟨w, hwm, hk⟩ := (d.hasKind_iff _).1 h6; exact ⟨w, hwm, Or.inr hk⟩
  obtain ⟨tw, htw, hen⟩ := wf_mem he hwm
  refine ⟨tw, htw, ?_⟩
  have := hen.kind
  clear htw hen
  rcases hk with hk | hk <;> rw [hk] at this <;>
  cases tw <;> simp only [typed.Workload.kindW, typed.Workload.kind] at this <;>
    first | rfl | exact absurd this (by decide)

/-- **The non-expiring mode's premise** (`member_boot_dist`'s `Hlm`): with a `leaseCatchup` workload, which needs
that no lease expires, `EtcdEnv`'s `noExpiry` gives it. -/
theorem lmOf_mono_noExpiry {d : Deployment}
    (H : (∃ w ∈ d.workloads, w.needsNoExpiry = true) → lease.leasesNoExpiry) :
    lmOf d = .mono → lease.leasesNoExpiry := by
  intro hlm
  apply H
  have h8 : d.hasKind (W64 8) = true := by
    unfold lmOf at hlm
    split at hlm
    · cases hlm
    · split at hlm
      · cases hlm
      · split at hlm
        · assumption
        · cases hlm
  obtain ⟨w, hwm, hk⟩ := (d.hasKind_iff _).1 h8
  exact ⟨w, hwm, by simp [Workload.needsNoExpiry, hk]⟩

/-- With a `leaseExpiry` workload the lease mode is revocable. -/
theorem lmOf_expiry {d : Deployment} (h : ∃ w ∈ d.workloads, w.kind = W64 9) : lmOf d = .revocable := by
  unfold lmOf
  rw [if_pos ((d.hasKind_iff _).2 h)]

/-- **With a `leaseCatchup` workload the lease mode is `mono`** (`Compatible`: no `leaseExpiry` beside a workload
that needs no lease to expire). -/
theorem lmOf_catchup {d : Deployment} (Hd : d.WellFormed) (h : ∃ w ∈ d.workloads, w.kind = W64 8) :
    lmOf d = .mono := by
  obtain ⟨t, he, hw⟩ := Hd
  have hcomp : typed.Compatible t.workloads := by grind [typed.Deployment.WellFormed]
  have h9 : d.hasKind (W64 9) = false := by
    apply d.hasKind_false
    intro w9 hw9 e9
    obtain ⟨w8, hw8, e8⟩ := h
    obtain ⟨t9, ht9, hen9⟩ := wf_mem he hw9
    obtain ⟨t8, ht8, hen8⟩ := wf_mem he hw8
    have k9 := hen9.kind
    have k8 := hen8.kind
    rw [e9] at k9
    rw [e8] at k8
    have hx9 : t9 = .leaseExpiry := by
      clear hen9 ht9
      cases t9 <;> simp only [typed.Workload.kindW, typed.Workload.kind] at k9 <;>
        first | rfl | exact absurd k9 (by decide)
    have hx8 : t8 = .leaseCatchup := by
      clear hen8 ht8
      cases t8 <;> simp only [typed.Workload.kindW, typed.Workload.kind] at k8 <;>
        first | rfl | exact absurd k8 (by decide)
    subst hx9 hx8
    exact hcomp.2.2.2.1 ⟨ht9, _, ht8, rfl⟩
  have h6 : d.hasKind (W64 6) = false := by
    apply d.hasKind_false
    intro w6 hw6 e6
    obtain ⟨w8, hw8, e8⟩ := h
    have hm : W64 8 ∈ d.workloads.map (·.kind) := List.mem_map.2 ⟨w8, hw8, e8⟩
    rw [kinds_of_authLease ⟨t, he, hw⟩ ⟨w6, hw6, e6⟩] at hm
    simp at hm
    exact absurd hm (by decide)
  unfold lmOf
  rw [h9, h6, if_pos ((d.hasKind_iff _).2 h)]
  rfl

/-- **The `authLease` class's lease mode is revocable** (its workload revokes `Lu`). -/
theorem lmOf_authLease {d : Deployment} (h6 : d.workloads.map (·.kind) = [W64 6]) : lmOf d = .revocable := by
  have h9 : d.hasKind (W64 9) = false := by
    apply d.hasKind_false
    intro w hw e
    have hm : W64 9 ∈ d.workloads.map (·.kind) := List.mem_map.2 ⟨w, hw, e⟩
    rw [h6] at hm
    simp at hm
    exact absurd hm (by decide)
  have h6' : d.hasKind (W64 6) = true := by
    obtain ⟨w, hw, e⟩ := List.mem_map.1 (show W64 6 ∈ d.workloads.map (·.kind) by rw [h6]; simp)
    exact (d.hasKind_iff _).2 ⟨w, hw, e⟩
  unfold lmOf
  rw [h9, h6']
  rfl

/-- **With auth on and the lease mode revocable, no lease expires** (`member_boot_dist`'s `Hauth`): the class is
`[authLease]` (`[auth]`'s mode is `.none`), whose workload needs that no lease expires, which `EtcdEnv`'s
`noExpiry` gives. -/
theorem lmOf_auth_revocable {d : Deployment} (Hd : d.WellFormed)
    (H : (∃ w ∈ d.workloads, w.needsNoExpiry = true) → lease.leasesNoExpiry) :
    d.cfg.auth = true → lmOf d = .revocable → lease.leasesNoExpiry := by
  intro ha hlm
  rcases auth_class Hd ha with h | h
  · exfalso
    have hno : ∀ k : w64, k ≠ W64 5 → d.hasKind k = false := by
      intro k hk
      apply d.hasKind_false
      intro w hw e
      have hm : k ∈ d.workloads.map (·.kind) := List.mem_map.2 ⟨w, hw, e⟩
      rw [h] at hm
      simp at hm
      exact hk hm
    unfold lmOf at hlm
    rw [hno _ (by decide), hno _ (by decide), hno _ (by decide)] at hlm
    simp only [Bool.false_eq_true, ↓reduceIte] at hlm
    cases hlm
  · apply H
    obtain ⟨w, hw, e⟩ := List.mem_map.1 (show W64 6 ∈ d.workloads.map (·.kind) by rw [h]; simp)
    exact ⟨w, hw, by simp [Workload.needsNoExpiry, e]⟩

section compactor
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]

theorem retention_zero {d : Deployment} (h : sint.Z d.cfg.retention = 0) : d.cfg.retention = W64 0 := by
  first
    | (apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at h; rw [h]; try (first | rfl | decide); done)
    | word

/-- **The compactor's slot at `cmpOf d`** (`v3compactor.bootCfg`, `NewServer`'s premise): off at any setting;
revision mode at a retention `r ≥ 1` (`Supported`) with `1 ≤ r` or `r` itself; periodic mode at `0` (and never with
`compact`, review F5). -/
theorem cmpOf_bootCfg {d : Deployment} (Hd : d.WellFormed) :
    v3compactor.bootCfg d.cfg.compactorMode d.cfg.retention (cmpOf d).1 (cmpOf d).2 := by
  obtain ⟨t, he, hw⟩ := Hd
  have hc := he.2.2.1.1
  have hs' : t.cfg.Supported := by grind [typed.Deployment.WellFormed]
  have hF5 : typed.Workload.compact ∈ t.workloads → t.cfg.compactor.isPeriodic = false := by
    grind [typed.Deployment.WellFormed]
  have hs := hs'.1
  have hcw : d.hasKind (W64 3) = true → typed.Workload.compact ∈ t.workloads := by
    intro h3
    obtain ⟨w, hwm, hk⟩ := (d.hasKind_iff _).1 h3
    obtain ⟨tw, htw, hen⟩ := wf_mem he hwm
    have := hen.kind
    rw [hk] at this
    clear hen
    cases tw <;> simp only [typed.Workload.kindW, typed.Workload.kind] at this <;>
      first | exact htw | exact absurd this (by decide)
  unfold cmpOf
  rcases hcm : t.cfg.compactor with _ | r | p
  · rw [hcm] at hc
    exact v3compactor.bootCfg_off _ _ _ _ (retention_zero hc)
  · rw [hcm] at hc hs
    obtain ⟨hm, hr, -⟩ := hc
    obtain ⟨h1, -⟩ := hs
    rw [hm]
    split
    · exact v3compactor.bootCfg_revision _ _ (by omega) (by omega)
    · rw [if_neg (by omega), if_pos rfl]
      exact v3compactor.bootCfg_revision _ _ (by omega) (by omega)
  · rw [hcm] at hc hs hF5
    obtain ⟨hm, hr, -⟩ := hc
    obtain ⟨h1, -⟩ := hs
    rw [hm]
    split
    · next h3 => exact absurd (hF5 (hcw h3)) (by simp [typed.Compactor.isPeriodic])
    · rw [if_neg (by omega), if_neg (by decide)]
      exact v3compactor.bootCfg_periodic _ _ (by omega) rfl

/-- **With auth on, no compaction** (`clusterAllocN`'s `Hon`): the compactor is off and no workload compacts. -/
theorem cmpOf_auth {d : Deployment} (Hd : d.WellFormed) :
    d.cfg.auth = true → (cmpOf d).1 = false ∧ (cmpOf d).2 = 0 := by
  intro ha
  have h3 : d.hasKind (W64 3) = false := by
    apply d.hasKind_false
    intro w hw e
    have hm : W64 3 ∈ d.workloads.map (·.kind) := List.mem_map.2 ⟨w, hw, e⟩
    rcases auth_class Hd ha with h | h <;> rw [h] at hm <;> simp at hm <;> exact absurd hm (by decide)
  unfold cmpOf
  rw [h3, if_neg (by decide), if_pos (Hd.authCompactorOff ha)]
  exact ⟨rfl, rfl⟩

end compactor

/-- With a `compact` workload, compaction mode at retention `1` (F5 §26.4). -/
theorem cmpOf_compact {d : Deployment} (h : ∃ w ∈ d.workloads, w.kind = W64 3) : cmpOf d = (true, 1) := by
  unfold cmpOf
  rw [if_pos ((d.hasKind_iff _).2 h)]

/-- **The sole writer's bounds** (S; `kvOnly_shape`'s for kv, `RunWatch`/`RunCache`'s for watch and cache): its
client machines `ns` are its `clients`, below `2 ^ 31`, and `len(ns) * ops` below `2 ^ 62` (`2 ^ 60` for kv). -/
def SoleBounds (s : Workload) (ns : List GoString) : Prop :=
  ns.length < 2 ^ 31 ∧ (ns.length : Int) = sint.Z s.clients ∧ 0 ≤ sint.Z s.ops ∧
    (ns.length : Int) * sint.Z s.ops < 2 ^ 62 ∧ (s.kind = W64 0 → (ns.length : Int) * sint.Z s.ops < 2 ^ 60)

/-- **The classes of a well-formed deployment with auth off** (§27.1, D1; §27.2's `classOf_spec`), with the
pure facts the start needs:
- E: no workload, no client machine;
- Ls: lease workloads only (kinds 7-9), at least one, no client machine;
- S: the sole writer `s` at index `j` (kind 0-2) with its client machines `ns` (`SoleBounds`), every other
  workload a `leaseRead` (kind 7) with no client machine, the lease mode `none`;
- P: at least one of `compact`/`putget`/`durable` (kinds 3, 4, 10), the others of these or `leaseRead`, no client
  machine, the lease mode `none`. -/
theorem class_authOff {d : Deployment} (Hd : d.WellFormed) (ha : d.cfg.auth = false) :
    (d.workloads = [] ∧ d.nodes = []) ∨
    (d.workloads ≠ [] ∧ (∀ w ∈ d.workloads, w.kind = W64 7 ∨ w.kind = W64 8 ∨ w.kind = W64 9) ∧
      ∀ ns ∈ d.nodes, ns = []) ∨
    (∃ (j : Nat) (s : Workload) (ns : List GoString), d.workloads[j]? = some s ∧ d.nodes[j]? = some ns ∧
      (s.kind = W64 0 ∨ s.kind = W64 1 ∨ s.kind = W64 2) ∧
      (∀ (j' : Nat) (w' : Workload), d.workloads[j']? = some w' → j' ≠ j → w'.kind = W64 7) ∧
      (∀ (j' : Nat) (ns' : List GoString), d.nodes[j']? = some ns' → j' ≠ j → ns' = []) ∧
      SoleBounds s ns ∧ lmOf d = .none) ∨
    ((∃ w ∈ d.workloads, w.kind = W64 3 ∨ w.kind = W64 4 ∨ w.kind = W64 10) ∧
      (∀ w ∈ d.workloads, w.kind = W64 3 ∨ w.kind = W64 4 ∨ w.kind = W64 7 ∨ w.kind = W64 10) ∧
      (∀ ns ∈ d.nodes, ns = []) ∧ lmOf d = .none) := by
  have Hd' := Hd
  obtain ⟨t, he, hw⟩ := Hd'
  have ha' : t.cfg.auth = false := by rw [← he.2.2.1.2.2.2]; exact ha
  have hws := he.2.2.2.1
  have hnn : t.nodes = d.nodes := he.2.2.2.2
  have hbnd : ∀ tw ∈ t.workloads, tw.BoundsOk := by grind [typed.Deployment.WellFormed]
  -- the node lists, at every index: the workload's client machines
  have hnode : ∀ {j : Nat} {ns : List GoString}, d.nodes[j]? = some ns →
      ∃ tw w, t.workloads[j]? = some tw ∧ d.workloads[j]? = some w ∧ tw.Encodes w ∧
        ns.length = tw.nodeCount := by
    intro j ns hn
    rw [← hnn] at hn
    obtain ⟨tw, htw, hl⟩ := typed.node_at hw hn
    obtain ⟨w, hwj, hen⟩ := cls_forall₂_get_left hws htw
    exact ⟨tw, w, htw, hwj, hen, hl⟩
  -- a Go workload's kind is its typed one's
  have hkind : ∀ {w : Workload}, w ∈ d.workloads → ∃ tw ∈ t.workloads, w.kind = tw.kindW := by
    intro w hwm
    obtain ⟨tw, htw, hen⟩ := wf_mem he hwm
    exact ⟨tw, htw, hen.kind⟩
  rcases typed.class_typed hw ha' with h0 | ⟨hne, hls⟩ | ⟨j, s, hj, hsk, hoth⟩ | ⟨⟨w0, hw0, hk0⟩, hpk⟩
  · -- E
    left
    have hl : d.workloads.length = 0 := by rw [← hws.length_eq, h0]; rfl
    have hwe : d.workloads = [] := List.eq_nil_of_length_eq_zero hl
    have hl' : t.nodes.length = t.workloads.length := by grind [typed.Deployment.WellFormed]
    refine ⟨hwe, List.eq_nil_of_length_eq_zero ?_⟩
    rw [← hnn, hl', h0]; rfl
  · -- Ls
    refine Or.inr (Or.inl ⟨fun e => hne ?_, fun w hwm => ?_, fun ns hns => ?_⟩)
    · have hl : t.workloads.length = 0 := by rw [hws.length_eq, e]; rfl
      exact List.eq_nil_of_length_eq_zero hl
    · obtain ⟨tw, htw, e⟩ := hkind hwm
      rw [e]
      rcases hls tw htw with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hns
      obtain ⟨tw, w, htw, -, -, hl⟩ := hnode hj
      have : tw.nodeCount = 0 := by
        rcases hls tw (List.mem_of_getElem? htw) with rfl | rfl | rfl <;> rfl
      exact List.eq_nil_of_length_eq_zero (by rw [hl, this])
  · -- S
    obtain ⟨gs, hgs, hen⟩ := cls_forall₂_get_left hws hj
    have hjn : j < d.nodes.length := by
      rw [← hnn]
      have hl : t.nodes.length = t.workloads.length := by grind [typed.Deployment.WellFormed]
      rw [hl]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨ns, hns⟩ : ∃ ns, d.nodes[j]? = some ns := ⟨_, List.getElem?_eq_getElem hjn⟩
    obtain ⟨tw', -, htw', -, -, hl⟩ := hnode hns
    rw [hj] at htw'
    cases htw'
    have hb := hbnd s (List.mem_of_getElem? hj)
    -- the other workloads are `leaseRead`s
    have hoth' : ∀ (j' : Nat) (w' : Workload), d.workloads[j']? = some w' → j' ≠ j → w'.kind = W64 7 := by
      intro j' w' hj' hne
      obtain ⟨tw, htw, hen'⟩ := cls_forall₂_get hws hj'
      rw [hen'.kind, hoth j' tw htw hne]
      rfl
    refine Or.inr (Or.inr (Or.inl ⟨j, gs, ns, hgs, hns, ?_, hoth', ?_, ?_, ?_⟩))
    · rw [hen.kind]
      rcases hsk with ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · intro j' ns' hn' hne
      obtain ⟨tw, w, htw, -, -, hl'⟩ := hnode hn'
      rw [hoth j' tw htw hne] at hl'
      exact List.eq_nil_of_length_eq_zero hl'
    · rcases hsk with ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ <;>
        obtain ⟨hk, hc, ho⟩ := hen <;>
        simp only [typed.Workload.BoundsOk] at hb <;>
        simp only [typed.Workload.nodeCount] at hl <;>
        refine ⟨by omega, by rw [hl, hc], by omega, ?_, ?_⟩
      · rw [hl, ho]
        have : ((c * o : Nat) : Int) < 2 ^ 60 := by exact_mod_cast hb.2
        have h62 : ((2 : Int) ^ 60) < 2 ^ 62 := by decide
        push_cast at this
        exact Int.lt_trans this h62
      · intro _
        rw [hl, ho]
        exact_mod_cast hb.2
      · rw [hl, ho]
        exact_mod_cast hb.2
      · intro h0
        rw [hk] at h0
        exact absurd h0 (by decide)
      · rw [hl, ho]
        exact_mod_cast hb.2
      · intro h0
        rw [hk] at h0
        exact absurd h0 (by decide)
    · apply lmOf_none
      intro w hwm
      obtain ⟨j', hj'⟩ := List.getElem?_of_mem hwm
      by_cases hjj : j' = j
      · subst hjj
        rw [hgs] at hj'
        cases hj'
        rw [hen.kind]
        rcases hsk with ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ | ⟨c, o, rfl⟩ <;>
          simp only [typed.Workload.kindW, typed.Workload.kind] <;> exact ⟨by decide, by decide, by decide⟩
      · rw [hoth' j' w hj' hjj]
        exact ⟨by decide, by decide, by decide⟩
  · -- P
    have hpk' : ∀ w ∈ d.workloads, w.kind = W64 3 ∨ w.kind = W64 4 ∨ w.kind = W64 7 ∨ w.kind = W64 10 := by
      intro w hwm
      obtain ⟨tw, htw, e⟩ := hkind hwm
      rw [e]
      rcases hpk tw htw with rfl | rfl | rfl | ⟨n, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    refine Or.inr (Or.inr (Or.inr ⟨?_, hpk', fun ns hns => ?_, ?_⟩))
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hw0
      obtain ⟨w, hwi, hen⟩ := cls_forall₂_get_left hws hi
      refine ⟨w, List.mem_of_getElem? hwi, ?_⟩
      rw [hen.kind]
      rcases hk0 with rfl | rfl | ⟨n, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hns
      obtain ⟨tw, w, htw, -, -, hl⟩ := hnode hj
      have : tw.nodeCount = 0 := by
        rcases hpk tw (List.mem_of_getElem? htw) with rfl | rfl | rfl | ⟨n, rfl⟩ <;> rfl
      exact List.eq_nil_of_length_eq_zero (by rw [hl, this])
    · apply lmOf_none
      intro w hwm
      rcases hpk' w hwm with e | e | e | e <;> rw [e] <;> exact ⟨by decide, by decide, by decide⟩

/-- **At most eleven workloads** (their kinds are distinct, each below 11). -/
theorem workloads_length_le {d : Deployment} (Hd : d.WellFormed) : d.workloads.length ≤ 11 := by
  obtain ⟨t, he, hw⟩ := Hd
  have hcomp : typed.Compatible t.workloads := by grind [typed.Deployment.WellFormed]
  have hsub : t.workloads.map typed.Workload.kind ⊆ List.range 11 := by
    intro k hk
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hk
    cases w <;> simp [typed.Workload.kind]
  have := List.Nodup.length_le_of_subset hcomp.1 hsub
  rw [← he.2.2.2.1.length_eq]
  simpa using this

/-- The client machines are the node lists' addresses, in order. -/
theorem nodeList_length_eq {d : Deployment} (Hd : d.WellFormed) : d.nodeList.length = d.nodes.flatten.length := by
  have hl : d.nodes.length = d.workloads.length := by
    obtain ⟨t, he, hw⟩ := Hd
    have hl : t.nodes.length = t.workloads.length := by grind [typed.Deployment.WellFormed]
    rw [← he.2.2.2.2, hl, he.2.2.2.1.length_eq]
  unfold Deployment.nodeList
  exact cls_nodeList_length _ _ hl.symm

/-- **Fewer than `2 ^ 31` client machines** (auth off: only the sole writer's, `SoleBounds`; auth on: `[auth]`'s four
or `[authLease]`'s none). -/
theorem nodeList_length_lt {d : Deployment} (Hd : d.WellFormed) : d.nodeList.length < 2 ^ 31 := by
  rw [nodeList_length_eq Hd]
  cases ha : d.cfg.auth
  · rcases class_authOff Hd ha with ⟨-, hn0⟩ | ⟨-, -, hn0⟩ | ⟨j, s, ns, -, hns, -, -, hnoth, hsb, -⟩ |
        ⟨-, -, hn0, -⟩
    · rw [hn0]; decide
    · rw [List.flatten_eq_nil_iff.2 hn0]; decide
    · rw [cls_flatten_single d.nodes j ns hns hnoth]; exact hsb.1
    · rw [List.flatten_eq_nil_iff.2 hn0]; decide
  · obtain ⟨t, he, hw⟩ := Hd
    have ha' : t.cfg.auth = true := by rw [← he.2.2.1.2.2.2]; exact ha
    have hq1 : t.cfg.auth = true → ∃ w ∈ t.workloads, w.needsAuth = true := by
      grind [typed.Deployment.WellFormed]
    have hcomp : typed.Compatible t.workloads := by grind [typed.Deployment.WellFormed]
    obtain ⟨w, hwm, hwa⟩ := hq1 ha'
    have hal : w.alone = true := by
      revert hwa; cases w <;> simp [typed.Workload.needsAuth, typed.Workload.alone]
    have hl1 := hcomp.2.1 ⟨w, hwm, hal⟩
    have hl : t.nodes.length = t.workloads.length := by grind [typed.Deployment.WellFormed]
    obtain ⟨ns, hns⟩ := List.length_eq_one_iff.1 (hl.trans hl1)
    rw [← he.2.2.2.2, hns]
    obtain ⟨tw, htw, hlen⟩ := typed.node_at hw (show t.nodes[0]? = some ns by rw [hns]; rfl)
    obtain ⟨w', hw'⟩ := List.length_eq_one_iff.1 hl1
    have e1 : w' = tw := by rw [hw'] at htw; simpa using htw
    have e2 : w = w' := List.mem_singleton.1 (hw' ▸ hwm)
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hlen, ← e1, ← e2]
    clear hlen htw e1 e2 hw' hwm hal hl1
    revert hwa
    cases w <;> simp [typed.Workload.needsAuth, typed.Workload.nodeCount]

/-- **The shared KV's prefixes are apart** (P; `kvPfx_alloc`'s premise): `pg/`, `du/`, `cw/`, none a prefix of
another. -/
theorem pfxs_apart : ∀ (i j : Nat) (a b : GoString), i ≠ j →
    [go!"pg/", go!"du/", go!"cw/"][i]? = some a → [go!"pg/", go!"du/", go!"cw/"][j]? = some b → ¬ a <+: b := by
  intro i j a b hij ha hb
  match i, j, ha, hb with
  | 0, 0, _, _ => exact absurd rfl hij
  | 1, 1, _, _ => exact absurd rfl hij
  | 2, 2, _, _ => exact absurd rfl hij
  | 0, 1, ha, hb | 0, 2, ha, hb | 1, 0, ha, hb | 1, 2, ha, hb | 2, 0, ha, hb | 2, 1, ha, hb =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at ha hb
    subst ha hb
    decide
  | i + 3, _, ha, _ => simp at ha
  | _, j + 3, _, hb => simp at hb

end facts

end etcd_dist
end EtcdGrove
end Perennial

end
