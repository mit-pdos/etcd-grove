/-
The pure invariants of reconfiguration (2026-10-14, reconfiguration stage B3), kept by every
rule of `StepR` (`StepR.lean`): I1, I3 and the configuration invariant of
`notes/reconfiguration-safety.md` (section 3), with what they rest on. No ghost state.

* `ConfI1 l c` (I1): of two conf-change entries of `l`, the first is at a position below `c`
  (its log index at most `c`): with `c` the commit index, at most one conf entry is above it.
* `ConfI3 l pci a` (I3, a leader's): every conf entry is at a log index at most `pci`, and at
  most one is above `a` (`applied`).
* `RInv dec c0 r`: the node's full log is `FullOk`; `base ≤ commit ≤ lastIndex`;
  `applied ≤ cidx ≤ commit`; a pending snapshot is at the configuration index, a node with
  none has `base ≤ applied`, a leader has none; **the configuration is the fold of the first
  `cidx` entries of the full log** from `c0` (`cfgFold`, `CfgOverlap.lean`); I1 of the full
  log at the commit index; I3 at a leader (`pci`, `applied`); a candidate has no pending
  snapshot and no conf entry in `(applied, commit]` (the campaign guard, still holding: I2's
  premise).

One preservation lemma per rule (`RInv_<rule>`); the rules that move none of the fields the
invariant reads go through `RInv.frame`, the ones that only raise the commit index through
`RInv.commitUp`. Two rules need what their message knows, as hypotheses (the ghost state's to
supply, stage B4):

* `appAccept`: `AppKnow r m` -- the batch is well formed, and there is the sender's log `G` up
  to the batch's end (`G.drop index = entries`) with I1 at the message's commit index, agreeing
  with the receiver's full log by log matching (`LogMatchL`), and with the message's previous
  term. The sender's side: `ConfI1_appOk`, from the sender's I1 and `AppCommitEq`.
* `snapRestore`: the snapshot's configuration is the fold of its prefix -- what `Adm` says for
  the dynamic model (`AdmFold`).

**I1 needs the commit index** (a finding of this stage). Under `StepC`'s `AppOk`, which allows
an `MsgApp` to carry any commit index up to the sender's, I1 is false: a leader whose log has
conf entries at 5 and 7 and commit index 6 (I3 holds: 7 was proposed once 5 was applied) may
send entries 5..7 with commit index 0, and a follower at commit index 4 then holds two conf
entries above its commit index, from which it may campaign (the guard reads only `(applied,
commit]`). Go is not affected: `sendAppend` puts the leader's commit index in every `MsgApp`
(`AppCommitEq`, a premise of `StepR.sendApps`/`win`). The code's `ReplSends` (`AppOk`) will
need the equality when the code produces `StepR` witnesses.

`RInv_init`: a node starting from `c0` with a committed and applied bootstrap log `L` (both
setups of the review's section 2 that keep the argument: `c0` empty and `L` the bootstrap
conf entries, or `c0` the initial `ConfState` and `L = []`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.StepR

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open GMap go_etcd_io.raft.v3

section inv
variable [FfiSyntax]

theorem rUnat_eq (w : w64) : (uint.nat w : Int) = uint.Z w := by
  simp [uint.nat, uint.Z]

theorem rUnat_le {a b : w64} (h : uint.Z a ≤ uint.Z b) : uint.nat a ≤ uint.nat b := by
  have := rUnat_eq a; have := rUnat_eq b; omega

/-! ### Conf entries of a list -/

/-- I3: every conf-change entry is at a position below `pci`, at most one at or past `a`. -/
def ConfI3 (l : List raftpb.Entry) (pci a : Nat) : Prop :=
  (∀ (k : Nat) (e : raftpb.Entry), l[k]? = some e → IsConfEnt e → k < pci) ∧
  confCount (l.drop a) ≤ 1

theorem confCount_eq_zero {l : List raftpb.Entry}
    (h : ∀ (k : Nat) (e : raftpb.Entry), l[k]? = some e → ¬ IsConfEnt e) : confCount l = 0 := by
  unfold confCount
  rw [List.countP_eq_zero]
  intro a ha
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
  simpa using h k a hk

theorem confCount_le_one {l : List raftpb.Entry}
    (h : ∀ (k1 k2 : Nat) (e1 e2 : raftpb.Entry), k1 < k2 → l[k1]? = some e1 →
      l[k2]? = some e2 → IsConfEnt e1 → IsConfEnt e2 → False) : confCount l ≤ 1 := by
  induction l with
  | nil => simp [confCount]
  | cons e l ih =>
    rw [confCount_cons]
    by_cases hc : IsConfEnt e
    · rw [if_pos hc]
      have : confCount l = 0 := confCount_eq_zero (fun k e' hk hc' =>
        h 0 (k + 1) e e' (by omega) rfl (by simpa using hk) hc hc')
      omega
    · rw [if_neg hc]
      have := ih (fun k1 k2 e1 e2 hlt h1 h2 c1 c2 =>
        h (k1 + 1) (k2 + 1) e1 e2 (by omega) (by simpa using h1) (by simpa using h2) c1 c2)
      omega

/-- Dropping more entries leaves no more conf entries. -/
theorem confCount_drop_le (l : List raftpb.Entry) {a b : Nat} (h : a ≤ b) :
    confCount (l.drop b) ≤ confCount (l.drop a) := by
  have : l.drop a = (l.drop a).take (b - a) ++ l.drop b := by
    have h2 := List.take_append_drop (b - a) (l.drop a)
    rw [List.drop_drop, Nat.add_sub_cancel' h] at h2
    exact h2.symm
  rw [this, confCount_append]; omega

/-- No conf entry at or past `a`. -/
theorem confCount_drop_zero {l : List raftpb.Entry} {a : Nat}
    (h : ∀ (k : Nat) (e : raftpb.Entry), l[k]? = some e → IsConfEnt e → k < a) :
    confCount (l.drop a) = 0 :=
  confCount_eq_zero fun k e hk hc => by
    rw [List.getElem?_drop] at hk
    have := h _ e hk hc
    omega

/-- The stamped entries have the conf entries of the batch. -/
theorem confCount_mapIdx {l : List raftpb.Entry} {f : Nat → raftpb.Entry → raftpb.Entry}
    (hf : ∀ k e, (f k e).Type' = e.Type') : confCount (l.mapIdx f) = confCount l := by
  induction l generalizing f with
  | nil => rfl
  | cons e l ih =>
    rw [List.mapIdx_cons, confCount_cons, confCount_cons, ih (fun k e => hf (k + 1) e)]
    have hi : IsConfEnt (f 0 e) ↔ IsConfEnt e := by unfold IsConfEnt; rw [hf]
    by_cases hc : IsConfEnt e
    · rw [if_pos (hi.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hi.1 h)), if_neg hc]

theorem isConfEnt_stamp (t li : w64) (k : Nat) (e : raftpb.Entry) :
    IsConfEnt (stamp t li k e) ↔ IsConfEnt e := Iff.rfl

theorem not_isConfEnt_zero : ¬ IsConfEnt (zero_val raftpb.Entry) := by
  have h : (zero_val raftpb.Entry).Type' = W32 0 := rfl
  unfold IsConfEnt; rw [h]
  intro hc; rcases hc with h1 | h2
  · revert h1; word
  · revert h2; word

/-! ### `NoConfIn` -/

theorem NoConfIn.mono {l : List raftpb.Entry} {lo hi lo' hi' : Nat} (h : NoConfIn l lo hi)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : NoConfIn l lo' hi' :=
  fun k e hk1 hk2 he => h k e (by omega) (by omega) he

theorem NoConfIn.confCount {l : List raftpb.Entry} {lo hi : Nat} (h : NoConfIn l lo hi) :
    confCount ((l.drop lo).take (hi - lo)) = 0 :=
  confCount_eq_zero fun k e hk => by
    rw [List.getElem?_take] at hk
    split at hk
    · rw [List.getElem?_drop] at hk
      exact h _ e (by omega) (by omega) hk
    · cases hk

/-- With no conf entry in `[lo, hi)`, the fold up to `hi` is the fold up to `lo`. -/
theorem cfgFold_noConf (dec : CCDec) (c0 : CCState) {l : List raftpb.Entry} {lo hi : Nat}
    {cs : CCState} (h : NoConfIn l lo hi) (hlh : lo ≤ hi) (hf : cfgFold dec c0 (l.take lo) = some cs) :
    cfgFold dec c0 (l.take hi) = some cs := by
  have hsplit : l.take hi = l.take lo ++ (l.drop lo).take (hi - lo) := by
    have h := List.take_add (l := l) (i := lo) (j := hi - lo)
    rwa [Nat.add_sub_cancel' hlh] at h
  rw [hsplit, cfgFold_append, hf, Option.bind_some, cfgFoldFrom_zero _ _ _ _ h.confCount]

/-! ### I1 and I3 -/

theorem ConfI1.mono {l : List raftpb.Entry} {c c' : Nat} (h : ConfI1 l c) (hc : c ≤ c') :
    ConfI1 l c' :=
  fun k1 k2 e1 e2 hlt h1 h2 c1 c2 => Nat.lt_of_lt_of_le (h k1 k2 e1 e2 hlt h1 h2 c1 c2) hc

/-- Below the end of the list is free. -/
theorem ConfI1.min_length {l : List raftpb.Entry} {c : Nat} (h : ConfI1 l c) :
    ConfI1 l (min c l.length) := by
  intro k1 k2 e1 e2 hlt h1 h2 c1 c2
  have := h k1 k2 e1 e2 hlt h1 h2 c1 c2
  have := (List.getElem?_eq_some_iff.mp h2).1
  omega

theorem ConfI1.prefix {l1 l2 : List raftpb.Entry} {c : Nat} (h : ConfI1 (l1 ++ l2) c) :
    ConfI1 l1 c := by
  intro k1 k2 e1 e2 hlt h1 h2 c1 c2
  have hk2 := (List.getElem?_eq_some_iff.mp h2).1
  exact h k1 k2 e1 e2 hlt (by rw [List.getElem?_append_left (by omega)]; exact h1)
    (by rw [List.getElem?_append_left hk2]; exact h2) c1 c2

theorem ConfI1.append_nonconf {l x : List raftpb.Entry} {c : Nat} (h : ConfI1 l c)
    (hx : ∀ e ∈ x, ¬ IsConfEnt e) : ConfI1 (l ++ x) c := by
  intro k1 k2 e1 e2 hlt h1 h2 c1 c2
  by_cases hk2 : k2 < l.length
  · exact h k1 k2 e1 e2 hlt (by rw [List.getElem?_append_left (by omega)] at h1; exact h1)
      (by rw [List.getElem?_append_left hk2] at h2; exact h2) c1 c2
  · rw [List.getElem?_append_right (by omega)] at h2
    exact absurd c2 (hx e2 (List.mem_of_getElem? h2))

/-- Every list with one conf entry at most past `a` has I1 at any `c ≥ a`. -/
theorem ConfI1_of_drop {l : List raftpb.Entry} {a c : Nat} (h : confCount (l.drop a) ≤ 1)
    (hac : a ≤ c) : ConfI1 l c := by
  intro k1 k2 e1 e2 hlt h1 h2 c1 c2
  apply Classical.byContradiction
  intro hk
  have := two_le_confCount (l := l.drop a) (k1 := k1 - a) (k2 := k2 - a) (by omega)
    (by rw [List.getElem?_drop, Nat.add_sub_cancel' (by omega)]; exact h1)
    (by rw [List.getElem?_drop, Nat.add_sub_cancel' (by omega)]; exact h2) c1 c2
  omega

/-- I1 and no conf entry in `[a, c)`: at most one past `a`. -/
theorem ConfI1.confCount_drop {l : List raftpb.Entry} {a c : Nat} (h : ConfI1 l c)
    (hn : NoConfIn l a c) : confCount (l.drop a) ≤ 1 := by
  apply confCount_le_one
  intro k1 k2 e1 e2 hlt h1 h2 c1 c2
  rw [List.getElem?_drop] at h1 h2
  have := h (a + k1) (a + k2) e1 e2 (by omega) h1 h2 c1 c2
  exact hn (a + k1) e1 (by omega) this h1 c1

/-! ### The invariant -/

/-- The pure invariant of a node (see the file header). -/
structure RInv (dec : CCDec) (c0 : CCState) (r : RState) : Prop where
  full : FullOk r.p.base r.fp
  base_commit : uint.Z r.p.base.index' ≤ uint.Z r.p.commit
  commit_last : uint.Z r.p.commit ≤ plogLastIndexZ r.p.base r.p.log
  applied_cidx : uint.nat r.applied ≤ r.cidx
  cidx_commit : r.cidx ≤ uint.nat r.p.commit
  snap_base : r.snap = true → r.cidx = uint.nat r.p.base.index'
  base_applied : r.snap = false → uint.Z r.p.base.index' ≤ uint.Z r.applied
  lead_snap : r.p.role = .leader → r.snap = false
  cfg : cfgFold dec c0 (r.full.take r.cidx) = some r.cfg
  i1 : ConfI1 r.full (uint.nat r.p.commit)
  i3 : r.p.role = .leader → ConfI3 r.full (uint.nat r.pci) (uint.nat r.applied)
  cand : r.p.role = .candidate →
    r.snap = false ∧ NoConfIn r.full (uint.nat r.applied) (uint.nat r.p.commit)

theorem RInv.full_length {dec : CCDec} {c0 : CCState} {r : RState} (H : RInv dec c0 r) :
    (r.full.length : Int) = plogLastIndexZ r.p.base r.p.log := by
  unfold RState.full plogLastIndexZ
  rw [List.length_append]; push_cast; rw [H.full.1]

/-- The configuration is a reachable one: `CfgOk` from the initial configuration's. -/
theorem RInv.cfgOk {dec : CCDec} {c0 : CCState} {r : RState} (H : RInv dec c0 r)
    (h0 : CfgOk c0) : CfgOk r.cfg :=
  cfgFold_ok H.cfg h0

/-- A leader's I1 comes from its I3. -/
theorem RInv.i1_of_i3 {dec : CCDec} {c0 : CCState} {r : RState} (H : RInv dec c0 r)
    (hl : r.p.role = .leader) : ConfI1 r.full (uint.nat r.p.commit) :=
  ConfI1_of_drop (H.i3 hl).2 (Nat.le_trans H.applied_cidx H.cidx_commit)

/-- A rule that moves none of the fields the invariant reads, and keeps the role (with
`pci`) or makes a follower. -/
theorem RInv.frame {dec : CCDec} {c0 : CCState} {r r' : RState} (H : RInv dec c0 r)
    (hfp : r'.fp = r.fp) (hb : r'.p.base = r.p.base) (hl : r'.p.log = r.p.log)
    (hc : r'.p.commit = r.p.commit) (ha : r'.applied = r.applied) (hs : r'.snap = r.snap)
    (hci : r'.cidx = r.cidx) (hcf : r'.cfg = r.cfg)
    (hrole : r'.p.role = .follower ∨ (r'.p.role = r.p.role ∧ r'.pci = r.pci)) :
    RInv dec c0 r' := by
  have hfull : r'.full = r.full := by unfold RState.full; rw [hfp, hl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hfp]; exact H.full
  · rw [hb, hc]; exact H.base_commit
  · rw [hb, hl, hc]; exact H.commit_last
  · rw [ha, hci]; exact H.applied_cidx
  · rw [hci, hc]; exact H.cidx_commit
  · rw [hs, hci, hb]; exact H.snap_base
  · rw [hs, hb, ha]; exact H.base_applied
  · intro h
    rcases hrole with hf | ⟨hr, _⟩
    · rw [hf] at h; cases h
    · rw [hs]; exact H.lead_snap (hr ▸ h)
  · rw [hfull, hci, hcf]; exact H.cfg
  · rw [hfull, hc]; exact H.i1
  · intro h
    rcases hrole with hf | ⟨hr, hp⟩
    · rw [hf] at h; cases h
    · rw [hfull, hp, ha]; exact H.i3 (hr ▸ h)
  · intro h
    rcases hrole with hf | ⟨hr, _⟩
    · rw [hf] at h; cases h
    · rw [hfull, hs, ha, hc]; exact H.cand (hr ▸ h)

/-- A rule that only raises the commit index (within the log), keeping a leader's role and
`pci` or making a follower. -/
theorem RInv.commitUp {dec : CCDec} {c0 : CCState} {r r' : RState} (H : RInv dec c0 r)
    (hfp : r'.fp = r.fp) (hb : r'.p.base = r.p.base) (hl : r'.p.log = r.p.log)
    (hc : uint.Z r.p.commit ≤ uint.Z r'.p.commit)
    (hcl : uint.Z r'.p.commit ≤ plogLastIndexZ r'.p.base r'.p.log)
    (ha : r'.applied = r.applied) (hs : r'.snap = r.snap)
    (hci : r'.cidx = r.cidx) (hcf : r'.cfg = r.cfg)
    (hrole : r'.p.role = .follower ∨
      (r'.p.role = .leader ∧ r.p.role = .leader ∧ r'.pci = r.pci)) :
    RInv dec c0 r' := by
  have hfull : r'.full = r.full := by unfold RState.full; rw [hfp, hl]
  have hcn := rUnat_le hc
  refine ⟨?_, ?_, hcl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hfp]; exact H.full
  · rw [hb]; exact Int.le_trans H.base_commit hc
  · rw [ha, hci]; exact H.applied_cidx
  · rw [hci]; exact Nat.le_trans H.cidx_commit hcn
  · rw [hs, hci, hb]; exact H.snap_base
  · rw [hs, hb, ha]; exact H.base_applied
  · intro h
    rcases hrole with hf | ⟨_, hr, _⟩
    · rw [hf] at h; cases h
    · rw [hs]; exact H.lead_snap hr
  · rw [hfull, hci, hcf]; exact H.cfg
  · rw [hfull]; exact H.i1.mono hcn
  · intro h
    rcases hrole with hf | ⟨_, hr, hp⟩
    · rw [hf] at h; cases h
    · rw [hfull, hp, ha]; exact H.i3 hr
  · intro h
    rcases hrole with hf | ⟨hl', _, _⟩
    · rw [hf] at h; cases h
    · rw [hl'] at h; cases h

/-- A node starting from `c0` with the committed and applied log `L` (see the file header). -/
theorem RInv_init (dec : CCDec) (c0 : CCState) (r : RState) (L : List raftpb.Entry)
    (hfp : r.fp = []) (hb : r.p.base = base0) (hl : r.p.log = L)
    (hL : (L.length : Int) < 2 ^ 64)
    (hc : uint.Z r.p.commit = L.length) (ha : r.applied = r.p.commit) (hci : r.cidx = L.length)
    (hs : r.snap = false) (hrole : r.p.role = .follower)
    (hcfg : cfgFold dec c0 L = some r.cfg) : RInv dec c0 r := by
  have hfull : r.full = L := by unfold RState.full; rw [hfp, hl, List.nil_append]
  have hcn : uint.nat r.p.commit = L.length := by have := rUnat_eq r.p.commit; omega
  have h0 := base0_index
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hfp]; exact FullOk_base0
  · rw [hb, h0, hc]; omega
  · rw [hb, hl, hc]; unfold plogLastIndexZ; rw [h0]; omega
  · rw [ha, hci, hcn]; exact Nat.le_refl _
  · rw [hci, hcn]; exact Nat.le_refl _
  · rw [hs]; intro h; cases h
  · intro _; rw [hb, h0, ha, hc]; omega
  · rw [hrole]; intro h; cases h
  · rw [hfull, hci, List.take_length]; exact hcfg
  · rw [hfull, hcn]
    intro k1 k2 e1 e2 hlt _ h2 _ _
    have := (List.getElem?_eq_some_iff.mp h2).1
    omega
  · rw [hrole]; intro h; cases h
  · rw [hrole]; intro h; cases h

/-! ### `stepLeader`'s conf-change loop -/

/-- What the loop keeps of its accumulator: `pendingConfIndex` only grows; every accepted conf
entry is below it; at most one is accepted, and only when `pendingConfIndex ≤ applied`, after
which it is past `applied`. -/
def PCInv (applied li pci : w64) (acc : List raftpb.Entry × w64) : Prop :=
  uint.Z pci ≤ uint.Z acc.2 ∧
  (∀ (i : Nat) (e : raftpb.Entry), acc.1[i]? = some e → IsConfEnt e →
    uint.Z li + (i : Int) + 1 ≤ uint.Z acc.2) ∧
  confCount acc.1 ≤ 1 ∧
  (confCount acc.1 = 0 → acc.2 = pci) ∧
  (0 < confCount acc.1 → uint.Z pci ≤ uint.Z applied ∧ uint.Z applied < uint.Z acc.2)

/-- Appending an entry that is no conf change keeps `PCInv`. -/
theorem PCInv.snoc_nonconf {applied li pci : w64} {acc : List raftpb.Entry × w64}
    {x : raftpb.Entry} (h : PCInv applied li pci acc) (hx : ¬ IsConfEnt x) :
    PCInv applied li pci (acc.1 ++ [x], acc.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : confCount (acc.1 ++ [x]) = confCount acc.1 := by
    rw [confCount_append, confCount_cons, if_neg hx]; rfl
  refine ⟨h1, ?_, by simp only; rw [hc]; exact h3, by simp only; rw [hc]; exact h4,
    by simp only; rw [hc]; exact h5⟩
  intro i e he hce
  simp only at he
  by_cases hi : i < acc.1.length
  · rw [List.getElem?_append_left hi] at he; exact h2 i e he hce
  · rw [List.getElem?_append_right (by omega)] at he
    have : i - acc.1.length = 0 := by
      have := (List.getElem?_eq_some_iff.mp he).1; simp at this; omega
    rw [this] at he; simp at he; subst he; exact absurd hce hx

theorem propConfStep_inv (joint : Bool) {applied li pci : w64} {acc : List raftpb.Entry × w64}
    {x : raftpb.Entry × Option CCMsg} (h : PCInv applied li pci acc)
    (hx : x.2.isSome = decide (IsConfEnt x.1)) (hal : uint.Z applied ≤ uint.Z li)
    (hb : uint.Z li + (acc.1.length : Int) + 1 < 2 ^ 64) :
    PCInv applied li pci (propConfStep joint applied li acc x) := by
  rcases x with ⟨e, o⟩
  unfold propConfStep
  cases o with
  | none =>
    simp only at hx ⊢
    exact h.snoc_nonconf (fun hc => by simp [hc] at hx)
  | some c =>
    simp only at hx ⊢
    have hce : IsConfEnt e := by simpa using hx.symm
    split
    · exact h.snoc_nonconf not_isConfEnt_zero
    · rename_i hcond
      have hle : uint.Z acc.2 ≤ uint.Z applied := by
        apply Classical.byContradiction; intro hlt; exact hcond (Or.inl (by omega))
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have h0 : confCount acc.1 = 0 := by
        apply Classical.byContradiction; intro hne
        have := (h5 (by omega)).2; omega
      have hp := h4 h0
      have hnew : uint.Z (li + W64 (acc.1.length : Int) + W64 1) =
          uint.Z li + (acc.1.length : Int) + 1 := by
        have := uint_Z_nonneg li
        word
      have hc1 : confCount (acc.1 ++ [e]) = 1 := by
        rw [confCount_append, confCount_cons, if_pos hce, h0]; rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only; rw [hnew]; rw [hp] at hle; omega
      · intro i e' he' hc'
        simp only at he' ⊢
        rw [hnew]
        by_cases hi : i < acc.1.length
        · rw [List.getElem?_append_left hi] at he'
          have := confCount_pos he' hc'; omega
        · have := (List.getElem?_eq_some_iff.mp he').1
          simp at this; omega
      · show confCount (acc.1 ++ [e]) ≤ 1
        rw [hc1]; exact Nat.le_refl _
      · show confCount (acc.1 ++ [e]) = 0 → _
        rw [hc1]; intro h; cases h
      · intro _; simp only; rw [hnew]; rw [hp] at hle; exact ⟨hle, by omega⟩

theorem propConf_foldl_inv (joint : Bool) {applied li pci : w64}
    (hal : uint.Z applied ≤ uint.Z li) (xs : List (raftpb.Entry × Option CCMsg))
    (hx : ∀ x ∈ xs, x.2.isSome = decide (IsConfEnt x.1)) :
    ∀ acc : List raftpb.Entry × w64, PCInv applied li pci acc →
      uint.Z li + (acc.1.length : Int) + (xs.length : Int) < 2 ^ 64 →
      PCInv applied li pci (xs.foldl (propConfStep joint applied li) acc) := by
  induction xs with
  | nil => intro acc h _; exact h
  | cons x xs ih =>
    intro acc h hb
    simp only [List.foldl_cons]
    apply ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    · exact propConfStep_inv joint h (hx x List.mem_cons_self) hal
        (by simp only [List.length_cons] at hb; omega)
    · rw [propConfStep_length]; simp only [List.length_cons] at hb; push_cast; omega

theorem cctypes_iff {ents : List raftpb.Entry} {cs : List (Option CCMsg)}
    (H : CCTypesOk ents cs) : ∀ x ∈ ents.zip cs, x.2.isSome = decide (IsConfEnt x.1) := by
  induction H with
  | nil => intro x hx; simp at hx
  | cons Hh _ ih =>
    intro x hx
    simp only [List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Hh
    · exact ih x hx

/-- What the loop's result says (`PCInv` of the whole batch). -/
theorem propConf_inv (joint : Bool) {applied li pci : w64} {ents : List raftpb.Entry}
    {cs : List (Option CCMsg)} (hcs : CCTypesOk ents cs) (hal : uint.Z applied ≤ uint.Z li)
    (hnw : uint.Z li + (ents.length : Int) < 2 ^ 64) :
    PCInv applied li pci (propConf applied li pci ents cs joint) := by
  unfold propConf
  apply propConf_foldl_inv joint hal _ (cctypes_iff hcs)
  · refine ⟨Int.le_refl _, (fun i e he => by simp at he), (by simp [confCount]), fun _ => rfl,
      (fun h => by simp [confCount] at h)⟩
  · simp only [List.length_nil, List.length_zip]; push_cast; omega

/-! ### The rules -/

section rules
variable {dec : CCDec} {c0 : CCState}

/-- The unique frame for the rules that read no field of the invariant: the protocol state's
log, base, commit index and role (or a new follower), and every new field, unchanged. -/
theorem RInv_keep {r : RState} (p' : PState) (H : RInv dec c0 r) (hb : p'.base = r.p.base)
    (hl : p'.log = r.p.log) (hc : p'.commit = r.p.commit)
    (hrole : p'.role = .follower ∨ p'.role = r.p.role) : RInv dec c0 { r with p := p' } :=
  H.frame rfl hb hl hc rfl rfl rfl rfl (hrole.imp id fun h => ⟨h, rfl⟩)

theorem preadRespondAll_fields (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).base = s.base ∧ (preadRespondAll id s qs).log = s.log ∧
    (preadRespondAll id s qs).commit = s.commit ∧ (preadRespondAll id s qs).role = s.role := by
  obtain ⟨o, rd, h⟩ := preadRespondAll_eq id s qs
  rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem RInv_campaign {r : RState} (id : w64) (ms : List Msg) (H : RInv dec c0 r)
    (hs : r.snap = false) (hg : NoConfIn r.full (uint.nat r.applied) (uint.nat r.p.commit)) :
    RInv dec c0 { r with p := psendMsgs (pbecomeCandidate id r.p) ms, pci := W64 0 } :=
  ⟨H.full, H.base_commit, H.commit_last, H.applied_cidx, H.cidx_commit, H.snap_base,
    H.base_applied, (fun h => by cases h), H.cfg, H.i1, (fun h => by cases h), (fun _ => ⟨hs, hg⟩)⟩

/-- A new leader: `pci` at the last index before its empty entry; I3 from the campaign guard
(still holding at a candidate, `RInv.cand`) and I1. -/
theorem RInv_win {r : RState} (id : w64) (mt : GMap w64 w64) (ms : List Msg)
    (H : RInv dec c0 r) (hrole : r.p.role = .candidate)
    (hlast : plogLastIndexZ r.p.base r.p.log + 1 < 2 ^ 64) :
    RInv dec c0 { r with p := psendMsgs (pwinState id r.p mt) ms, pci := plastIndex r.p } := by
  have hlen := H.full_length
  have hcl := H.commit_last
  have hcn := rUnat_eq r.p.commit
  have hcidx : r.cidx ≤ r.full.length := by have := H.cidx_commit; omega
  have hx : ¬ IsConfEnt (pleaderEntry r.p) := not_isConfEnt_zero
  have hfull : RState.full { r with p := psendMsgs (pwinState id r.p mt) ms, pci := plastIndex r.p }
      = r.full ++ [pleaderEntry r.p] := by
    unfold RState.full; simp only [psendMsgs, pwinState, pappend, pbecomeLeader, List.append_assoc]
  have hpci : uint.nat (plastIndex r.p) = r.full.length := by
    have := rUnat_eq (plastIndex r.p)
    have : uint.Z (plastIndex r.p) = plogLastIndexZ r.p.base r.p.log := by
      unfold plastIndex; exact uint_Z_W64 _ (by have := plogLastIndexZ_nonneg r.p.base r.p.log; omega) (by omega)
    omega
  have ⟨hsn, hg⟩ := H.cand hrole
  refine ⟨H.full, H.base_commit, ?_, H.applied_cidx, H.cidx_commit, H.snap_base, H.base_applied,
    (fun _ => hsn), ?_, ?_, ?_, (fun h => by cases h)⟩
  · show uint.Z r.p.commit ≤ plogLastIndexZ r.p.base (r.p.log ++ [pleaderEntry r.p])
    unfold plogLastIndexZ at hcl ⊢; simp only [List.length_append, List.length_singleton]
    push_cast; omega
  · rw [hfull, List.take_append_of_le_length hcidx]; exact H.cfg
  · rw [hfull]; exact H.i1.append_nonconf (by simpa using hx)
  · intro _
    rw [hfull]
    refine ⟨?_, ?_⟩
    · intro k e he hce
      show k < uint.nat (plastIndex r.p)
      rw [hpci]
      by_cases hk : k < r.full.length
      · exact hk
      · rw [List.getElem?_append_right (by omega)] at he
        have := (List.getElem?_eq_some_iff.mp he).1
        simp at this
        rw [show k - r.full.length = 0 by omega] at he
        simp at he; subst he; exact absurd hce hx
    · have ha : uint.nat r.applied ≤ r.full.length := by have := H.applied_cidx; omega
      have hx0 : confCount [pleaderEntry r.p] = 0 := by
        rw [confCount_cons, if_neg hx]; rfl
      rw [List.drop_append_of_le_length ha, confCount_append, hx0]
      have := H.i1.confCount_drop hg
      omega

theorem RInv_propose {r : RState} (id : w64) (m : Msg) (cs : List (Option CCMsg))
    (ms : List Msg) (H : RInv dec c0 r) (hrole : r.p.role = .leader)
    (hcs : CCTypesOk m.entries cs)
    (hnw : plogLastIndexZ r.p.base r.p.log + (m.entries.length : Int) < 2 ^ 64) :
    RInv dec c0 { r with
      p := psendMsgs
        (pappend r.p ((propBatch r m.entries cs).1.mapIdx (stamp r.p.term (plastIndex r.p)))) ms
      pci := (propBatch r m.entries cs).2 } := by
  have hlen := H.full_length
  have hcl := H.commit_last
  have hcn := rUnat_eq r.p.commit
  have han := rUnat_eq r.applied
  have hcidx : r.cidx ≤ r.full.length := by have := H.cidx_commit; omega
  have hli : uint.Z (plastIndex r.p) = r.full.length := by
    unfold plastIndex; rw [hlen]
    exact uint_Z_W64 _ (by have := plogLastIndexZ_nonneg r.p.base r.p.log; omega) (by omega)
  have hal : uint.Z r.applied ≤ uint.Z (plastIndex r.p) := by
    have := H.applied_cidx; have := H.cidx_commit; omega
  have hlenb : m.entries.length = (propBatch r m.entries cs).1.length := by
    unfold propBatch; rw [propConf_length]; have := List.Forall₂.length_eq hcs; omega
  have hpc : PCInv r.applied (plastIndex r.p) r.pci (propBatch r m.entries cs) :=
    propConf_inv (CfgM.joint r.cfg.cfg) hcs hal (by rw [hli]; omega)
  generalize propBatch r m.entries cs = pb at hpc hlenb ⊢
  obtain ⟨p1, p2, p3, _, p5⟩ := hpc
  have hcB : confCount (pb.1.mapIdx (stamp r.p.term (plastIndex r.p))) = confCount pb.1 :=
    confCount_mapIdx (fun _ _ => rfl)
  have hfull : RState.full { r with
      p := psendMsgs (pappend r.p (pb.1.mapIdx (stamp r.p.term (plastIndex r.p)))) ms, pci := pb.2 }
      = r.full ++ pb.1.mapIdx (stamp r.p.term (plastIndex r.p)) := by
    unfold RState.full; simp only [psendMsgs, pappend, List.append_assoc]
  have hI3 := H.i3 hrole
  have hpn := rUnat_le p1
  have i3' : ConfI3 (r.full ++ pb.1.mapIdx (stamp r.p.term (plastIndex r.p))) (uint.nat pb.2)
      (uint.nat r.applied) := by
    refine ⟨?_, ?_⟩
    · intro k e he hce
      by_cases hk : k < r.full.length
      · rw [List.getElem?_append_left hk] at he
        exact Nat.lt_of_lt_of_le (hI3.1 k e he hce) hpn
      · rw [List.getElem?_append_right (by omega), List.getElem?_mapIdx] at he
        cases hb : pb.1[k - r.full.length]? with
        | none => rw [hb] at he; cases he
        | some e0 =>
          rw [hb] at he; simp only [Option.map_some, Option.some.injEq] at he; subst he
          have := p2 _ e0 hb ((isConfEnt_stamp _ _ _ _).1 hce)
          have := rUnat_eq pb.2
          omega
    · have ha : uint.nat r.applied ≤ r.full.length := by have := H.applied_cidx; omega
      rw [List.drop_append_of_le_length ha, confCount_append, hcB]
      by_cases h0 : confCount pb.1 = 0
      · rw [h0]; exact hI3.2
      · have hpa := (p5 (by omega))
        have hz : confCount (r.full.drop (uint.nat r.applied)) = 0 :=
          confCount_drop_zero fun k e he hce => by
            have := hI3.1 k e he hce; have := rUnat_eq r.pci; omega
        rw [hz, Nat.zero_add]; exact p3
  refine ⟨H.full, H.base_commit, ?_, H.applied_cidx, H.cidx_commit, H.snap_base, H.base_applied,
    (fun _ => H.lead_snap hrole), ?_, ?_, ?_, (fun h => by
      have h' : r.p.role = .candidate := h
      rw [hrole] at h'; cases h')⟩
  · show uint.Z r.p.commit ≤
      plogLastIndexZ r.p.base (r.p.log ++ pb.1.mapIdx (stamp r.p.term (plastIndex r.p)))
    unfold plogLastIndexZ at hcl ⊢; simp only [List.length_append]; push_cast; omega
  · rw [hfull, List.take_append_of_le_length hcidx]; exact H.cfg
  · rw [hfull]
    exact ConfI1_of_drop i3'.2 (show uint.nat r.applied ≤ uint.nat r.p.commit by
      have := H.applied_cidx; have := H.cidx_commit; omega)
  · intro _; rw [hfull]; exact i3'

theorem RInv_propDrop {r : RState} (m : Msg) (cs : List (Option CCMsg))
    (H : RInv dec c0 r) (hrole : r.p.role = .leader) (hcs : CCTypesOk m.entries cs)
    (hnw : plogLastIndexZ r.p.base r.p.log + (m.entries.length : Int) < 2 ^ 64) :
    RInv dec c0 { r with pci := (propBatch r m.entries cs).2 } := by
  have hlen := H.full_length
  have hli : uint.Z (plastIndex r.p) = r.full.length := by
    unfold plastIndex; rw [hlen]
    exact uint_Z_W64 _ (by have := plogLastIndexZ_nonneg r.p.base r.p.log; omega) (by omega)
  have hal : uint.Z r.applied ≤ uint.Z (plastIndex r.p) := by
    have := H.applied_cidx; have := H.cidx_commit; have := H.commit_last
    have := rUnat_eq r.applied; have := rUnat_eq r.p.commit; omega
  have p1 : uint.Z r.pci ≤ uint.Z (propBatch r m.entries cs).2 :=
    (propConf_inv (CfgM.joint r.cfg.cfg) (pci := r.pci) hcs hal (by rw [hli]; omega)).1
  have hpn := rUnat_le p1
  refine ⟨H.full, H.base_commit, H.commit_last, H.applied_cidx, H.cidx_commit, H.snap_base,
    H.base_applied, H.lead_snap, H.cfg, H.i1, ?_, H.cand⟩
  intro hl
  exact ⟨fun k e he hce => Nat.lt_of_lt_of_le ((H.i3 hl).1 k e he hce) hpn, (H.i3 hl).2⟩

theorem RInv_commit {r : RState} (n : w64) (H : RInv dec c0 r) (hrole : r.p.role = .leader)
    (hc : uint.Z r.p.commit < uint.Z n) (hn : uint.Z n ≤ plogLastIndexZ r.p.base r.p.log) :
    RInv dec c0 { r with p := { r.p with commit := n } } :=
  H.commitUp rfl rfl rfl (show uint.Z r.p.commit ≤ uint.Z n by omega) hn rfl rfl rfl rfl
    (Or.inr ⟨hrole, hrole, rfl⟩)

theorem RInv_heartbeat {r : RState} (src cm : w64) (ms : List Msg) (H : RInv dec c0 r)
    (hm : uint.Z cm ≤ plogLastIndexZ r.p.base r.p.log) :
    RInv dec c0 { r with p := (psendMsgs
      { padoptLeader r.p src with commit := plogCommitTo r.p.commit cm } ms) } := by
  have := H.commit_last
  refine H.commitUp rfl rfl rfl ?_ ?_ rfl rfl rfl rfl (Or.inl rfl)
  · show uint.Z r.p.commit ≤ uint.Z (plogCommitTo r.p.commit cm)
    unfold plogCommitTo; split <;> omega
  · show uint.Z (plogCommitTo r.p.commit cm) ≤ plogLastIndexZ r.p.base r.p.log
    unfold plogCommitTo; split <;> omega

theorem RInv_snapFastfwd {r : RState} (m : Msg) (ms : List Msg) (H : RInv dec c0 r)
    (hc : uint.Z r.p.commit < uint.Z m.index)
    (hm : PlogMatches r.p.base r.p.log (entryID.mk m.logterm m.index)) :
    RInv dec c0 { r with p := (psendMsgs { padoptLeader r.p m.src with commit := m.index } ms) } :=
  H.commitUp rfl rfl rfl (show uint.Z r.p.commit ≤ uint.Z m.index by omega)
    (plogTermAt_some_range _ _ _ _ hm).2 rfl rfl rfl rfl
    (Or.inl rfl)

/-- A snapshot restored: the node's full log is the snapshot's prefix, its configuration the
snapshot's, which is the prefix's fold (`hcfg`, A3: the message's knowledge). -/
theorem RInv_snapRestore {r : RState} (m : Msg) (fp' : List raftpb.Entry) (cs' : CCState)
    (ms : List Msg) (H : RInv dec c0 r) (hc : uint.Z r.p.commit < uint.Z m.index)
    (hfull : FullOk (entryID.mk m.logterm m.index) fp') (hcfg : cfgFold dec c0 fp' = some cs') :
    RInv dec c0 { r with
      p := (psendMsgs
        { padoptLeader r.p m.src with
            base := entryID.mk m.logterm m.index, log := [], commit := m.index } ms)
      snap := true
      cidx := uint.nat m.index
      cfg := cs'
      fp := fp' } := by
  have hl : (fp'.length : Int) = uint.Z m.index := hfull.1
  have hmn := rUnat_eq m.index
  have hfl : fp'.length = uint.nat m.index := by omega
  have hac : uint.nat r.applied ≤ uint.nat m.index := by
    have := H.applied_cidx; have := H.cidx_commit; have := rUnat_le (Int.le_of_lt hc); omega
  refine ⟨hfull, Int.le_refl _, ?_, hac, Nat.le_refl _, (fun _ => rfl), (fun h => by cases h),
    (fun h => by cases h), ?_, ?_, (fun h => by cases h), (fun h => by cases h)⟩
  · show uint.Z m.index ≤ plogLastIndexZ (entryID.mk m.logterm m.index) []
    unfold plogLastIndexZ; simp
  · show cfgFold dec c0 ((fp' ++ []).take (uint.nat m.index)) = some cs'
    rw [List.append_nil, List.take_of_length_le (by omega)]; exact hcfg
  · show ConfI1 (fp' ++ []) (uint.nat m.index)
    intro k1 k2 e1 e2 hlt _ h2 _ _
    have := (List.getElem?_eq_some_iff.mp h2).1
    simp at this; omega

theorem RInv_advance {r : RState} (a : w64) (H : RInv dec c0 r) (hs : r.snap = false)
    (h1 : uint.Z r.applied ≤ uint.Z a) (h2 : uint.Z a ≤ uint.Z r.p.commit)
    (hn : NoConfIn r.full r.cidx (uint.nat a)) :
    RInv dec c0 { r with applied := a, cidx := max r.cidx (uint.nat a) } := by
  have h1n := rUnat_le h1
  have h2n := rUnat_le h2
  refine ⟨H.full, H.base_commit, H.commit_last, Nat.le_max_right _ _,
    Nat.max_le.2 ⟨H.cidx_commit, h2n⟩, ?_,
    (fun _ => Int.le_trans (H.base_applied hs) h1), H.lead_snap, ?_, H.i1, ?_, ?_⟩
  · intro h
    have h' : r.snap = true := h
    rw [hs] at h'; cases h'
  · show cfgFold dec c0 (r.full.take (max r.cidx (uint.nat a))) = some r.cfg
    by_cases ha : uint.nat a ≤ r.cidx
    · rw [Nat.max_eq_left ha]; exact H.cfg
    · rw [Nat.max_eq_right (by omega)]
      exact cfgFold_noConf dec c0 hn (by omega) H.cfg
  · intro hl
    exact ⟨(H.i3 hl).1, Nat.le_trans (confCount_drop_le _ h1n) (H.i3 hl).2⟩
  · intro hc
    exact ⟨hs, (H.cand hc).2.mono h1n (Nat.le_refl _)⟩

theorem RInv_applySnap {r : RState} (H : RInv dec c0 r) (hs : r.snap = true) :
    RInv dec c0 { r with applied := r.p.base.index', snap := false } := by
  have hbn : uint.nat r.p.base.index' = r.cidx := (H.snap_base hs).symm
  refine ⟨H.full, H.base_commit, H.commit_last, Nat.le_of_eq hbn, H.cidx_commit,
    (fun h => by cases h), (fun _ => Int.le_refl _), (fun _ => rfl), H.cfg, H.i1, ?_, ?_⟩
  · intro hl; have := H.lead_snap hl; rw [hs] at this; cases this
  · intro hc; have := (H.cand hc).1; rw [hs] at this; cases this

/-- The configuration takes the next conf entry: the fold one entry further. -/
theorem RInv_applyConf {r : RState} (k : Nat) (e : raftpb.Entry) (op : CCOp) (cs' : CCState)
    (H : RInv dec c0 r) (hs : r.snap = false) (hk : r.cidx ≤ k) (hkc : k < uint.nat r.p.commit)
    (he : r.full[k]? = some e) (hc : IsConfEnt e) (hn : NoConfIn r.full r.cidx k)
    (hd : dec (r.full.take k) e = some op) (hst : ccStepB op r.cfg = some cs') :
    RInv dec c0 { r with cidx := k + 1, cfg := cs' } := by
  refine ⟨H.full, H.base_commit, H.commit_last,
    (show uint.nat r.applied ≤ k + 1 by have := H.applied_cidx; omega), hkc, ?_,
    H.base_applied, H.lead_snap, ?_, H.i1, H.i3, H.cand⟩
  · intro h
    have h' : r.snap = true := h
    rw [hs] at h'; cases h'
  show cfgFold dec c0 (r.full.take (k + 1)) = some cs'
  rw [List.take_add_one, he, Option.toList_some, cfgFold_snoc,
    cfgFold_noConf dec c0 hn hk H.cfg, Option.bind_some]
  unfold entStep; rw [if_pos hc, hd, Option.bind_some]; exact hst

end rules

/-! ### `MsgApp`: the receiver's and the sender's side of I1 -/

/-- Log matching between two full logs: where they have an entry of the same term, they agree
up to it. -/
def LogMatchL (F G : List raftpb.Entry) : Prop :=
  ∀ (k : Nat) (e e' : raftpb.Entry), F[k]? = some e → G[k]? = some e' → e.Term' = e'.Term' →
    F.take (k + 1) = G.take (k + 1)

/-- What an `MsgApp` tells its receiver `r` for I1 (the ghost state's to supply, B4): the batch
is well formed and does not wrap (`AppPayloadOk`), and there is a log `G` -- the sender's full
log up to the batch's end -- ending with the batch, with I1 at the message's commit index,
with the message's previous term at its index, and agreeing with the receiver's full log by
log matching. -/
def AppKnow (r : RState) (m : Msg) : Prop :=
  AppPayloadOk m ∧
  ∃ G : List raftpb.Entry, G.length = uint.nat m.index + m.entries.length ∧
    G.drop (uint.nat m.index) = m.entries ∧
    ConfI1 G (uint.nat m.commit) ∧
    (0 < uint.nat m.index → ∃ e, G[uint.nat m.index - 1]? = some e ∧ e.Term' = m.logterm) ∧
    LogMatchL r.full G

/-- The sender's side: an `MsgApp` that `AppOk` allows and that carries the sender's commit
index (`AppCommitEq`) has, for the sender's log up to the batch's end, I1 at its commit
index. (Without the equality this is false: the file header.) -/
theorem ConfI1_appOk {dec : CCDec} {c0 : CCState} {r : RState} {id : w64} {m : Msg}
    (H : RInv dec c0 r) (hm : AppOk id r.p m) (hc : m.commit = r.p.commit) :
    ConfI1 (r.full.take (uint.nat m.index) ++ m.entries) (uint.nat m.commit) := by
  obtain ⟨_, _, _, _, ht, _, _, hpre, _, hnw⟩ := hm
  obtain ⟨hb, _⟩ := plogTermAt_some_range _ _ _ _ ht
  have hfl : (r.fp.length : Int) = uint.Z r.p.base.index' := H.full.1
  have hin := rUnat_eq m.index
  obtain ⟨t, ht'⟩ := hpre
  have hnw1 : uint.Z (m.index + W64 1) = uint.Z m.index + 1 := by word
  unfold plogFrom at ht'
  rw [hnw1] at ht'
  have hsplit : r.full = (r.full.take (uint.nat m.index) ++ m.entries) ++ t := by
    have hk : uint.nat m.index = r.fp.length + (uint.Z m.index + 1 - uint.Z r.p.base.index' - 1).toNat := by
      omega
    unfold RState.full
    rw [hk, List.take_length_add_append, List.append_assoc, List.append_assoc, ht',
      List.take_append_drop]
  rw [hc]
  have := H.i1
  rw [hsplit] at this
  exact this.prefix

theorem plogFindConflict_first (b : entryID) (es : List raftpb.Entry) :
    ∀ (ents : List raftpb.Entry) (d : Nat) (e : raftpb.Entry), ents[d]? = some e →
    ¬ PlogMatches b es (entId e) →
    (∀ (j : Nat) (e' : raftpb.Entry), j < d → ents[j]? = some e' → PlogMatches b es (entId e')) →
    plogFindConflict b es ents = e.Index' := by
  intro ents
  induction ents with
  | nil => intro d e hd; simp at hd
  | cons a ents ih =>
    intro d e hd hnm hbef
    cases d with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      simp only [plogFindConflict, if_neg hnm]
    | succ d =>
      have ha := hbef 0 a (by omega) rfl
      simp only [plogFindConflict, if_pos ha]
      exact ih d e (by simpa using hd) hnm
        (fun j e' hj he' => hbef (j + 1) e' (by omega) (by simpa using he'))

/-- A full log's term at a positive index is its entry's. -/
theorem full_entry_of_term (F : List raftpb.Entry) (j t : w64)
    (h : plogTermAt base0 F j = some t) (hj : 0 < uint.Z j) :
    ∃ e, F[uint.nat j - 1]? = some e ∧ e.Term' = t := by
  have h0 := base0_index
  have hjn := rUnat_eq j
  unfold plogTermAt at h
  rw [h0] at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
  obtain ⟨e, he, het⟩ := h
  refine ⟨e, ?_, het⟩
  rw [show uint.nat j - 1 = (uint.Z j - 0 - 1).toNat by omega]
  exact he

section rules
variable {dec : CCDec} {c0 : CCState}

/-- An accepted `MsgApp`. With no conflict the log is unchanged and the commit index rises
within it. With a conflict (above the commit index), the new full log is the sender's `G`
(log matching below the conflict), whose I1 at the message's commit index gives I1 at the new
commit index; the prefix up to the configuration index is untouched. -/
theorem RInv_appAccept {r : RState} (m : Msg) (lastnewi : w64) (es' : List raftpb.Entry)
    (ms : List Msg) (H : RInv dec c0 r)
    (hma : plogMaybeAppend r.p.base r.p.log (entryID.mk m.logterm m.index) m.entries
      = some (lastnewi, es'))
    (hcf : plogFindConflict r.p.base r.p.log m.entries = W64 0 ∨
      uint.Z r.p.commit < uint.Z (plogFindConflict r.p.base r.p.log m.entries))
    (hk : AppKnow r m) :
    RInv dec c0 { r with p := (psendMsgs
      { padoptLeader r.p m.src with
          log := es',
          commit := plogCommitTo r.p.commit
                      (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) }
      ms) } := by
  obtain ⟨⟨hwf, hnw⟩, G, hGl, hGd, hGi, hGp, hLM⟩ := hk
  have hlast := plogMaybeAppend_last _ _ _ _ _ _ hwf hnw hma
  obtain ⟨hm, hln, hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ hwf hnw hma
  have ⟨hbm, _⟩ := plogTermAt_some_range _ _ _ _ hm
  simp only at hnw hln hbm
  generalize hXd : (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) = X
  have hx : uint.Z X = min (uint.Z m.commit) (uint.Z lastnewi) := by
    rw [← hXd]; split <;> omega
  have hc1 : uint.Z r.p.commit ≤ uint.Z (plogCommitTo r.p.commit X) := by
    unfold plogCommitTo; split <;> omega
  have hc2 : uint.Z X ≤ uint.Z (plogCommitTo r.p.commit X) := by
    unfold plogCommitTo; split <;> omega
  have hc3 : ∀ n : Int, uint.Z r.p.commit ≤ n → uint.Z X ≤ n →
      uint.Z (plogCommitTo r.p.commit X) ≤ n := by
    intro n h1 h2; unfold plogCommitTo; split <;> omega
  have hcl := H.commit_last
  rcases hcase with ⟨rfl, _⟩ | ⟨d, e, hd, hnm, hbef, hei, hend, rfl⟩
  · refine H.commitUp rfl rfl rfl hc1 ?_ rfl rfl rfl rfl (Or.inl rfl)
    show uint.Z (plogCommitTo r.p.commit X) ≤ plogLastIndexZ r.p.base r.p.log
    exact hc3 _ hcl (by omega)
  · simp only at hei hend
    -- the conflict is the first unmatched entry, above the commit index
    have hfc := plogFindConflict_first _ _ _ d e hd hnm hbef
    have hce : uint.Z r.p.commit < uint.Z e.Index' := by
      rcases hcf with h0 | h
      · rw [hfc] at h0; exact absurd h0 (batch_index_nz _ _ hwf d e hd)
      · rwa [hfc] at h
    have hbc := H.base_commit
    have hlen := H.full_length
    have hfl : (r.fp.length : Int) = uint.Z r.p.base.index' := H.full.1
    have hdlt := (List.getElem?_eq_some_iff.mp hd).1
    have hin := rUnat_eq m.index
    have hcn := rUnat_eq r.p.commit
    -- the new full log: the old one below the conflict, then the batch from it
    have hP : r.fp ++ (r.p.log.take (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat ++
        m.entries.drop d) = r.full.take (uint.nat m.index + d) ++ m.entries.drop d := by
      have hk : uint.nat m.index + d =
          r.fp.length + (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat := by omega
      unfold RState.full
      rw [hk, List.take_length_add_append, List.append_assoc]
    -- below the conflict the old full log is the sender's
    have hagree : r.full.take (uint.nat m.index + d) = G.take (uint.nat m.index + d) := by
      cases d with
      | zero =>
        by_cases h0 : uint.nat m.index = 0
        · rw [Nat.add_zero, h0]; rfl
        · obtain ⟨e1, he1, ht1⟩ := full_entry_of_term r.full m.index m.logterm
            (by unfold RState.full; rw [full_term_at _ _ _ _ H.full hbm]; exact hm) (by omega)
          obtain ⟨e2, he2, ht2⟩ := hGp (by omega)
          have := hLM _ e1 e2 he1 he2 (by rw [ht1, ht2])
          rwa [Nat.sub_add_cancel (by omega)] at this
      | succ d' =>
        obtain ⟨x, hx'⟩ : ∃ x, m.entries[d']? = some x :=
          ⟨m.entries[d'], List.getElem?_eq_getElem (by omega)⟩
        have hmx := hbef d' x (by omega) hx'
        have hxi := hwf d' x hx'
        unfold PlogMatches entId at hmx
        obtain ⟨hxb, _⟩ := plogTermAt_some_range _ _ _ _ hmx
        obtain ⟨e1, he1, ht1⟩ := full_entry_of_term r.full x.Index' x.Term'
          (by unfold RState.full; rw [full_term_at _ _ _ _ H.full hxb]; exact hmx)
            (by push_cast at hxi; have := uint_Z_nonneg m.index; omega)
        have hxn := rUnat_eq x.Index'
        have hG : G[uint.nat m.index + d']? = some x := by
          rw [← List.getElem?_drop, hGd]; exact hx'
        have hpos : uint.nat x.Index' - 1 = uint.nat m.index + d' := by
          push_cast at hxi; omega
        rw [hpos] at he1
        have := hLM _ e1 x he1 hG ht1
        rwa [show uint.nat m.index + d' + 1 = uint.nat m.index + (d' + 1) by omega] at this
    have hnewG : r.fp ++ (r.p.log.take (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat ++
        m.entries.drop d) = G := by
      rw [hP, hagree, List.take_add, hGd, List.append_assoc, List.take_append_drop,
        ← hGd, List.take_append_drop]
    have hlastZ : uint.Z lastnewi = (G.length : Int) := by
      rw [hln, hGl]; push_cast; omega
    have hcidx : r.cidx ≤ uint.nat m.index + d := by
      have := H.cidx_commit; push_cast at hei; omega
    have hPlen : uint.nat m.index + d ≤ r.full.length := by
      push_cast at hei; omega
    refine ⟨H.full, Int.le_trans hbc hc1, ?_, H.applied_cidx,
      Nat.le_trans H.cidx_commit (rUnat_le hc1), H.snap_base, H.base_applied,
      (fun h => by cases h), ?_, ?_, (fun h => by cases h), (fun h => by cases h)⟩
    · show uint.Z (plogCommitTo r.p.commit X)
          ≤ plogLastIndexZ r.p.base
            (r.p.log.take (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat ++ m.entries.drop d)
      have hl2 : plogLastIndexZ r.p.base
          (r.p.log.take (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat ++ m.entries.drop d)
          = (G.length : Int) := by
        rw [← hnewG]; unfold plogLastIndexZ
        simp only [List.length_append]; push_cast; omega
      rw [hl2]
      push_cast at hei
      exact hc3 _ (by omega) (by omega)
    · show cfgFold dec c0 ((r.fp ++ (r.p.log.take (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat
          ++ m.entries.drop d)).take r.cidx) = some r.cfg
      rw [hP, List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take,
        Nat.min_eq_left hcidx]
      exact H.cfg
    · show ConfI1 (r.fp ++ (r.p.log.take (uint.Z e.Index' - uint.Z r.p.base.index' - 1).toNat
          ++ m.entries.drop d)) (uint.nat (plogCommitTo r.p.commit X))
      rw [hnewG]
      apply hGi.min_length.mono
      have := rUnat_eq m.commit
      have := rUnat_eq (plogCommitTo r.p.commit X)
      omega

end rules

/-! ### Consequences: I2, and the conf entries past the configuration index -/

/-- I2: a candidate's configuration is the fold of its whole committed prefix (the guard: no
conf entry in `(applied, commit]`), and at most one conf entry is past its commit index (I1). -/
theorem RInv.cand_cfg {dec : CCDec} {c0 : CCState} {r : RState} (H : RInv dec c0 r)
    (hc : r.p.role = .candidate) :
    cfgFold dec c0 (r.full.take (uint.nat r.p.commit)) = some r.cfg ∧
    confCount (r.full.drop (uint.nat r.p.commit)) ≤ 1 :=
  ⟨cfgFold_noConf dec c0 ((H.cand hc).2.mono H.applied_cidx (Nat.le_refl _)) H.cidx_commit H.cfg,
    H.i1.confCount_drop (fun _ _ h1 h2 => absurd h2 (by omega))⟩

/-- A leader has at most one conf entry past its configuration index (I3, `applied ≤ cidx`). -/
theorem RInv.leader_drop_cidx {dec : CCDec} {c0 : CCState} {r : RState} (H : RInv dec c0 r)
    (hl : r.p.role = .leader) : confCount (r.full.drop r.cidx) ≤ 1 :=
  Nat.le_trans (confCount_drop_le _ H.applied_cidx) (H.i3 hl).2

/-! ### Every rule -/

/-- Every `StepR` derivation keeps `RInv`, given that each admissible configuration is its
prefix's fold (`AdmFold`, A3 for snapshots) and what each received `MsgApp` tells the state
that receives it (`AppKnow`, stated here for any state with the invariant, since the
derivation does not name it; the per-rule lemmas take it for the receiving state only). -/
theorem RInv_stepR {Adm : List raftpb.Entry → CCState → Prop} {dec : CCDec} {c0 : CCState}
    {id : w64} (hAdm : ∀ l cs, Adm l cs → cfgFold dec c0 l = some cs)
    {r : RState} {ms : List Msg} {r' : RState} (h : StepR Adm dec id r ms r')
    (hK : ∀ r1 m, m ∈ ms → m.ty = .app → RInv dec c0 r1 → AppKnow r1 m)
    (H : RInv dec c0 r) : RInv dec c0 r' := by
  induction h with
  | refl => exact H
  | trans _ _ _ _ _ _ _ ih1 ih2 =>
    exact ih2 (fun r1 m hm => hK r1 m (List.mem_append_right _ hm))
      (ih1 (fun r1 m hm => hK r1 m (List.mem_append_left _ hm)) H)
  | higherTerm => exact H.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl)
  | campaign r peers cl _ _ hs hg _ _ => exact RInv_campaign id _ H hs hg
  | win r mt ms h1 _ h3 _ _ _ => exact RInv_win id mt _ H h1 h3
  | appAccept m r lastnewi es' h1 _ _ _ _ _ h7 h8 =>
    exact RInv_appAccept m lastnewi es' _ H h7 h8 (hK r m List.mem_cons_self h1 H)
  | heartbeat m r _ _ _ _ _ h6 => exact RInv_heartbeat m.src m.commit _ H h6
  | commit r n h1 h2 h3 _ _ => exact RInv_commit n H h1 h2 h3
  | propose m r cs _ h2 h3 h4 => exact RInv_propose id m cs _ H h2 h3 h4
  | propDrop m r cs _ h2 h3 h4 => exact RInv_propDrop m cs H h2 h3 h4
  | snapRestore m r fp' cs' _ _ _ _ _ h6 _ h8 _ h10 =>
    exact RInv_snapRestore m fp' cs' _ H h6 h8 (hAdm _ _ h10)
  | snapFastfwd m r _ _ _ _ _ h6 h7 => exact RInv_snapFastfwd m _ H h6 h7
  | readAck m r N =>
    have := preadRespondAll_fields id
      ({ r.p with rd := { r.p.rd with
           ro := (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).1 } })
      (readonlyAdvance (readonlyRecvAck r.p.rd.ro m.src m.ctx) N).2
    exact RInv_keep _ H this.1 this.2.1 this.2.2.1 (Or.inr this.2.2.2)
  | advance r a h1 h2 h3 h4 => exact RInv_advance a H h1 h2 h3 h4
  | applySnap r h1 => exact RInv_applySnap H h1
  | applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 _ =>
    exact RInv_applyConf k e op cs' H h1 h2 h3 h4 h5 h6 h7 h8
  | _ =>
    first
    | exact RInv_keep _ H rfl rfl rfl (Or.inr rfl)
    | exact RInv_keep _ H rfl rfl rfl (Or.inl rfl)
    | exact H.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl)

/-- A derivation that receives nothing keeps `RInv` with no message knowledge. -/
theorem RInv_stepR_nil {Adm : List raftpb.Entry → CCState → Prop} {dec : CCDec} {c0 : CCState}
    {id : w64} (hAdm : ∀ l cs, Adm l cs → cfgFold dec c0 l = some cs)
    {r r' : RState} (h : StepR Adm dec id r [] r') (H : RInv dec c0 r) : RInv dec c0 r' :=
  RInv_stepR hAdm h (fun _ _ hm => by simp at hm) H

/-- The dynamic model's admissible configurations satisfy `RInv_stepR`'s premise. -/
theorem AdmFold_fold (dec : CCDec) (c0 : CCState) :
    ∀ l cs, AdmFold dec c0 l cs → cfgFold dec c0 l = some cs := fun _ _ h => h

end inv

end EtcdGrove
end Perennial
