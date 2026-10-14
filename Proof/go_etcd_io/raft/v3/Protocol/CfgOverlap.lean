/-
Quorum overlap across configuration changes (2026-10-14, reconfiguration stage B1),
Lean-first: pure, no ghost state. The paper proof this file founds is
`notes/reconfiguration-safety.md`.

* `QOverlap c1 c2`: every joint quorum of `c1` meets every joint quorum of `c2` (`JQuorum`,
  `Protocol/StepC.lean`).
* `CfgOk s`: what a configuration a node can be in satisfies -- `checkInvariants` accepts it
  (`CfgInv`), it has an incoming voter, and it tracks fewer than `2^62` ids. The size bound
  keeps `Simple`'s `symdiff` count (a Go `int`) from wrapping: two disjoint incoming voter
  sets of `2^62` ids each would have a symmetric difference of `2^63`, which reads as
  negative, and `Simple` would accept the swap (with `≤ 2^62`, raft's own bound in
  `raft.applyConfChange.spec`, `simpleM_overlap` is false at that one boundary).
* One configuration change keeps quorums overlapping (`simpleM_overlap`,
  `enterJointM_overlap`, `leaveJointM_overlap`, `ccApplyM_overlap`), each keeping `CfgOk`
  given the bound on the result; `maj_symdiff_overlap` is the arithmetic behind `Simple`
  (majorities of two sets that differ by at most one id meet).
* The configuration of a log prefix: `cfgFold dec s0 l`, every conf-change entry of `l`
  (`IsConfEnt`) applied in order by `ccStepB` (`ccApplyM` and the size bound), its change
  read by `dec` from the entry and the prefix before it (`CCDec`, since stage B3: an
  application may change what it applies depending on the history, as etcd does; the
  decoder from the proposed data, `isPropData`, is `decOfData`); `none` where Go would panic
  (`applyConfChange`'s `panic(err)`, an undecodable entry) or the bound fails.
  `confPos`/`confCount` are a log's conf-change positions (0-based list indices: the entry
  at log index `i` of a log from `base0` is at position `i - 1`) and their number.
  `fold_adjacent`: two prefixes of one log whose conf counts differ by at most one have
  overlapping configurations.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApplyConf

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-! ### Majorities of nearly equal sets -/

theorem gset_size_inter_diff (l r : GSet w64) :
    GMap.size l = GMap.size (l ∩ r) + GMap.size (l \ r) := by
  have hd : (l ∩ r) ## (l \ r) := by
    rw [GMap.elem_of_disjoint]; intro x h1 h2
    rw [GMap.elem_of_intersection] at h1; rw [GMap.elem_of_difference] at h2
    exact h2.2 h1.2
  have he : l = (l ∩ r) ∪ (l \ r) := by
    apply GMap.set_eq; intro x
    rw [GMap.elem_of_union, GMap.elem_of_intersection, GMap.elem_of_difference]
    by_cases hx : x ∈ r <;> simp [hx]
  have := GMap.size_union hd
  rw [← he] at this
  exact this

theorem gset_inter_comm (l r : GSet w64) : l ∩ r = r ∩ l := by
  apply GMap.set_eq; intro x
  rw [GMap.elem_of_intersection, GMap.elem_of_intersection]
  exact And.comm

/-- Majorities of two sets whose symmetric difference has at most one id meet. -/
theorem maj_symdiff_overlap (l r q1 q2 : GSet w64) (hd : symdiffN l r ≤ 1)
    (h1 : IsQuorum l q1) (h2 : IsQuorum r q2) : ∃ x, x ∈ q1 ∧ x ∈ q2 := by
  apply Classical.byContradiction
  intro hno
  have hdis : (q1 ∩ l) ## (q2 ∩ r) := by
    rw [GMap.elem_of_disjoint]; intro x ha hb
    rw [GMap.elem_of_intersection] at ha hb
    exact hno ⟨x, ha.1, hb.1⟩
  have hsub : (q1 ∩ l) ∪ (q2 ∩ r) ⊆ l ∪ r := by
    rw [GMap.elem_of_subseteq]; intro x hx
    rw [GMap.elem_of_union, GMap.elem_of_intersection, GMap.elem_of_intersection] at hx
    rw [GMap.elem_of_union]
    exact hx.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have hle := GMap.subseteq_size hsub
  rw [GMap.size_union hdis, GMap.size_union_alt] at hle
  have hl := gset_size_inter_diff l r
  have hr := gset_size_inter_diff r l
  rw [gset_inter_comm r l] at hr
  unfold IsQuorum at h1 h2
  unfold symdiffN at hd
  -- `size` is `GMap.size`
  change GMap.size l < 2 * GMap.size (q1 ∩ l) at h1
  change GMap.size r < 2 * GMap.size (q2 ∩ r) at h2
  omega

/-! ### One configuration change -/

section model
variable [FfiSyntax]

/-- A configuration a node can be in (see the file header). -/
def CfgOk (s : CCState) : Prop :=
  CfgInv s ∧ s.cfg.incoming ≠ ∅ ∧ GMap.size s.cfg.ids < 2 ^ 62

theorem checkedM_some {s s' : CCState} (h : checkedM s = some s') : s' = s ∧ CfgInv s := by
  unfold checkedM at h
  split at h
  · rename_i hc; cases h; exact ⟨rfl, hc⟩
  · cases h

theorem applyM_incoming {ccs : List raftpb.ConfChangeSingle} {s s' : CCState}
    (h : applyM ccs s = some s') : s'.cfg.incoming ≠ ∅ := by
  unfold applyM at h
  cases h1 : applyAll ccs s with
  | none => rw [h1] at h; cases h
  | some s1 =>
    rw [h1, Option.bind_some] at h
    split at h
    · cases h
    · rename_i hne; cases h; exact hne

theorem incoming_subset_ids (c : CfgM) : c.incoming ⊆ c.ids := by
  rw [GMap.elem_of_subseteq]; intro x hx
  unfold CfgM.ids CfgM.voters
  rw [GMap.elem_of_union, GMap.elem_of_union]
  exact Or.inl (Or.inl hx)

theorem size_incoming_le (c : CfgM) : GMap.size c.incoming ≤ GMap.size c.ids :=
  GMap.subseteq_size (incoming_subset_ids c)

theorem size_diff_le (l r : GSet w64) : GMap.size (l \ r) ≤ GMap.size l := by
  have := gset_size_inter_diff l r
  omega

/-- Below `2^63`, `Simple`'s check reads the count as it is. -/
theorem not_symdiffTooBig {l r : GSet w64} (hb : symdiffN l r < 2 ^ 63)
    (h : ¬ SymdiffTooBig l r) : symdiffN l r ≤ 1 := by
  unfold SymdiffTooBig at h
  have : sint.Z (W64 (symdiffN l r : Int)) = (symdiffN l r : Int) := by
    have h0 : (0 : Int) ≤ (symdiffN l r : Int) := Int.natCast_nonneg _
    have h1 : (symdiffN l r : Int) < 2 ^ 63 := by exact_mod_cast hb
    word
  rw [this] at h
  omega

theorem simpleM_overlap {ccs : List raftpb.ConfChangeSingle} {s s' : CCState}
    (h : simpleM ccs s = some s') (hs : CfgOk s) (hb : GMap.size s'.cfg.ids < 2 ^ 62) :
    QOverlap s.cfg s'.cfg ∧ CfgOk s' := by
  obtain ⟨_, hsi, hsb⟩ := hs
  unfold simpleM at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hout0
  have hout : s.cfg.outgoing = ∅ := Classical.not_not.mp hout0
  split at h
  · cases h
  rename_i s1 hs1
  split at h
  · cases h
  rename_i hsd
  obtain ⟨rfl, hinv⟩ := checkedM_some h
  have hout' : s'.cfg.outgoing = ∅ := by
    rw [applyM_outgoing ccs _ _ hs1]; exact hout
  have hin' := applyM_incoming hs1
  refine ⟨fun q1 q2 h1 h2 => ?_, ⟨hinv, hin', hb⟩⟩
  have hsd' : symdiffN s.cfg.incoming s'.cfg.incoming ≤ 1 := by
    apply not_symdiffTooBig _ hsd
    have := size_diff_le s.cfg.incoming s'.cfg.incoming
    have := size_diff_le s'.cfg.incoming s.cfg.incoming
    have := size_incoming_le s.cfg
    have := size_incoming_le s'.cfg
    unfold symdiffN
    omega
  exact maj_symdiff_overlap _ _ q1 q2 hsd' (JQuorum_incoming hsi h1) (JQuorum_incoming hin' h2)

theorem enterJointM_overlap {al : Bool} {ccs : List raftpb.ConfChangeSingle} {s s' : CCState}
    (h : enterJointM al ccs s = some s') (hs : CfgOk s) (hb : GMap.size s'.cfg.ids < 2 ^ 62) :
    QOverlap s.cfg s'.cfg ∧ CfgOk s' := by
  obtain ⟨_, hsi, _⟩ := hs
  unfold enterJointM at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i s1 hs1
  obtain ⟨rfl, hinv⟩ := checkedM_some h
  have hout : s1.cfg.outgoing = s.cfg.incoming := applyM_outgoing ccs _ _ hs1
  have hin' := applyM_incoming hs1
  refine ⟨fun q1 q2 h1 h2 => ?_, ⟨hinv, hin', hb⟩⟩
  have h2' : MajQ s.cfg.incoming q2 := by
    have := h2.2
    simp only at this
    rw [hout] at this
    exact this
  exact quorums_intersect s.cfg.incoming q1 q2 (JQuorum_incoming hsi h1) ((MajQ_of_ne q2 hsi).1 h2')

theorem leaveJointM_overlap {s s' : CCState}
    (h : leaveJointM s = some s') (hs : CfgOk s) (hb : GMap.size s'.cfg.ids < 2 ^ 62) :
    QOverlap s.cfg s'.cfg ∧ CfgOk s' := by
  obtain ⟨_, hsi, _⟩ := hs
  unfold leaveJointM at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨rfl, hinv⟩ := checkedM_some h
  have hin : (leaveJointState s).cfg.incoming = s.cfg.incoming := rfl
  refine ⟨fun q1 q2 h1 h2 => ?_, ⟨hinv, by rw [hin]; exact hsi, hb⟩⟩
  have h2' := JQuorum_incoming (by rw [hin]; exact hsi) h2
  rw [hin] at h2'
  exact quorums_intersect s.cfg.incoming q1 q2 (JQuorum_incoming hsi h1) h2'

/-- `raft.applyConfChange`'s change keeps quorums overlapping. -/
theorem ccApplyM_overlap {t : raftpb.ConfChangeTransition} {ccs : List raftpb.ConfChangeSingle}
    {s s' : CCState} (h : ccApplyM t ccs s = some s') (hs : CfgOk s)
    (hb : GMap.size s'.cfg.ids < 2 ^ 62) : QOverlap s.cfg s'.cfg ∧ CfgOk s' := by
  unfold ccApplyM at h
  split at h
  · exact leaveJointM_overlap h hs hb
  · split at h
    · exact enterJointM_overlap h hs hb
    · exact simpleM_overlap h hs hb
    · cases h

/-! ### The configuration of a log prefix -/

/-- A conf change as `raft.applyConfChange` takes it: `AsV2`'s transition and changes. -/
abbrev CCOp := raftpb.ConfChangeTransition × List raftpb.ConfChangeSingle

/-- One conf change applied, within the size bound of `CfgOk`. -/
def ccStepB (op : CCOp) (s : CCState) : Option CCState :=
  (ccApplyM op.1 op.2 s).bind fun s' => if GMap.size s'.cfg.ids < 2 ^ 62 then some s' else none

/-- A decoder (2026-10-14, reconfiguration stage B3): the change a conf-change entry makes,
given the log prefix before it. The prefix is there because etcd's application may change what
it applies depending on the history (`EtcdServer.applyConfChange` validates the change against
its membership store and, if it refuses it, passes it to raft with `NodeID` zeroed, which
`confchange` then skips): every node applies the same committed entry at the same prefix,
which is all the argument needs. `CCDec.ofEnt` is a decoder that ignores the prefix. -/
abbrev CCDec := List raftpb.Entry → raftpb.Entry → Option CCOp

/-- A decoder of the entry alone. -/
def CCDec.ofEnt (d : raftpb.Entry → Option CCOp) : CCDec := fun _ e => d e

/-- One entry, after the prefix `pre`: a conf-change entry's decoded change applied; any other
entry leaves the configuration. -/
def entStep (dec : CCDec) (pre : List raftpb.Entry) (s : CCState) (e : raftpb.Entry) :
    Option CCState :=
  if IsConfEnt e then (dec pre e).bind fun op => ccStepB op s else some s

/-- The configuration after the entries `l`, from `s`, the entries `pre` before them. -/
def cfgFoldFrom (dec : CCDec) (pre : List raftpb.Entry) (s : CCState) :
    List raftpb.Entry → Option CCState
  | [] => some s
  | e :: es => (entStep dec pre s e).bind fun s' => cfgFoldFrom dec (pre ++ [e]) s' es

/-- The configuration after the entries `l` (a log from its start), from `s`. -/
def cfgFold (dec : CCDec) (s : CCState) (l : List raftpb.Entry) : Option CCState :=
  cfgFoldFrom dec [] s l

/-- The positions of the conf-change entries of `l`, in order, counted from `k`. -/
def confPosFrom (k : Nat) : List raftpb.Entry → List Nat
  | [] => []
  | e :: es => (if IsConfEnt e then [k] else []) ++ confPosFrom (k + 1) es

/-- The positions (0-based) of the conf-change entries of `l`, in order. -/
def confPos (l : List raftpb.Entry) : List Nat := confPosFrom 0 l

theorem mem_confPosFrom (k : Nat) (l : List raftpb.Entry) (i : Nat) :
    i ∈ confPosFrom k l ↔ k ≤ i ∧ ∃ e, l[i - k]? = some e ∧ IsConfEnt e := by
  induction l generalizing k with
  | nil => simp [confPosFrom]
  | cons e l ih =>
    simp only [confPosFrom, List.mem_append, ih]
    constructor
    · rintro (h | ⟨hk, e', he', hc⟩)
      · by_cases hc : IsConfEnt e
        · rw [if_pos hc, List.mem_singleton] at h
          subst h
          exact ⟨Nat.le_refl _, e, by simp, hc⟩
        · rw [if_neg hc] at h; cases h
      · refine ⟨by omega, e', ?_, hc⟩
        rw [show i - k = (i - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
        exact he'
    · rintro ⟨hk, e', he', hc⟩
      by_cases hik : i = k
      · subst hik
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at he'
        subst he'
        left; rw [if_pos hc]; exact List.mem_singleton_self _
      · right
        refine ⟨by omega, e', ?_, hc⟩
        rw [show i - k = (i - (k + 1)) + 1 by omega, List.getElem?_cons_succ] at he'
        exact he'

theorem mem_confPos (l : List raftpb.Entry) (i : Nat) :
    i ∈ confPos l ↔ ∃ e, l[i]? = some e ∧ IsConfEnt e := by
  unfold confPos
  rw [mem_confPosFrom]
  simp

theorem length_confPosFrom (k : Nat) (l : List raftpb.Entry) :
    (confPosFrom k l).length = confCount l := by
  induction l generalizing k with
  | nil => rfl
  | cons e l ih =>
    rw [confPosFrom, List.length_append, ih, confCount_cons]
    by_cases h : IsConfEnt e <;> simp [h, Nat.add_comm]

theorem length_confPos (l : List raftpb.Entry) : (confPos l).length = confCount l :=
  length_confPosFrom 0 l

theorem cfgFoldFrom_append (dec : CCDec) (pre : List raftpb.Entry) (s : CCState)
    (l1 l2 : List raftpb.Entry) :
    cfgFoldFrom dec pre s (l1 ++ l2)
      = (cfgFoldFrom dec pre s l1).bind fun s' => cfgFoldFrom dec (pre ++ l1) s' l2 := by
  induction l1 generalizing s pre with
  | nil => simp [cfgFoldFrom]
  | cons e l ih =>
    simp only [List.cons_append, cfgFoldFrom]
    cases entStep dec pre s e with
    | none => rfl
    | some s' => simp [ih]

theorem cfgFold_append (dec : CCDec) (s : CCState) (l1 l2 : List raftpb.Entry) :
    cfgFold dec s (l1 ++ l2) = (cfgFold dec s l1).bind fun s' => cfgFoldFrom dec l1 s' l2 := by
  unfold cfgFold; rw [cfgFoldFrom_append, List.nil_append]

/-- One more entry at the end. -/
theorem cfgFold_snoc (dec : CCDec) (s : CCState) (l : List raftpb.Entry) (e : raftpb.Entry) :
    cfgFold dec s (l ++ [e]) = (cfgFold dec s l).bind fun s' => entStep dec l s' e := by
  rw [cfgFold_append]
  cases cfgFold dec s l with
  | none => rfl
  | some s' =>
    simp only [Option.bind_some, cfgFoldFrom]
    cases entStep dec l s' e <;> rfl

/-- An entry that is not a conf change leaves the configuration. -/
theorem entStep_not_conf (dec : CCDec) (pre : List raftpb.Entry) (s : CCState)
    (e : raftpb.Entry) (h : ¬ IsConfEnt e) : entStep dec pre s e = some s := by
  unfold entStep; rw [if_neg h]

/-- One conf-change entry keeps quorums overlapping and `CfgOk`. -/
theorem entStep_overlap {dec : CCDec} {pre : List raftpb.Entry} {s s' : CCState}
    {e : raftpb.Entry} (h : entStep dec pre s e = some s') (hs : CfgOk s) :
    QOverlap s.cfg s'.cfg ∧ CfgOk s' := by
  unfold entStep at h
  split at h
  · cases hd : dec pre e with
    | none => rw [hd] at h; cases h
    | some op =>
      rw [hd, Option.bind_some] at h
      unfold ccStepB at h
      cases ha : ccApplyM op.1 op.2 s with
      | none => rw [ha] at h; cases h
      | some s1 =>
        rw [ha, Option.bind_some] at h
        split at h
        · rename_i hb; cases h; exact ccApplyM_overlap ha hs hb
        · cases h
  · cases h; exact ⟨QOverlap.refl hs.2.1, hs⟩

theorem cfgFoldFrom_ok {dec : CCDec} {pre : List raftpb.Entry} {s s' : CCState}
    {l : List raftpb.Entry} (h : cfgFoldFrom dec pre s l = some s') (hs : CfgOk s) :
    CfgOk s' := by
  induction l generalizing s pre with
  | nil => cases h; exact hs
  | cons e l ih =>
    simp only [cfgFoldFrom] at h
    cases he : entStep dec pre s e with
    | none => rw [he] at h; cases h
    | some s1 =>
      rw [he, Option.bind_some] at h
      exact ih h (entStep_overlap he hs).2

theorem cfgFold_ok {dec : CCDec} {s s' : CCState} {l : List raftpb.Entry}
    (h : cfgFold dec s l = some s') (hs : CfgOk s) : CfgOk s' :=
  cfgFoldFrom_ok h hs

/-- Entries with no conf change leave the configuration. -/
theorem cfgFoldFrom_zero (dec : CCDec) (pre : List raftpb.Entry) (s : CCState)
    (l : List raftpb.Entry) (h : confCount l = 0) : cfgFoldFrom dec pre s l = some s := by
  induction l generalizing pre with
  | nil => rfl
  | cons e l ih =>
    rw [confCount_cons] at h
    have hn : ¬ IsConfEnt e := by intro hc; rw [if_pos hc] at h; omega
    rw [if_neg hn] at h
    simp only [cfgFoldFrom, entStep_not_conf dec pre s e hn, Option.bind_some]
    exact ih _ (by omega)

theorem cfgFold_zero (dec : CCDec) (s : CCState) (l : List raftpb.Entry)
    (h : confCount l = 0) : cfgFold dec s l = some s :=
  cfgFoldFrom_zero dec [] s l h

/-- Entries with at most one conf change keep quorums overlapping. -/
theorem cfgFoldFrom_le_one_overlap {dec : CCDec} {pre : List raftpb.Entry} {s s' : CCState}
    {l : List raftpb.Entry} (hc : confCount l ≤ 1) (h : cfgFoldFrom dec pre s l = some s')
    (hs : CfgOk s) : QOverlap s.cfg s'.cfg := by
  induction l generalizing s pre with
  | nil => cases h; exact QOverlap.refl hs.2.1
  | cons e l ih =>
    rw [confCount_cons] at hc
    simp only [cfgFoldFrom] at h
    by_cases he : IsConfEnt e
    · rw [if_pos he] at hc
      cases hs1 : entStep dec pre s e with
      | none => rw [hs1] at h; cases h
      | some s1 =>
        rw [hs1, Option.bind_some, cfgFoldFrom_zero dec _ s1 l (by omega)] at h
        cases h
        exact (entStep_overlap hs1 hs).1
    · rw [if_neg he] at hc
      rw [entStep_not_conf dec pre s e he, Option.bind_some] at h
      exact ih (by omega) h hs

theorem cfgFold_le_one_overlap {dec : CCDec} {s s' : CCState}
    {l : List raftpb.Entry} (hc : confCount l ≤ 1) (h : cfgFold dec s l = some s')
    (hs : CfgOk s) : QOverlap s.cfg s'.cfg :=
  cfgFoldFrom_le_one_overlap hc h hs

/-- Two prefixes of one log whose conf counts differ by at most one have overlapping
configurations. -/
theorem fold_adjacent (dec : CCDec) (l : List raftpb.Entry) (i j : Nat)
    (s0 si sj : CCState) (hij : i ≤ j) (hc : confCount (l.take j) ≤ confCount (l.take i) + 1)
    (h0 : CfgOk s0) (hi : cfgFold dec s0 (l.take i) = some si)
    (hj : cfgFold dec s0 (l.take j) = some sj) : QOverlap si.cfg sj.cfg := by
  have hsplit : l.take j = l.take i ++ (l.drop i).take (j - i) := by
    have h := List.take_add (l := l) (i := i) (j := j - i)
    rwa [Nat.add_sub_cancel' hij] at h
  rw [hsplit, cfgFold_append, hi, Option.bind_some] at hj
  rw [hsplit, confCount_append] at hc
  exact cfgFoldFrom_le_one_overlap (by omega) hj (cfgFold_ok hi h0)

/-- The symmetric form: the conf counts of the two prefixes, in either order. -/
theorem fold_adjacent' (dec : CCDec) (l : List raftpb.Entry) (i j : Nat)
    (s0 si sj : CCState) (hc1 : confCount (l.take j) ≤ confCount (l.take i) + 1)
    (hc2 : confCount (l.take i) ≤ confCount (l.take j) + 1)
    (h0 : CfgOk s0) (hi : cfgFold dec s0 (l.take i) = some si)
    (hj : cfgFold dec s0 (l.take j) = some sj) : QOverlap si.cfg sj.cfg := by
  rcases Nat.le_total i j with hij | hji
  · exact fold_adjacent dec l i j s0 si sj hij hc1 h0 hi hj
  · exact (fold_adjacent dec l j i s0 sj si hji hc2 h0 hj hi).symm

/-! ### The decoder from the entries' bytes (2026-10-14, reconfiguration stage B3)

A conf-change entry's `Data'` is a slice; what it holds is recorded, once proposed, in the
ghost map of proposed slices (`isPropData`, `Protocol/Ghost.lean`), which agrees across
nodes. Given that map's content as a function `data` from slices to bytes, a conf-change
entry decodes the way `stepLeader` and `RawNode.ApplyConfChange` read it: `Unmarshal` by the
entry's type (`ccDecodeV1`/`ccDecodeV2`), then `AsV2` (`ccV2Of`). An entry whose bytes do not
decode has no change (`none`, which `cfgFold` turns into `none`: Go panics there). The
decoder an etcd-like application uses may also depend on the prefix (`CCDec`); this one does
not. -/

/-- The conf change of type `ty` the bytes `bs` encode. -/
def ccMsgOfBytes (ty : w32) (bs : List w8) : Option CCMsg :=
  if ty = W32 1 then (ccDecodeV1 bs).map CCMsg.v1
  else if ty = W32 2 then (ccDecodeV2 bs).map CCMsg.v2
  else none

/-- The decoder of entries whose slices hold `data`: by the entry alone. -/
def decOfData (data : GoSlice → List w8) : CCDec :=
  CCDec.ofEnt fun e => (ccMsgOfBytes e.Type' (data e.Data')).map ccV2Of

/-- A conf-change entry whose bytes decode (`CCDecodes`, which `stepLeader` checks when it
is proposed) has a change. -/
theorem decOfData_some (data : GoSlice → List w8) (pre : List raftpb.Entry) (e : raftpb.Entry)
    (hc : IsConfEnt e) (hd : CCDecodes e.Type' (data e.Data')) :
    ∃ op, decOfData data pre e = some op := by
  simp only [decOfData, CCDec.ofEnt, ccMsgOfBytes]
  rcases hc with h1 | h2
  · obtain ⟨m, hm⟩ := hd.1 h1
    rw [if_pos h1, hm]; exact ⟨_, rfl⟩
  · have h1 : ¬ e.Type' = W32 1 := by
      rw [h2]; word
    obtain ⟨m, hm⟩ := hd.2 h2
    rw [if_neg h1, if_pos h2, hm]; exact ⟨_, rfl⟩

end model

end EtcdGrove
end Perennial
