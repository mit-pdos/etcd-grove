/-
# The membership of a log over the client's decisions (2026-10-28, the conf-change decision switch)

The bridge from the API's decisions (`ConfDecision`, recorded by position: a decision map `M`,
`Protocol/DecMap.lean`) to the protocol's fold: a cluster's nodes run raft's dynamic mode of the base
decoder that decides nothing (`noDec`), over the decisions recorded (`effDec noDec M`), so a conf
entry's configuration step is its recorded decision's (`ccDecOf`: a change applied as `AsV2` makes it,
`none` a rejection), and an undecided one has none.

- `decFold M c0 l`: the membership after the log `l` from `c0`, every conf entry by its decision in `M`
  (at its position), `none` past an undecided one or a change that fails;
- `cfgFold_decs`: the protocol's fold of a log is `decFold` of the log as a client sees it, from a
  valid `c0`; `decFold_mono` (more decisions keep a defined fold), `decFold_valid`.

Internal: it reads the sealed `Membership.Valid`/`applyChange`. (Replaces `ConfRuleDec.lean`, the
rule's decoder of stage U4a's interim cluster.)
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRule
public import Proof.go_etcd_io.raft.v3.InvApiView
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- Two comparable lists agree below both lengths. -/
theorem take_eq_of_cmp {α : Type} (l1 l2 : List α) (k : Nat) (h : l1 <+: l2 ∨ l2 <+: l1)
    (h1 : k ≤ l1.length) (h2 : k ≤ l2.length) : l1.take k = l2.take k := by
  rcases h with h | h
  · rw [List.prefix_iff_eq_take.1 h, List.take_take, Nat.min_eq_left h1]
  · rw [List.prefix_iff_eq_take.1 h, List.take_take, Nat.min_eq_left h2]

theorem getElem?_eq_of_cmp {α : Type} (l1 l2 : List α) (k : Nat) (h : l1 <+: l2 ∨ l2 <+: l1)
    (h1 : k < l1.length) (h2 : k < l2.length) : l1[k]? = l2[k]? := by
  have := take_eq_of_cmp l1 l2 (k + 1) h h1 h2
  have e1 : (l1.take (k + 1))[k]? = l1[k]? := by rw [List.getElem?_take]; simp
  have e2 : (l2.take (k + 1))[k]? = l2[k]? := by rw [List.getElem?_take]; simp
  rw [← e1, ← e2, this]

theorem take_succ_of_getElem? {α : Type} (l : List α) (k : Nat) (e : α) (h : l[k]? = some e) :
    l.take (k + 1) = l.take k ++ [e] := by
  rw [List.take_add_one, h]; rfl

/-- A decision as the protocol's decision map records it: a change applied (`some`), or a skip. -/
def _root_.Perennial.EtcdGrove.ConfDecision.toOpt : ConfDecision → Option ConfChangeIM
  | .apply o => some o
  | .skip => none

theorem _root_.Perennial.EtcdGrove.ConfDecision.toOpt_inj {d1 d2 : ConfDecision}
    (h : d1.toOpt = d2.toOpt) : d1 = d2 := by
  cases d1 <;> cases d2 <;> simp_all [ConfDecision.toOpt]

/-- One entry, at position `k`, at the membership `m`: a conf entry by its decision recorded at `k`
(`none` if undecided); any other entry keeps `m`. -/
def decStep (M : DecMap) (k : Nat) (m : Membership) (e : LogEntry) : Option Membership :=
  if e.isConfChange then
    match M.lookup k with
    | none => none
    | some none => some m
    | some (some o) => Membership.applyChange o m
  else some m

/-- The membership after the entries `l`, from `m`, the first at position `k`. -/
def decFoldFrom (M : DecMap) (k : Nat) (m : Membership) : List LogEntry → Option Membership
  | [] => some m
  | e :: es => (decStep M k m e).bind fun m' => decFoldFrom M (k + 1) m' es

/-- **The membership after the log `l`**, from `c0`, every conf entry by its recorded decision. -/
def decFold (M : DecMap) (c0 : Membership) (l : List LogEntry) : Option Membership :=
  decFoldFrom M 0 c0 l

theorem decFoldFrom_append (M : DecMap) (k : Nat) (m : Membership) (l1 l2 : List LogEntry) :
    decFoldFrom M k m (l1 ++ l2)
      = (decFoldFrom M k m l1).bind fun m' => decFoldFrom M (k + l1.length) m' l2 := by
  induction l1 generalizing m k with
  | nil => simp [decFoldFrom]
  | cons e l ih =>
    simp only [List.cons_append, decFoldFrom, List.length_cons]
    cases decStep M k m e with
    | none => rfl
    | some m' =>
      simp only [Option.bind_some]
      rw [ih]
      rw [show k + 1 + l.length = k + (l.length + 1) by omega]

theorem decFold_snoc (M : DecMap) (c0 : Membership) (l : List LogEntry) (e : LogEntry) :
    decFold M c0 (l ++ [e]) = (decFold M c0 l).bind fun m => decStep M l.length m e := by
  unfold decFold
  rw [decFoldFrom_append, Nat.zero_add]
  cases decFoldFrom M 0 c0 l with
  | none => rfl
  | some m =>
    simp only [Option.bind_some, decFoldFrom]
    cases decStep M l.length m e <;> rfl

theorem decFold_nil (M : DecMap) (c0 : Membership) : decFold M c0 [] = some c0 := rfl

/-- An entry that is no conf change keeps the membership. -/
theorem decFold_snoc_normal (M : DecMap) (c0 : Membership) (l : List LogEntry) (e : LogEntry)
    (h : ¬ e.isConfChange) : decFold M c0 (l ++ [e]) = decFold M c0 l := by
  rw [decFold_snoc]
  cases decFold M c0 l with
  | none => rfl
  | some m => simp only [Option.bind_some, decStep, ite_eq_right h]

/-- A decided conf entry: the decision's step. -/
theorem decStep_decided (M : DecMap) (k : Nat) (m : Membership) (e : LogEntry) (d : ConfDecision)
    (hc : e.isConfChange) (hk : M.lookup k = some d.toOpt) : decStep M k m e = d.step m := by
  unfold decStep
  rw [ite_eq_left hc, hk]
  cases d <;> rfl

/-- Past positions with no conf entry the membership is kept. -/
theorem decFold_take_noConf (M : DecMap) (c0 : Membership) (l : List LogEntry) (a b : Nat)
    (hn : NoConfChangeIn l a b) (hab : a ≤ b) (hb : b ≤ l.length) :
    decFold M c0 (l.take b) = decFold M c0 (l.take a) := by
  induction b with
  | zero => rw [Nat.le_zero.1 hab]
  | succ b ih =>
    rcases Nat.lt_or_ge b a with h | h
    · rw [show a = b + 1 by omega]
    have hlt : b < l.length := by omega
    obtain ⟨e, he⟩ : ∃ e, l[b]? = some e := ⟨l[b], List.getElem?_eq_getElem hlt⟩
    rw [take_succ_of_getElem? l b e he, decFold_snoc_normal M c0 _ e (hn b e h (by omega) he)]
    exact ih (fun k e' h1 h2 he' => hn k e' h1 (by omega) he') h (by omega)

/-- **More decisions keep a defined fold.** -/
theorem decFoldFrom_mono {M M' : DecMap} (hM : M ⊆ M') (k : Nat) (m m' : Membership)
    (l : List LogEntry) (h : decFoldFrom M k m l = some m') : decFoldFrom M' k m l = some m' := by
  induction l generalizing k m with
  | nil => exact h
  | cons e l ih =>
    simp only [decFoldFrom] at h ⊢
    have hs : ∀ x, decStep M k m e = some x → decStep M' k m e = some x := by
      intro x hx
      unfold decStep at hx ⊢
      split at hx
      · rename_i hc
        rw [ite_eq_left hc]
        cases hl : M.lookup k with
        | none => rw [hl] at hx; cases hx
        | some v =>
          rw [hM k v hl]
          rw [hl] at hx
          exact hx
      · rename_i hc; rw [ite_eq_right hc]; exact hx
    cases h1 : decStep M k m e with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1, Option.bind_some] at h
      rw [hs x h1, Option.bind_some]
      exact ih (k + 1) x h

theorem decFold_mono {M M' : DecMap} (hM : M ⊆ M') (c0 m : Membership) (l : List LogEntry)
    (h : decFold M c0 l = some m) : decFold M' c0 l = some m :=
  decFoldFrom_mono hM 0 c0 m l h

/-- **A fold from a valid membership is valid** (a change keeps a membership valid). -/
theorem decFoldFrom_valid (M : DecMap) (k : Nat) (m m' : Membership) (l : List LogEntry)
    (hm : m.Valid) (h : decFoldFrom M k m l = some m') : m'.Valid := by
  induction l generalizing k m with
  | nil => simp only [decFoldFrom, Option.some.injEq] at h; subst h; exact hm
  | cons e l ih =>
    simp only [decFoldFrom] at h
    cases hs : decStep M k m e with
    | none => rw [hs] at h; cases h
    | some m1 =>
      rw [hs, Option.bind_some] at h
      apply ih (k + 1) m1 _ h
      unfold decStep at hs
      split at hs
      · split at hs
        · cases hs
        · cases hs; exact hm
        · exact memApply_valid _ m m1 hm hs
      · cases hs; exact hm

theorem decFold_valid (M : DecMap) (c0 m : Membership) (l : List LogEntry) (h0 : c0.Valid)
    (h : decFold M c0 l = some m) : m.Valid :=
  decFoldFrom_valid M 0 c0 m l h0 h

/-- **The protocol's fold is the API's**: from a valid `c0`, `cfgFold` of the base decoder that
decides nothing over the decisions `M` is `decFold` of the log as a client sees it, each membership
as its canonical state. -/
theorem cfgFold_decs (M : DecMap) (c0 : Membership) (h0 : c0.Valid) (L : List EntryM) :
    cfgFold (effDec noDec M) (stOf c0) L = (decFold M c0 (strip L)).map stOf := by
  suffices H : ∀ (pre : List EntryM) (m : Membership), m.Valid →
      cfgFoldFrom (effDec noDec M) pre (stOf m) L
        = (decFoldFrom M pre.length m (strip L)).map stOf from H [] c0 h0
  induction L with
  | nil => intro pre m _; rfl
  | cons e L ih =>
    intro pre m hm
    have hv : memValid m := hm
    have hstrip : strip (e :: L) = LogEntry.ofEntryM e :: strip L := rfl
    rw [hstrip]
    simp only [cfgFoldFrom, decFoldFrom]
    have hconf : IsConfEnt e ↔ (LogEntry.ofEntryM e).isConfChange := Iff.rfl
    have hlen : (pre ++ [e]).length = pre.length + 1 := by simp
    by_cases hc : IsConfEnt e
    · have hc' := hconf.1 hc
      have hed : effDec noDec M pre e = (M.lookup pre.length).map ccDecOf := rfl
      cases hl : M.lookup pre.length with
      | none =>
        have hst : entStep (effDec noDec M) pre (stOf m) e = none := by
          unfold entStep; rw [ite_eq_left hc, hed, hl]; rfl
        have hfs : decStep M pre.length m (LogEntry.ofEntryM e) = none := by
          unfold decStep; rw [ite_eq_left hc', hl]
        rw [hst, hfs]; rfl
      | some v =>
        cases v with
        | none =>
          have hst : entStep (effDec noDec M) pre (stOf m) e = some (stOf m) := by
            unfold entStep; rw [ite_eq_left hc, hed, hl]; rfl
          have hfs : decStep M pre.length m (LogEntry.ofEntryM e) = some m := by
            unfold decStep; rw [ite_eq_left hc', hl]
          rw [hst, hfs]
          simp only [Option.bind_some]
          rw [ih (pre ++ [e]) m hm, hlen]
        | some o =>
          have hst : entStep (effDec noDec M) pre (stOf m) e = ccStepB (ccV2Of o) (stOf m) := by
            unfold entStep; rw [ite_eq_left hc, hed, hl]; rfl
          have hfs : decStep M pre.length m (LogEntry.ofEntryM e) = Membership.applyChange o m := by
            unfold decStep; rw [ite_eq_left hc', hl]
          rw [hst, hfs]
          cases ha : Membership.applyChange o m with
          | none =>
            have : ccStepB (ccV2Of o) (stOf m) = none := by
              have ha' : memApply o m = none := ha
              unfold memApply at ha'
              cases hs : ccStepB (ccV2Of o) (stOf m) with
              | none => rfl
              | some _ => rw [hs] at ha'; cases ha'
            rw [this]; rfl
          | some m' =>
            have ha' : memApply o m = some m' := ha
            obtain ⟨hs, -⟩ := memApply_some hv.2 ha'
            rw [hs]
            simp only [Option.bind_some]
            rw [ih (pre ++ [e]) m' (memApply_valid o m m' hv ha'), hlen]
    · have hc' : ¬ (LogEntry.ofEntryM e).isConfChange := fun h => hc (hconf.2 h)
      rw [entStep_not_conf _ _ _ _ hc]
      simp only [decStep, ite_eq_right hc', Option.bind_some]
      rw [ih (pre ++ [e]) m hm, hlen]

end pure

end ApiImpl
end EtcdGrove
end Perennial
