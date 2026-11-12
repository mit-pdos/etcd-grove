/-
# Snapshot records and lists: pure lemmas (2026-10-28, stage U2; the conf-change decision switch)

The pure part of the snapshot laws of `InvApiDec.lean` (`snapshotCert_make_impl`,
`snapshotCert_made_impl`): a record matching a registry key (`SnapRec.Matches`), `List.Forall₂`
lemmas, and a `ConfState`'s lists against a membership (`cfgM_of_confStateIs`, `lists_of_cfgM`).
(Until the decision switch also stage U2's rule-based registry, `ownSnapsMade γ r c0`, now
`InvApiDec`'s over `confAtU`.)
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRule
public import Proof.go_etcd_io.raft.v3.InvApiView
public import Proof.go_etcd_io.raft.v3.Protocol.SnapCertDyn
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 ApiImpl

section pure
variable [GooseExts]

/-- A snapshot's record matches a registry key: its index and data. -/
def _root_.Perennial.EtcdGrove.SnapRec.Matches (s : SnapRec) (key : w64 × List w8) : Prop :=
  uint.nat key.1 = s.index ∧ key.2 = s.data

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {S : List α} {K : List β} {b : β}
    (h : List.Forall₂ R S K) (hb : b ∈ K) : ∃ a ∈ S, R a b := by
  induction h with
  | nil => cases hb
  | @cons a b' S K hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨a', ha', h'⟩ := ih hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {S : List α} {K : List β} {a : α} {b : β}
    (h : List.Forall₂ R S K) (hab : R a b) : List.Forall₂ R (S ++ [a]) (K ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab .nil
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem perm_elements_nodup (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem listToSet_of_perm (l : List w64) (X : GSet w64) (h : l ≡ₚ GMap.elements X) :
    GMap.listToSet l = X := by
  rw [← GMap.listToSet_elements X]
  apply GMap.set_eq
  intro x
  rw [GMap.elem_of_list_to_set, GMap.elem_of_list_to_set]
  exact h.mem_iff

/-- The configuration of a `ConfState` reporting a membership is the membership's. -/
theorem cfgM_of_confStateIs (cs : ConfStateM) (m : Membership) (t i : w64) (d : List w8)
    (hc : confStateIs cs m)
    (hal : cs.VotersOutgoing' = [] → m.autoLeave = false) :
    SnapTrip.cfgM ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ = cfgOf m := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hc
  unfold SnapTrip.cfgM csCfgM cfgOf
  simp only [ConfStateM.lists]
  rw [listToSet_of_perm _ _ h1, listToSet_of_perm _ _ h2, listToSet_of_perm _ _ h3,
    listToSet_of_perm _ _ h4]
  congr 1
  by_cases h : cs.VotersOutgoing' = []
  · simp [h, hal h]
  · simp [h]

/-- The lists of a snapshot whose configuration is a membership's report it, given no repeats. -/
theorem lists_of_cfgM (k : SnapTrip) (m : Membership) (hk : SnapListsOk k)
    (hm : k.cfgM = cfgOf m) : k.cl.Is m ∧ k.al = m.autoLeave := by
  obtain ⟨-, hv, hl, ho, hn, -, hal, -⟩ := hk
  unfold SnapTrip.cfgM csCfgM cfgOf at hm
  simp only [CfgM.mk.injEq] at hm
  obtain ⟨e1, e2, e3, e4, e5⟩ := hm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← e1]; exact perm_elements_nodup _ hv
  · rw [← e2]; exact perm_elements_nodup _ ho
  · rw [← e3]; exact perm_elements_nodup _ hl
  · rw [← e4]; exact perm_elements_nodup _ hn
  · by_cases h : k.cl.outgoing = []
    · simp [h] at e5; rw [hal h, ← e5]
    · simp [h] at e5; exact e5

end pure

end ApiImpl
end EtcdGrove
end Perennial
