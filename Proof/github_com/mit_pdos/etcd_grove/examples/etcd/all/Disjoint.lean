/- Lean-first (no Rocq counterpart).

# `etcd/all`: the two clusters' addresses and data directories are distinct

`etcd_adequate_members_below`'s premises for `etcdProgram` (`Adequacy.lean`): the program's start list
`etcdStarts` (restartN's members, then restart1's) and no bridge; the address list `etcdAddrs` and the
data-directory list `etcdDirs` without duplicates; both up to order the start list's; every address a
literal; every member name at most 200 bytes.

restartN's addresses and directories by its own lemmas (`restartN/Dir.lean`); restart1's directory apart
from restartN's by a lemma over groups (`nodup_groups`: a list of groups, each without duplicates and
labelled, whose labels are pairwise separated, concatenates to a list without duplicates), a directory
group's label the prefixes its directories start with (`TagIn`), the labels' separation decided.
(Until 2026-11-27 the program ran eleven clusters, their addresses labelled by port intervals too.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI go_etcd_io.raft.v3 etcdstart

section pure

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

/-! ## Groups -/

/-- **Labelled groups**: groups without duplicates, each element satisfying its group's label, the
labels pairwise separated (no element satisfies two separated labels), concatenate to a list without
duplicates. -/
theorem nodup_groups {α L : Type _} (Mem : L → α → Prop) (Sep : L → L → Prop)
    (hsep : ∀ l₁ l₂ a, Sep l₁ l₂ → Mem l₁ a → Mem l₂ a → False) :
    ∀ gs : List (List α × L), (∀ g ∈ gs, g.1.Nodup ∧ ∀ a ∈ g.1, Mem g.2 a) →
      (gs.map Prod.snd).Pairwise Sep → (gs.flatMap Prod.fst).Nodup
  | [], _, _ => List.nodup_nil
  | g :: gs, hg, hp => by
    rw [List.flatMap_cons, List.nodup_append]
    rw [List.map_cons, List.pairwise_cons] at hp
    have hg0 := hg g (by simp)
    refine ⟨hg0.1, nodup_groups Mem Sep hsep gs (fun g' h => hg g' (by simp [h])) hp.2, ?_⟩
    intro a ha b hb e
    subst e
    obtain ⟨g', hg', hb'⟩ := List.mem_flatMap.1 hb
    exact hsep _ _ a (hp.1 _ (List.mem_map_of_mem hg')) (hg0.2 a ha)
      ((hg g' (by simp [hg'])).2 a hb')

/-! ## Addresses -/

/-- **The program's addresses are distinct.** -/
theorem etcdAddrs_nodup (k₅ : Nat) (hk₅ : k₅ ≤ 1000) : (etcdAddrs k₅).Nodup :=
  etcd_restartN.restartNAddrs_nodup k₅ hk₅

/-- **Every address of the program is a literal.** -/
theorem etcdAddrs_lit (k₅ : Nat) (hk₅ : k₅ ≤ 1000) : ∀ a ∈ etcdAddrs k₅, netAddrLit a = true :=
  etcd_restartN.restartNAddrs_lit k₅ hk₅

/-- **Every address of the program is valid for the net extension** (`Net.addrOk`: every port is
below `32768`, Linux's ephemeral range; 2026-11-23, the listening tokens of the net extension's start). -/
theorem etcdAddrs_ok (k₅ : Nat) (hk₅ : k₅ ≤ 1000) : ∀ a ∈ etcdAddrs k₅, Net.addrOk a = true := by
  intro a ha
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  obtain ⟨i, hi, hp, -⟩ := etcd_restartN.member_port k₅ m hm
  rw [hp]
  exact addrOk_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

/-! ## Data directories: prefixes -/

/-- `a` starts with one of the prefixes `ts`. -/
def TagIn (ts : List GoString) (a : GoString) : Prop := ∃ t ∈ ts, t <+: a

/-- No prefix of `ts` is a prefix of one of `ts'`, or the other way round. -/
def TagsSep (ts ts' : List GoString) : Prop :=
  ∀ t ∈ ts, ∀ t' ∈ ts', ¬ t <+: t' ∧ ¬ t' <+: t

instance (ts ts' : List GoString) : Decidable (TagsSep ts ts') := by
  unfold TagsSep; infer_instance

instance (ts : List GoString) (a : GoString) : Decidable (TagIn ts a) := by
  unfold TagIn; infer_instance

theorem tagIn_sep (ts ts' : List GoString) (a : GoString) (hs : TagsSep ts ts')
    (h₁ : TagIn ts a) (h₂ : TagIn ts' a) : False := by
  obtain ⟨t, ht, h1⟩ := h₁
  obtain ⟨t', ht', h2⟩ := h₂
  rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
  · exact (hs t ht t' ht').1 h
  · exact (hs t ht t' ht').2 h

/-- The data directory of member `i` of a `k`-member cluster `pfx` starts with
`/tmp/etcd-grove-data/<pfx>-`. -/
theorem tagIn_memberAt (pfx : GoString) (pb cb i : w64) :
    TagIn [go!"/tmp/etcd-grove-data/" ++ pfx ++ go!"-"] (memberDataDir (memberAt pfx pb cb i).Name') :=
  ⟨_, List.mem_singleton_self _, ⟨decStr i ++ go!".etcd", by
    simp [memberDataDir, memberAt, List.append_assoc]⟩⟩

/-- The directory groups of `etcdDirs`, each with its prefixes. -/
def dirGroups (k₅ : Nat) : List (List GoString × List GoString) :=
  [(etcd_restartN.restartNDirs k₅, [go!"/tmp/etcd-grove-data/" ++ go!"restartN" ++ go!"-"]),
    ([go!"/tmp/etcd-grove-data/restart1.etcd"], [go!"/tmp/etcd-grove-data/restart1."])]

theorem dirLabels_sep (k₅ : Nat) : ((dirGroups k₅).map Prod.snd).Pairwise TagsSep := by
  show ([[go!"/tmp/etcd-grove-data/" ++ go!"restartN" ++ go!"-"],
    [go!"/tmp/etcd-grove-data/restart1."]] : List (List GoString)).Pairwise TagsSep
  decide +kernel

theorem etcdDirs_groups (k₅ : Nat) : etcdDirs k₅ = (dirGroups k₅).flatMap Prod.fst := by
  simp [etcdDirs, dirGroups]

/-- **The program's data directories are distinct.** -/
theorem etcdDirs_nodup (k₅ : Nat) (hk₅ : k₅ ≤ 1000) : (etcdDirs k₅).Nodup := by
  rw [etcdDirs_groups]
  refine nodup_groups TagIn TagsSep tagIn_sep _ ?_ (dirLabels_sep k₅)
  intro g hg
  simp only [dirGroups, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨etcd_restartN.restartNDirs_nodup k₅ hk₅, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := etcd_restartN.members_mem k₅ m hm
    exact tagIn_memberAt _ _ _ _
  · exact ⟨by decide +kernel, by decide +kernel⟩

/-! ## The start list, and its addresses and directories up to order -/

/-- **The program's members**: restartN's, then restart1's. -/
def etcdStarts (k₅ : Nat) : List (GoString × MemberAddrs) :=
  etcd_restartN.startAddrs k₅ ++ [(etcd_restart1.name, ⟨none, none⟩)]

/-- **The program's bridges**: none. -/
def etcdBridges : List GoString := []

/-- **The members' addresses and the bridges' are the program's, up to order.** -/
theorem etcdAddrs_perm (k₅ : Nat) :
    ((etcdStarts k₅).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      etcdBridges).Perm (etcdAddrs k₅) := by
  have h9 : ([(etcd_restart1.name, (⟨none, none⟩ : MemberAddrs))] : List (GoString × MemberAddrs)).flatMap
      (fun (m : GoString × MemberAddrs) => m.2.addrs) = [] := rfl
  unfold etcdStarts etcdBridges etcdAddrs
  simp only [List.flatMap_append]
  rw [h9, List.append_nil]
  exact etcd_restartN.restartNAddrs_perm k₅

/-- **The members' data directories are the program's, up to order.** -/
theorem etcdDirs_perm (k₅ : Nat) :
    ((etcdStarts k₅).map
      (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm (etcdDirs k₅) := by
  have h9 : ([(etcd_restart1.name, (⟨none, none⟩ : MemberAddrs))] : List (GoString × MemberAddrs)).map
      (fun (m : GoString × MemberAddrs) => memberDataDir m.1) =
      [go!"/tmp/etcd-grove-data/restart1.etcd"] := by decide +kernel
  unfold etcdStarts etcdDirs
  simp only [List.map_append]
  rw [h9]
  exact (etcd_restartN.restartNDirs_perm k₅).append (List.Perm.refl _)

/-- (wal-fsfix2) The members' names are at most 200 bytes (`etcd_adequate_members_below`'s `hmsL`). -/
theorem etcdStarts_names_len (k₅ : Nat) : ∀ m ∈ etcdStarts k₅, m.1.length ≤ 200 := by
  intro m hm
  simp only [etcdStarts, List.mem_append] at hm
  rcases hm with h | h
  · exact etcd_restartN.startAddrs_names_len k₅ m h
  · revert m; decide

end pure

end etcd_all
end EtcdGrove
end Perennial
