/- Lean-first (no Rocq counterpart).

# `etcd/all`: the eleven clusters' addresses and data directories are distinct

`etcd_adequate_members_below`'s premises for `etcdProgram` (`Adequacy.lean`): the program's start list
`etcdStarts` (the eleven clusters' members, in the order of `etcdAddrs`) and bridges `etcdBridges`; the
address list `etcdAddrs` and the data-directory list `etcdDirs` without duplicates; both up to order the
start list's; every address a literal; every member name at most 200 bytes.

Distinctness across clusters by one lemma over groups (`nodup_groups`: a list of groups, each without
duplicates and labelled, whose labels are pairwise separated, concatenates to a list without
duplicates): an address group's label is the port intervals its addresses `127.0.0.1:<p>` lie in
(`PortIn`), a directory group's the prefixes its directories start with (`TagIn`); the labels' pairwise
separation is decided. Within a cluster, the drivers' own `_nodup` lemmas (or `decide`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes

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

/-! ## Addresses: port intervals -/

/-- The address `127.0.0.1:<p>`. -/
abbrev addrOf (p : Nat) : GoString := go!"127.0.0.1:" ++ decStr (W64 (p : Int))

/-- `a` is `127.0.0.1:<p>` for a port `p` in one of the intervals `ivs` (`[lo, hi)`). -/
def PortIn (ivs : List (Nat × Nat)) (a : GoString) : Prop :=
  ∃ p, p < 65536 ∧ (∃ iv ∈ ivs, iv.1 ≤ p ∧ p < iv.2) ∧ a = addrOf p

/-- No interval of `l₁` meets one of `l₂`. -/
def IvsSep (l₁ l₂ : List (Nat × Nat)) : Prop :=
  ∀ iv ∈ l₁, ∀ iv' ∈ l₂, iv.2 ≤ iv'.1 ∨ iv'.2 ≤ iv.1

instance (l₁ l₂ : List (Nat × Nat)) : Decidable (IvsSep l₁ l₂) := by
  unfold IvsSep; infer_instance

theorem addrOf_inj {p q : Nat} (hp : p < 65536) (hq : q < 65536) (h : addrOf p = addrOf q) :
    p = q := by
  have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left h))
  simp [W64] at this
  omega

theorem portIn_sep (l₁ l₂ : List (Nat × Nat)) (a : GoString) (hs : IvsSep l₁ l₂)
    (h₁ : PortIn l₁ a) (h₂ : PortIn l₂ a) : False := by
  obtain ⟨p, hp, ⟨iv, hiv, h1, h2⟩, rfl⟩ := h₁
  obtain ⟨q, hq, ⟨iv', hiv', h3, h4⟩, he⟩ := h₂
  have := addrOf_inj hp hq he
  subst this
  rcases hs iv hiv iv' hiv' with h | h <;> omega

/-- A literal group: its addresses are among `ps`'s, each port in one of the intervals. -/
theorem portIn_lits (L : List GoString) (ps : List Nat) (ivs : List (Nat × Nat))
    (hL : ∀ a ∈ L, a ∈ ps.map addrOf)
    (hps : ∀ p ∈ ps, p < 65536 ∧ ∃ iv ∈ ivs, iv.1 ≤ p ∧ p < iv.2) :
    ∀ a ∈ L, PortIn ivs a := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hL a ha)
  exact ⟨p, (hps p hp).1, (hps p hp).2, rfl⟩

/-- A `k`-member group: its addresses are `b + i` with `i < k`, `b` in `[lo, hi - 1000]`. -/
theorem portIn_range (lo hi k b i : Nat) (hk : k ≤ 1000) (hb1 : lo ≤ b) (hb2 : b + 1000 ≤ hi)
    (hhi : hi ≤ 65536) (hik : i < k) : PortIn [(lo, hi)] (addrOf (b + i)) :=
  ⟨b + i, by omega, ⟨(lo, hi), List.mem_singleton_self _, by simp; omega, by simp; omega⟩, rfl⟩

/-- The three one-member clusters' client addresses (compactwatch's, compacted's, cache's). -/
abbrev kvLitAddrs : List GoString :=
  [go!"127.0.0.1:23794", go!"127.0.0.1:23791", go!"127.0.0.1:23873"]

/-- The address groups of `etcdAddrs`, each with its port intervals. -/
def addrGroups (k₁ k₂ k₃ k₄ k₅ : Nat) : List (List GoString × List (Nat × Nat)) :=
  [(etcd_txnlinfaultsN.txnlinfaultsNAddrs k₁, [(26000, 29000)]),
    (linkv3pAddrs, [(23831, 23854)]),
    (kvLitAddrs, [(23791, 23792), (23794, 23795), (23873, 23874)]),
    (etcd_authN.authNAddrs k₂, [(29000, 31000)]),
    (etcd_authlease.authleaseAddrs k₃, [(16000, 18000)]),
    (etcd_leaseN.leaseNAddrs k₄, [(10000, 12000)]),
    (leasecatchupAddrs, [(24011, 24034)]),
    (etcd_restartN.restartNAddrs k₅, [(14000, 15000)])]

theorem addrLabels_sep (k₁ k₂ k₃ k₄ k₅ : Nat) :
    ((addrGroups k₁ k₂ k₃ k₄ k₅).map Prod.snd).Pairwise IvsSep := by
  show ([[(26000, 29000)], [(23831, 23854)], [(23791, 23792), (23794, 23795), (23873, 23874)],
    [(29000, 31000)], [(16000, 18000)], [(10000, 12000)], [(24011, 24034)], [(14000, 15000)]] :
      List (List (Nat × Nat))).Pairwise IvsSep
  decide

theorem etcdAddrs_groups (k₁ k₂ k₃ k₄ k₅ : Nat) :
    etcdAddrs k₁ k₂ k₃ k₄ k₅ = (addrGroups k₁ k₂ k₃ k₄ k₅).flatMap Prod.fst := by
  simp [etcdAddrs, addrGroups, List.append_assoc]

/-- **The program's addresses are distinct.** -/
theorem etcdAddrs_nodup (k₁ k₂ k₃ k₄ k₅ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000)
    (hk₃ : k₃ ≤ 1000) (hk₄ : k₄ ≤ 1000) (hk₅ : k₅ ≤ 1000) :
    (etcdAddrs k₁ k₂ k₃ k₄ k₅).Nodup := by
  rw [etcdAddrs_groups]
  refine nodup_groups PortIn IvsSep portIn_sep _ ?_ (addrLabels_sep k₁ k₂ k₃ k₄ k₅)
  intro g hg
  simp only [addrGroups, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨etcd_txnlinfaultsN.txnlinfaultsNAddrs_nodup k₁ hk₁, fun a ha => ?_⟩
    obtain ⟨b, i, hb, hi, rfl⟩ := etcd_txnlinfaultsN.addr_port k₁ a ha
    exact portIn_range 26000 29000 k₁ b i hk₁ (by omega) (by omega) (by omega) hi
  · refine ⟨by decide, portIn_lits _ [23831, 23832, 23833, 23841, 23842, 23843, 23851, 23852, 23853]
      _ (by decide +kernel) (by decide)⟩
  · refine ⟨by decide, portIn_lits _ [23791, 23794, 23873] _ (by decide +kernel) (by decide)⟩
  · refine ⟨etcd_authN.authNAddrs_nodup k₂ hk₂, fun a ha => ?_⟩
    obtain ⟨b, i, hb, hi, rfl⟩ := etcd_authN.addr_port k₂ a ha
    exact portIn_range 29000 31000 k₂ b i hk₂ (by omega) (by omega) (by omega) hi
  · refine ⟨etcd_authlease.authleaseAddrs_nodup k₃ hk₃, fun a ha => ?_⟩
    obtain ⟨b, i, hb, hi, rfl⟩ := etcd_authlease.addr_port k₃ a ha
    exact portIn_range 16000 18000 k₃ b i hk₃ (by omega) (by omega) (by omega) hi
  · refine ⟨etcd_leaseN.leaseNAddrs_nodup k₄ hk₄, fun a ha => ?_⟩
    obtain ⟨b, i, hb, hi, rfl⟩ := etcd_leaseN.addr_port k₄ a ha
    exact portIn_range 10000 12000 k₄ b i hk₄ (by omega) (by omega) (by omega) hi
  · refine ⟨by decide, portIn_lits _ [24011, 24012, 24013, 24021, 24022, 24023, 24031, 24032, 24033]
      _ (by decide +kernel) (by decide)⟩
  · refine ⟨etcd_restartN.restartNAddrs_nodup k₅ hk₅, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, hi, hp, -⟩ := etcd_restartN.member_port k₅ m hm
    rw [hp]
    exact portIn_range 14000 15000 k₅ 14000 i hk₅ (by omega) (by omega) (by omega) hi

/-- **Every address of the program is a literal.** -/
theorem etcdAddrs_lit (k₁ k₂ k₃ k₄ k₅ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000)
    (hk₃ : k₃ ≤ 1000) (hk₄ : k₄ ≤ 1000) (hk₅ : k₅ ≤ 1000) :
    ∀ a ∈ etcdAddrs k₁ k₂ k₃ k₄ k₅, netAddrLit a = true := by
  intro a ha
  rw [etcdAddrs_groups] at ha
  obtain ⟨g, hg, ha⟩ := List.mem_flatMap.1 ha
  simp only [addrGroups, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact etcd_txnlinfaultsN.txnlinfaultsNAddrs_lit k₁ hk₁ a ha
  · exact (show ∀ x ∈ (linkv3pAddrs : List GoString), netAddrLit x = true by decide) a ha
  · exact (show ∀ x ∈ kvLitAddrs, netAddrLit x = true by decide) a ha
  · exact etcd_authN.authNAddrs_lit k₂ hk₂ a ha
  · exact etcd_authlease.authleaseAddrs_lit k₃ hk₃ a ha
  · exact etcd_leaseN.leaseNAddrs_lit k₄ hk₄ a ha
  · exact (show ∀ x ∈ (leasecatchupAddrs : List GoString), netAddrLit x = true by decide) a ha
  · exact etcd_restartN.restartNAddrs_lit k₅ hk₅ a ha

/-- `127.0.0.1:<p>` is valid for the net extension (`Net.addrOk`) for a port `1 ≤ p < 32768`. -/
theorem addrOf_ok (p : Nat) (h1 : 1 ≤ p) (h2 : p < 32768) : Net.addrOk (addrOf p) = true :=
  addrOk_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

/-- **Every address of the program is valid for the net extension** (`Net.addrOk`: every port is
below `32768`, Linux's ephemeral range; 2026-11-23, the listening tokens of the net extension's start). -/
theorem etcdAddrs_ok (k₁ k₂ k₃ k₄ k₅ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000)
    (hk₃ : k₃ ≤ 1000) (hk₄ : k₄ ≤ 1000) (hk₅ : k₅ ≤ 1000) :
    ∀ a ∈ etcdAddrs k₁ k₂ k₃ k₄ k₅, Net.addrOk a = true := by
  intro a ha
  rw [etcdAddrs_groups] at ha
  obtain ⟨g, hg, ha⟩ := List.mem_flatMap.1 ha
  simp only [addrGroups, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨b, i, hb, hi, rfl⟩ := etcd_txnlinfaultsN.addr_port k₁ a ha
    exact addrOf_ok (b + i) (by omega) (by omega)
  · exact (show ∀ x ∈ (linkv3pAddrs : List GoString), Net.addrOk x = true by decide) a ha
  · exact (show ∀ x ∈ kvLitAddrs, Net.addrOk x = true by decide) a ha
  · obtain ⟨b, i, hb, hi, rfl⟩ := etcd_authN.addr_port k₂ a ha
    exact addrOf_ok (b + i) (by omega) (by omega)
  · obtain ⟨b, i, hb, hi, rfl⟩ := etcd_authlease.addr_port k₃ a ha
    exact addrOf_ok (b + i) (by omega) (by omega)
  · obtain ⟨b, i, hb, hi, rfl⟩ := etcd_leaseN.addr_port k₄ a ha
    exact addrOf_ok (b + i) (by omega) (by omega)
  · exact (show ∀ x ∈ (leasecatchupAddrs : List GoString), Net.addrOk x = true by decide) a ha
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, hi, hp, -⟩ := etcd_restartN.member_port k₅ m hm
    rw [hp]
    exact addrOf_ok (14000 + i) (by omega) (by omega)

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

/-- The three one-member KV clusters' data directories. -/
abbrev kvLitDirs : List GoString :=
  [go!"/tmp/etcd-grove-data/compactkv.etcd", go!"/tmp/etcd-grove-data/putgetc.etcd",
    go!"/tmp/etcd-grove-data/cachekv.etcd"]

/-- The directory groups of `etcdDirs`, each with its prefixes. -/
def dirGroups (k₁ k₂ k₃ k₄ k₅ : Nat) : List (List GoString × List GoString) :=
  [(etcd_txnlinfaultsN.txnlinfaultsNDirs k₁, [go!"/tmp/etcd-grove-data/" ++ go!"txnlinfaultsN" ++ go!"-"]),
    ([memberDataDir etcd_partition.name₁, memberDataDir etcd_partition.name₂,
      memberDataDir etcd_partition.name₃], [go!"/tmp/etcd-grove-data/linkv3p-"]),
    (kvLitDirs, [go!"/tmp/etcd-grove-data/compactkv.", go!"/tmp/etcd-grove-data/putgetc.",
      go!"/tmp/etcd-grove-data/cachekv."]),
    (etcd_authN.authNDirs k₂, [go!"/tmp/etcd-grove-data/" ++ go!"authN" ++ go!"-"]),
    (etcd_authlease.authleaseDirs k₃, [go!"/tmp/etcd-grove-data/" ++ go!"authlease" ++ go!"-"]),
    (etcd_leaseN.leaseNDirs k₄, [go!"/tmp/etcd-grove-data/" ++ go!"leaseN" ++ go!"-"]),
    (leasecatchupDataDirs, [go!"/tmp/etcd-grove-data/leasecatchup-"]),
    (etcd_restartN.restartNDirs k₅, [go!"/tmp/etcd-grove-data/" ++ go!"restartN" ++ go!"-"]),
    ([go!"/tmp/etcd-grove-data/restart1.etcd"], [go!"/tmp/etcd-grove-data/restart1."])]

theorem dirLabels_sep (k₁ k₂ k₃ k₄ k₅ : Nat) :
    ((dirGroups k₁ k₂ k₃ k₄ k₅).map Prod.snd).Pairwise TagsSep := by
  show ([[go!"/tmp/etcd-grove-data/" ++ go!"txnlinfaultsN" ++ go!"-"],
    [go!"/tmp/etcd-grove-data/linkv3p-"],
    [go!"/tmp/etcd-grove-data/compactkv.", go!"/tmp/etcd-grove-data/putgetc.",
      go!"/tmp/etcd-grove-data/cachekv."],
    [go!"/tmp/etcd-grove-data/" ++ go!"authN" ++ go!"-"],
    [go!"/tmp/etcd-grove-data/" ++ go!"authlease" ++ go!"-"],
    [go!"/tmp/etcd-grove-data/" ++ go!"leaseN" ++ go!"-"],
    [go!"/tmp/etcd-grove-data/leasecatchup-"],
    [go!"/tmp/etcd-grove-data/" ++ go!"restartN" ++ go!"-"],
    [go!"/tmp/etcd-grove-data/restart1."]] : List (List GoString)).Pairwise TagsSep
  decide +kernel

theorem etcdDirs_groups (k₁ k₂ k₃ k₄ k₅ : Nat) :
    etcdDirs k₁ k₂ k₃ k₄ k₅ = (dirGroups k₁ k₂ k₃ k₄ k₅).flatMap Prod.fst := by
  simp [etcdDirs, dirGroups, List.append_assoc]

/-- **The program's data directories are distinct.** -/
theorem etcdDirs_nodup (k₁ k₂ k₃ k₄ k₅ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000)
    (hk₃ : k₃ ≤ 1000) (hk₄ : k₄ ≤ 1000) (hk₅ : k₅ ≤ 1000) :
    (etcdDirs k₁ k₂ k₃ k₄ k₅).Nodup := by
  rw [etcdDirs_groups]
  refine nodup_groups TagIn TagsSep tagIn_sep _ ?_ (dirLabels_sep k₁ k₂ k₃ k₄ k₅)
  intro g hg
  simp only [dirGroups, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨etcd_txnlinfaultsN.txnlinfaultsNDirs_nodup k₁ hk₁, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := etcd_txnlinfaultsN.members_mem k₁ m hm
    exact tagIn_memberAt _ _ _ _
  · exact ⟨by decide +kernel, by decide +kernel⟩
  · exact ⟨by decide +kernel, by decide +kernel⟩
  · refine ⟨etcd_authN.authNDirs_nodup k₂ hk₂, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := etcd_authN.members_mem k₂ m hm
    exact tagIn_memberAt _ _ _ _
  · refine ⟨etcd_authlease.authleaseDirs_nodup k₃ hk₃, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := etcd_authlease.members_mem k₃ m hm
    exact tagIn_memberAt _ _ _ _
  · refine ⟨etcd_leaseN.leaseNDirs_nodup k₄ hk₄, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := etcd_leaseN.members_mem k₄ m hm
    exact tagIn_memberAt _ _ _ _
  · exact ⟨by decide +kernel, by decide +kernel⟩
  · refine ⟨etcd_restartN.restartNDirs_nodup k₅ hk₅, fun a ha => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, -, rfl⟩ := etcd_restartN.members_mem k₅ m hm
    exact tagIn_memberAt _ _ _ _
  · exact ⟨by decide +kernel, by decide +kernel⟩

/-! ## The start list, and its addresses and directories up to order -/

/-- The three one-member KV clusters' start entries (compactwatch's, compacted's, cache's). -/
abbrev kvStarts : List (GoString × MemberAddrs) :=
  [(go!"compactkv", ⟨none, some go!"127.0.0.1:23794"⟩), (go!"putgetc", ⟨none, some go!"127.0.0.1:23791"⟩),
    (go!"cachekv", ⟨none, some go!"127.0.0.1:23873"⟩)]

/-- **The program's members**, cluster by cluster in the order of `etcdAddrs`. -/
def etcdStarts (k₁ k₂ k₃ k₄ k₅ : Nat) : List (GoString × MemberAddrs) :=
  etcd_txnlinfaultsN.startAddrs k₁ ++ cluster3.members etcd_partition.clusterCfg ++ kvStarts ++
    etcd_authN.startAddrs k₂ ++ etcd_authlease.startAddrs k₃ ++ etcd_leaseN.startAddrs k₄ ++
    cluster3.members etcd_leasecatchup.clusterCfg ++ etcd_restartN.startAddrs k₅ ++
    [(etcd_restart1.name, ⟨none, none⟩)]

/-- **The program's bridges**: txnlinfaultsN's, partition's, leasecatchup's. -/
def etcdBridges (k₁ : Nat) : List GoString :=
  etcd_txnlinfaultsN.bridges k₁ ++ cluster3.bridges etcd_partition.clusterCfg ++
    cluster3.bridges etcd_leasecatchup.clusterCfg

theorem perm_rearrange {α : Type _} [DecidableEq α] (A1 A2 A3 A4 A5 A6 A7 A8 B1 B2 B3 : List α) :
    ((A1 ++ A2 ++ A3 ++ A4 ++ A5 ++ A6 ++ A7 ++ A8 ++ []) ++ (B1 ++ B2 ++ B3)).Perm
      ((A1 ++ B1) ++ (A2 ++ B2) ++ A3 ++ (A4 ++ []) ++ (A5 ++ []) ++ (A6 ++ []) ++ (A7 ++ B3) ++
        (A8 ++ [])) :=
  List.perm_iff_count.2 (fun a => by simp only [List.count_append, List.count_nil]; omega)

/-- **The members' addresses and the bridges' are the program's, up to order.** -/
theorem etcdAddrs_perm (k₁ k₂ k₃ k₄ k₅ : Nat) :
    ((etcdStarts k₁ k₂ k₃ k₄ k₅).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      etcdBridges k₁).Perm (etcdAddrs k₁ k₂ k₃ k₄ k₅) := by
  have h2 : ((cluster3.members etcd_partition.clusterCfg).flatMap
      (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      cluster3.bridges etcd_partition.clusterCfg).Perm linkv3pAddrs := by decide
  have h7 : ((cluster3.members etcd_leasecatchup.clusterCfg).flatMap
      (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      cluster3.bridges etcd_leasecatchup.clusterCfg).Perm leasecatchupAddrs := by decide
  have h3 : kvStarts.flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) = kvLitAddrs := rfl
  have h9 : ([(etcd_restart1.name, (⟨none, none⟩ : MemberAddrs))] : List (GoString × MemberAddrs)).flatMap
      (fun (m : GoString × MemberAddrs) => m.2.addrs) = [] := rfl
  unfold etcdStarts etcdBridges
  simp only [List.flatMap_append]
  rw [h3, h9]
  refine (perm_rearrange _ _ _ _ _ _ _ _ _ _ _).trans ?_
  unfold etcdAddrs
  exact (((((((etcd_txnlinfaultsN.txnlinfaultsNAddrs_perm k₁).append h2).append
    (List.Perm.refl _)).append (etcd_authN.authNAddrs_perm k₂)).append
    (etcd_authlease.authleaseAddrs_perm k₃)).append (etcd_leaseN.leaseNAddrs_perm k₄)).append h7).append
    (etcd_restartN.restartNAddrs_perm k₅)

/-- **The members' data directories are the program's, up to order.** -/
theorem etcdDirs_perm (k₁ k₂ k₃ k₄ k₅ : Nat) :
    ((etcdStarts k₁ k₂ k₃ k₄ k₅).map
      (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm (etcdDirs k₁ k₂ k₃ k₄ k₅) := by
  have h3 : kvStarts.map (fun (m : GoString × MemberAddrs) => memberDataDir m.1) = kvLitDirs := by
    decide +kernel
  have h9 : ([(etcd_restart1.name, (⟨none, none⟩ : MemberAddrs))] : List (GoString × MemberAddrs)).map
      (fun (m : GoString × MemberAddrs) => memberDataDir m.1) =
      [go!"/tmp/etcd-grove-data/restart1.etcd"] := by decide +kernel
  unfold etcdStarts etcdDirs
  simp only [List.map_append]
  rw [h3, h9]
  exact (((((((((etcd_txnlinfaultsN.txnlinfaultsNDirs_perm k₁).append (List.Perm.refl _)).append
    (List.Perm.refl _)).append (etcd_authN.authNDirs_perm k₂)).append
    (etcd_authlease.authleaseDirs_perm k₃)).append (etcd_leaseN.leaseNDirs_perm k₄)).append
    (List.Perm.refl _)).append (etcd_restartN.restartNDirs_perm k₅)).append (List.Perm.refl _))

/-- (wal-fsfix2) The members' names are at most 200 bytes (`etcd_adequate_members_below`'s `hmsL`). -/
theorem etcdStarts_names_len (k₁ k₂ k₃ k₄ k₅ : Nat) :
    ∀ m ∈ etcdStarts k₁ k₂ k₃ k₄ k₅, m.1.length ≤ 200 := by
  intro m hm
  simp only [etcdStarts, List.mem_append] at hm
  rcases hm with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact etcd_txnlinfaultsN.startAddrs_names_len k₁ m h
  · revert m; decide
  · revert m; decide
  · exact etcd_authN.startAddrs_names_len k₂ m h
  · exact etcd_authlease.startAddrs_names_len k₃ m h
  · exact etcd_leaseN.startAddrs_names_len k₄ m h
  · revert m; decide
  · exact etcd_restartN.startAddrs_names_len k₅ m h
  · revert m; decide

end pure

end etcd_all
end EtcdGrove
end Perennial
