/- Lean-first (no Rocq counterpart).

# `k8s/all`: the two clusters' addresses and data directories are disjoint

The pure premises of `etcd_adequate_alloc_members` at the program of the one closed Kubernetes theorem
(`notes/k8s-unified-scope.md`, §3.3; `notes/k8s-compactor-n-plan.md`): the members are the store
cluster's (`k8s_etcd3N.startAddrs k₁`) then the compactor cluster's (`k8s_compactorN.startAddrs k₂`),
the other addresses their bridges. Every store-cluster address is `127.0.0.1:<p>` with
`20000 ≤ p < 23000` (`k8s_etcd3N.addr_port`), every compactor-cluster one with `23000 ≤ p < 26000`
(`k8s_compactorN.addr_port`): the address lists are disjoint (`k8sAddrs_nodup`). Every store-cluster
data directory is a member named `k8setcd3N-i`, every compactor-cluster one `k8scompactorN-j`
(`k8sDirs_nodup`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.TopLevelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI go_etcd_io.raft.v3 etcdstart

section pure

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet

/-- **The program's addresses are distinct.** -/
theorem k8sAddrs_nodup (k₁ k₂ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000) :
    (k8sAddrs k₁ k₂).Nodup := by
  unfold k8sAddrs
  refine List.nodup_append.2 ⟨k8s_etcd3N.k8setcd3NAddrs_nodup k₁ hk₁,
    k8s_compactorN.k8scompactorNAddrs_nodup k₂ hk₂, ?_⟩
  intro a ha c hc e
  subst e
  obtain ⟨b, i, hb, hi, rfl⟩ := k8s_etcd3N.addr_port k₁ _ ha
  obtain ⟨b', i', hb', hi', he⟩ := k8s_compactorN.addr_port k₂ _ hc
  have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left he))
  simp [W64] at this
  omega

theorem k8sAddrs_lit (k₁ k₂ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000) :
    ∀ a ∈ k8sAddrs k₁ k₂, netAddrLit a = true := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact k8s_etcd3N.k8setcd3NAddrs_lit k₁ hk₁ a h
  · exact k8s_compactorN.k8scompactorNAddrs_lit k₂ hk₂ a h

/-- **The program's addresses are valid for the net extension** (`Net.addrOk`, 2026-11-23: the
single-process theorem over `etcdNetExts` takes their listening tokens from the extension's start):
every port is in `[20000, 26000)` (`addr_port`), below Linux's ephemeral range (`addrOk_loopback`). -/
theorem k8sAddrs_ok (k₁ k₂ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000) :
    ∀ a ∈ k8sAddrs k₁ k₂, Net.addrOk a = true := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨b, i, hb, hi, rfl⟩ := k8s_etcd3N.addr_port k₁ a h
    exact addrOk_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)
  · obtain ⟨b, i, hb, hi, rfl⟩ := k8s_compactorN.addr_port k₂ a h
    exact addrOk_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

/-- `(a ++ b) ++ (c ++ d)` is `(a ++ c) ++ (b ++ d)` up to order. -/
theorem perm_middle4 {α : Type _} (a b c d : List α) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left a ?_
  simp only [← List.append_assoc]
  exact List.Perm.append_right d List.perm_append_comm

/-- **The members' addresses and the bridges' are the program's, up to order.** -/
theorem k8sAddrs_perm (k₁ k₂ : Nat) :
    ((k8s_etcd3N.startAddrs k₁ ++ k8s_compactorN.startAddrs k₂).flatMap
        (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      (k8s_etcd3N.bridges k₁ ++ k8s_compactorN.bridges k₂)).Perm (k8sAddrs k₁ k₂) := by
  rw [List.flatMap_append]
  refine (perm_middle4 _ _ _ _).trans ?_
  unfold k8sAddrs
  exact List.Perm.append (k8s_etcd3N.k8setcd3NAddrs_perm k₁) (k8s_compactorN.k8scompactorNAddrs_perm k₂)

/-- A store-cluster member's name. -/
theorem storeName (k : Nat) (m : GMember) (hm : m ∈ k8s_etcd3N.members k) :
    ∃ i : w64, m.Name' = go!"k8setcd3N" ++ go!"-" ++ decStr i := by
  obtain ⟨i, -, rfl⟩ := k8s_etcd3N.members_mem k m hm
  exact ⟨_, rfl⟩

/-- A compactor-cluster member's name. -/
theorem compactorName (k : Nat) (m : GMember) (hm : m ∈ k8s_compactorN.members k) :
    ∃ i : w64, m.Name' = go!"k8scompactorN" ++ go!"-" ++ decStr i := by
  obtain ⟨i, -, rfl⟩ := k8s_compactorN.members_mem k m hm
  exact ⟨_, rfl⟩

/-- **The program's data directories are distinct.** -/
theorem k8sDirs_nodup (k₁ k₂ : Nat) (hk₁ : k₁ ≤ 1000) (hk₂ : k₂ ≤ 1000) :
    (k8sDirs k₁ k₂).Nodup := by
  unfold k8sDirs
  refine List.nodup_append.2 ⟨k8s_etcd3N.k8setcd3NDirs_nodup k₁ hk₁,
    k8s_compactorN.k8scompactorNDirs_nodup k₂ hk₂, ?_⟩
  intro a ha c hc e
  subst e
  unfold k8s_etcd3N.k8setcd3NDirs at ha
  unfold k8s_compactorN.k8scompactorNDirs at hc
  obtain ⟨m, hm, he⟩ := List.mem_map.1 ha
  obtain ⟨m', hm', he'⟩ := List.mem_map.1 hc
  obtain ⟨i, hi⟩ := storeName k₁ m hm
  obtain ⟨i', hi'⟩ := compactorName k₂ m' hm'
  rw [← he', hi, hi'] at he
  have h := congrArg (List.take 4) (memberDataDir_inj he)
  simp only [List.append_assoc] at h
  rw [List.take_append_of_le_length (by decide), List.take_append_of_le_length (by decide)] at h
  exact absurd h (by decide)

/-- **The members' data directories are the program's, up to order.** -/
theorem k8sDirs_perm (k₁ k₂ : Nat) :
    ((k8s_etcd3N.startAddrs k₁ ++ k8s_compactorN.startAddrs k₂).map
        (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm (k8sDirs k₁ k₂) := by
  rw [List.map_append]
  unfold k8sDirs
  exact List.Perm.append (k8s_etcd3N.k8setcd3NDirs_perm k₁) (k8s_compactorN.k8scompactorNDirs_perm k₂)

end pure

end k8s_all
end EtcdGrove
end Perennial
