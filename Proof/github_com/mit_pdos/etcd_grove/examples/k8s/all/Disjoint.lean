/- Lean-first (no Rocq counterpart).

# `k8s/all`: the two clusters' addresses and data directories are disjoint

The pure premises of `etcd_adequate_alloc_members` at the program of the one closed Kubernetes theorem
(`notes/k8s-unified-scope.md`, §3.3): the members are the store cluster's (`k8s_etcd3N.startAddrs k`)
then the compactor cluster's (`cluster3.members k8s_compactor.clusterCfg`), the other addresses their
bridges. Every store-cluster address is `127.0.0.1:<p>` with `20000 ≤ p < 23000` (`addr_port`), every
compactor-cluster address one of nine literals with ports from 23931 (`compactorAddrs_port`): the
address lists are disjoint (`k8sAddrs_nodup`). Every store-cluster data directory is a member named
`k8setcd3N-i`, every compactor-cluster one `k8scompactorp-j` (`k8sDirs_nodup`).
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

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs

/-- The decimal form of a five-digit number, digit by digit. -/
theorem decStr_five (n : Nat) (h1 : 10000 ≤ n) (h2 : n < 100000) :
    decStr (W64 (n : Int)) = (baseDigits 10 (by omega) n).map digitChar := by
  rw [decStr_eq]
  congr 2
  simp [W64]
  omega

/-- **The compactor cluster's addresses**: `127.0.0.1:<p>`, `p` from 23931 to 23953. -/
theorem compactorAddrs_port (a : GoString) (ha : a ∈ k8sCompactorAddrs) :
    ∃ p : Nat, 23931 ≤ p ∧ p ≤ 23953 ∧ a = go!"127.0.0.1:" ++ decStr (W64 (p : Int)) := by
  unfold k8sCompactorAddrs at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨23941, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23942, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23943, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23931, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23932, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23933, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23951, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23952, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩
  · exact ⟨23953, by omega, by omega, by rw [decStr_five _ (by omega) (by omega)]; simp [baseDigits, digitChar]⟩

theorem compactorAddrs_nodup : k8sCompactorAddrs.Nodup := by
  unfold k8sCompactorAddrs; decide

theorem compactorAddrs_lit : ∀ a ∈ k8sCompactorAddrs, netAddrLit a = true := by
  unfold k8sCompactorAddrs; decide

/-- **The program's addresses are distinct.** -/
theorem k8sAddrs_nodup (k : Nat) (hk : k ≤ 1000) : (k8sAddrs k).Nodup := by
  unfold k8sAddrs
  refine List.nodup_append.2 ⟨k8s_etcd3N.k8setcd3NAddrs_nodup k hk, compactorAddrs_nodup, ?_⟩
  intro a ha c hc e
  subst e
  obtain ⟨b, i, hb, hi, rfl⟩ := k8s_etcd3N.addr_port k _ ha
  obtain ⟨p, hp1, hp2, he⟩ := compactorAddrs_port _ hc
  have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left he))
  simp [W64] at this
  omega

theorem k8sAddrs_lit (k : Nat) (hk : k ≤ 1000) : ∀ a ∈ k8sAddrs k, netAddrLit a = true := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact k8s_etcd3N.k8setcd3NAddrs_lit k hk a h
  · exact compactorAddrs_lit a h

/-- `(a ++ b) ++ (c ++ d)` is `(a ++ c) ++ (b ++ d)` up to order. -/
theorem perm_middle4 {α : Type _} (a b c d : List α) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left a ?_
  simp only [← List.append_assoc]
  exact List.Perm.append_right d List.perm_append_comm

theorem compactorAddrs_perm :
    ((cluster3.members k8s_compactor.clusterCfg).flatMap
        (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      cluster3.bridges k8s_compactor.clusterCfg).Perm k8sCompactorAddrs := by
  decide

/-- **The members' addresses and the bridges' are the program's, up to order.** -/
theorem k8sAddrs_perm (k : Nat) :
    ((k8s_etcd3N.startAddrs k ++ cluster3.members k8s_compactor.clusterCfg).flatMap
        (fun (m : GoString × MemberAddrs) => m.2.addrs) ++
      (k8s_etcd3N.bridges k ++ cluster3.bridges k8s_compactor.clusterCfg)).Perm (k8sAddrs k) := by
  rw [List.flatMap_append]
  refine (perm_middle4 _ _ _ _).trans ?_
  unfold k8sAddrs
  exact List.Perm.append (k8s_etcd3N.k8setcd3NAddrs_perm k) compactorAddrs_perm

theorem compactorDirs_nodup : k8sCompactorDirs.Nodup := by
  unfold k8sCompactorDirs; decide

/-- A store-cluster member's name. -/
theorem storeName (k : Nat) (m : GMember) (hm : m ∈ k8s_etcd3N.members k) :
    ∃ i : w64, m.Name' = go!"k8setcd3N" ++ go!"-" ++ decStr i := by
  obtain ⟨i, -, rfl⟩ := k8s_etcd3N.members_mem k m hm
  exact ⟨_, rfl⟩

/-- **The program's data directories are distinct.** -/
theorem k8sDirs_nodup (k : Nat) (hk : k ≤ 1000) : (k8sDirs k).Nodup := by
  unfold k8sDirs
  refine List.nodup_append.2 ⟨k8s_etcd3N.k8setcd3NDirs_nodup k hk, compactorDirs_nodup, ?_⟩
  intro a ha c hc e
  subst e
  unfold k8s_etcd3N.k8setcd3NDirs at ha
  obtain ⟨m, hm, he⟩ := List.mem_map.1 ha
  obtain ⟨i, hi⟩ := storeName k m hm
  unfold k8sCompactorDirs at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h <;> rw [h, hi] at he <;> have := memberDataDir_inj he <;>
    simp at this

/-- **The members' data directories are the program's, up to order.** -/
theorem k8sDirs_perm (k : Nat) :
    ((k8s_etcd3N.startAddrs k ++ cluster3.members k8s_compactor.clusterCfg).map
        (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm (k8sDirs k) := by
  rw [List.map_append]
  unfold k8sDirs
  exact List.Perm.append (k8s_etcd3N.k8setcd3NDirs_perm k) (List.Perm.refl _)

end pure

end k8s_all
end EtcdGrove
end Perennial
