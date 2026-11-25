/-
**leaseexpiryN's members, addresses and directory: the pure facts** (leaseexpiryN, `notes/leaseexpiryN-plan.md`, 2026-11-15).
Lean-first (no Rocq counterpart). txnlinfaultsN's (`txnlinfaultsN/Dir.lean`) without the bridges: for
`k ≤ 1000` members the names distinct and valid UTF-8, the peer addresses distinct plain peer URLs,
every address a loopback literal and the program's addresses (every member's peer and client
address) distinct (`etcd_adequate_members`' premises). The directory is putgetN's `dirN`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart
open etcd_putgetN (port_toNat loopback_plain loopback_plainEndpoint)

section pure
variable [GooseExts]

/-! ## The members' addresses -/

theorem members_mem (k : Nat) (m : GMember) (h : m ∈ members k) :
    ∃ i, i < k ∧ m = memberAt go!"leaseexpiryN" (W64 12000) (W64 13000) (W64 (i : Int)) := by
  unfold members membersOf at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  exact ⟨i, List.mem_range.1 hi, rfl⟩

theorem members_names_nodup (k : Nat) (hk : k ≤ 1000) : ((members k).map (·.Name')).Nodup :=
  membersOf_names_nodup _ k (by omega) _ _

theorem members_names_utf8 (k : Nat) : ∀ m ∈ members k, utf8Valid m.Name' := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact memberAt_name_utf8 _ (fun b hb => by revert b; decide) _ _ _

/-- The members' names are at most 200 bytes (wal-fsfix: their data directories fit). -/
theorem members_names_len (k : Nat) : ∀ m ∈ members k, m.Name'.length ≤ 200 := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact memberAt_name_len _ (by decide) _ _ _

theorem members_peers_nodup (k : Nat) (hk : k ≤ 1000) : ((members k).map (·.Peer')).Nodup := by
  unfold members membersOf
  rw [List.map_map]
  refine List.pairwise_map.2 (List.Pairwise.imp_of_mem ?_ List.nodup_range)
  intro i j hi hj hne h
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  simp only [Function.comp, memberAt] at h
  have h' := decStr_inj (List.append_cancel_left h)
  have := congrArg BitVec.toNat h'
  rw [show (W64 12000 : w64) = W64 ((12000 : Nat) : Int) from rfl,
    port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

theorem members_peer_plain (k : Nat) :
    ∀ m ∈ members k, types.plainPeerURL (go!"http://" ++ m.Peer') := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact loopback_plain _

/-- A member's addresses, by its index. -/
theorem member_port (k : Nat) (m : GMember) (hm : m ∈ members k) :
    ∃ i, i < k ∧ m.Peer' = go!"127.0.0.1:" ++ decStr (W64 ((12000 + i : Nat) : Int)) ∧
      m.Client' = go!"127.0.0.1:" ++ decStr (W64 ((13000 + i : Nat) : Int)) := by
  obtain ⟨i, hi, rfl⟩ := members_mem k m hm
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [memberAt] <;> congr 2 <;> apply BitVec.eq_of_toNat_eq <;>
    simp [W64] <;> omega

/-! ## The program's addresses and data directories (`etcd_adequate_members`' premises) -/

/-- **The program's addresses**: the peer addresses and the client addresses of the members `Main(k)`
starts (`cluster k`: none for a `k` outside `[1, 1000]`). -/
def leaseexpiryNAddrs (k : w64) : List GoString :=
  (cluster k).map (·.Peer') ++ (cluster k).map (·.Client')

/-- **The program's data directories**: the members' `leaseexpiryN-i.etcd`, of the members `Main(k)`
starts (`cluster k`). -/
def leaseexpiryNDirs (k : w64) : List GoString := (cluster k).map (fun m => memberDataDir m.Name')

/-- The program's start bundles, as `etcd_adequate_members` takes them. -/
def startAddrs (k : w64) : List (GoString × MemberAddrs) :=
  (startOf (cluster k)).map (fun m => (m.1, ⟨some m.2.1, m.2.2⟩))

/-- (wal-fsfix2) The start bundles' names are at most 200 bytes (`etcd_adequate_members`' `hmsL`). -/
theorem startAddrs_names_len (k : w64) : ∀ m ∈ startAddrs k, m.1.length ≤ 200 := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact members_names_len _ y (mem_cluster hy).1

theorem leaseexpiryNAddrs_perm (k : w64) :
    ((startAddrs k).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++ []).Perm
      (leaseexpiryNAddrs k) := by
  unfold startAddrs leaseexpiryNAddrs startOf
  rw [List.append_nil]
  generalize cluster k = ms
  induction ms with
  | nil => exact List.Perm.refl _
  | cons m r ih =>
    simp only [List.map_cons, List.flatMap_cons]
    show (m.Peer' :: m.Client' :: _).Perm (m.Peer' :: (r.map (·.Peer') ++ m.Client' :: r.map (·.Client')))
    refine List.Perm.cons _ ?_
    exact (List.Perm.cons _ ih).trans List.perm_middle.symm

theorem leaseexpiryNDirs_perm (k : w64) :
    ((startAddrs k).map (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm
      (leaseexpiryNDirs k) := by
  unfold startAddrs leaseexpiryNDirs startOf
  simp only [List.map_map]
  exact List.Perm.refl _

theorem leaseexpiryNDirs_nodup (k : w64) : (leaseexpiryNDirs k).Nodup := by
  unfold leaseexpiryNDirs
  rcases cluster_cases k with ⟨-, hk, he⟩ | he
  rotate_left
  · rw [he]; simp
  rw [he]
  rw [show (fun m : GMember => memberDataDir m.Name') = memberDataDir ∘ (·.Name') from rfl,
    ← List.map_map]
  exact List.Pairwise.map _ (fun a b h e => h (memberDataDir_inj e)) (members_names_nodup _ hk)

/-- Every address of the program is `127.0.0.1:<p>` with `p` in one of the two ranges. -/
theorem addr_port (k : w64) (a : GoString) (ha : a ∈ leaseexpiryNAddrs k) :
    ∃ b i, (b = 12000 ∨ b = 13000) ∧ i < 1000 ∧
      a = go!"127.0.0.1:" ++ decStr (W64 ((b + i : Nat) : Int)) := by
  unfold leaseexpiryNAddrs at ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨hm, hk⟩ := mem_cluster hm
    obtain ⟨i, hi, hp, -⟩ := member_port _ m hm
    exact ⟨12000, i, Or.inl rfl, by omega, hp⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨hm, hk⟩ := mem_cluster hm
    obtain ⟨i, hi, -, hc⟩ := member_port _ m hm
    exact ⟨13000, i, Or.inr rfl, by omega, hc⟩

theorem leaseexpiryNAddrs_lit (k : w64) :
    ∀ a ∈ leaseexpiryNAddrs k, netAddrLit a = true := by
  intro a ha
  obtain ⟨b, i, hb, hi, rfl⟩ := addr_port k a ha
  exact netAddrLit_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

theorem members_clients_nodup (k : Nat) (hk : k ≤ 1000) : ((members k).map (·.Client')).Nodup := by
  unfold members membersOf
  rw [List.map_map]
  refine List.pairwise_map.2 (List.Pairwise.imp_of_mem ?_ List.nodup_range)
  intro i j hi hj hne h
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  simp only [Function.comp, memberAt] at h
  have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left h))
  rw [show (W64 13000 : w64) = W64 ((13000 : Nat) : Int) from rfl,
    port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

theorem members_client_plain (k : Nat) : ∀ m ∈ members k, plainEndpoint m.Client' := by
  intro m hm
  obtain ⟨i, -, -, hc⟩ := member_port k m hm
  rw [hc]; exact loopback_plainEndpoint _

theorem leaseexpiryNAddrs_nodup (k : w64) : (leaseexpiryNAddrs k).Nodup := by
  unfold leaseexpiryNAddrs
  rcases cluster_cases k with ⟨-, hk, he⟩ | he
  rotate_left
  · rw [he]; simp
  rw [he, List.nodup_append]
  refine ⟨members_peers_nodup _ hk, members_clients_nodup _ hk, ?_⟩
  intro a ha c hc e
  subst e
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  obtain ⟨m', hm', he⟩ := List.mem_map.1 hc
  obtain ⟨i, hi, hp, -⟩ := member_port _ m hm
  obtain ⟨j, hj, -, hc'⟩ := member_port _ m' hm'
  rw [hp, hc'] at he
  have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left he))
  simp [W64] at this
  omega

end pure

end etcd_leaseexpiryN
end EtcdGrove
end Perennial
