/-
**leaseN's members, addresses and directory: the pure facts** (leaseN, `notes/leaseN-plan.md`, 2026-11-15).
Lean-first (no Rocq counterpart). txnlinfaultsN's (`txnlinfaultsN/Dir.lean`) without the bridges: for
`k ≤ 1000` members the names distinct and valid UTF-8, the peer addresses distinct plain peer URLs,
every address a loopback literal and the program's addresses (every member's peer and client
address) distinct (`etcd_adequate_members`' premises). The directory is putgetN's `dirN`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart
open etcd_putgetN (port_toNat loopback_plain loopback_plainEndpoint)

section pure
variable [GooseExts]

/-! ## The members' addresses -/

theorem members_mem (k : Nat) (m : GMember) (h : m ∈ members k) :
    ∃ i, i < k ∧ m = memberAt go!"leaseN" (W64 10000) (W64 11000) (W64 (i : Int)) := by
  unfold members membersOf at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  exact ⟨i, List.mem_range.1 hi, rfl⟩

theorem members_names_nodup (k : Nat) (hk : k ≤ 1000) : ((members k).map (·.Name')).Nodup :=
  membersOf_names_nodup _ k (by omega) _ _

theorem members_names_utf8 (k : Nat) : ∀ m ∈ members k, utf8Valid m.Name' := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact memberAt_name_utf8 _ (fun b hb => by revert b; decide) _ _ _

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
  rw [show (W64 10000 : w64) = W64 ((10000 : Nat) : Int) from rfl,
    port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

theorem members_peer_plain (k : Nat) :
    ∀ m ∈ members k, types.plainPeerURL (go!"http://" ++ m.Peer') := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact loopback_plain _

/-- A member's addresses, by its index. -/
theorem member_port (k : Nat) (m : GMember) (hm : m ∈ members k) :
    ∃ i, i < k ∧ m.Peer' = go!"127.0.0.1:" ++ decStr (W64 ((10000 + i : Nat) : Int)) ∧
      m.Client' = go!"127.0.0.1:" ++ decStr (W64 ((11000 + i : Nat) : Int)) := by
  obtain ⟨i, hi, rfl⟩ := members_mem k m hm
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [memberAt] <;> congr 2 <;> apply BitVec.eq_of_toNat_eq <;>
    simp [W64] <;> omega

/-! ## The program's addresses and data directories (`etcd_adequate_members`' premises) -/

/-- **The program's addresses**: the members' peer addresses and their client addresses. -/
def leaseNAddrs (k : Nat) : List GoString :=
  (members k).map (·.Peer') ++ (members k).map (·.Client')

/-- **The program's data directories**: the members' `leaseN-i.etcd`. -/
def leaseNDirs (k : Nat) : List GoString := (members k).map (fun m => m.Name' ++ go!".etcd")

/-- The program's start bundles, as `etcd_adequate_members` takes them. -/
def startAddrs (k : Nat) : List (GoString × MemberAddrs) :=
  (startOf (members k)).map (fun m => (m.1, ⟨some m.2.1, m.2.2⟩))

theorem leaseNAddrs_perm (k : Nat) :
    ((startAddrs k).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++ []).Perm
      (leaseNAddrs k) := by
  unfold startAddrs leaseNAddrs startOf
  rw [List.append_nil]
  generalize members k = ms
  induction ms with
  | nil => exact List.Perm.refl _
  | cons m r ih =>
    simp only [List.map_cons, List.flatMap_cons]
    show (m.Peer' :: m.Client' :: _).Perm (m.Peer' :: (r.map (·.Peer') ++ m.Client' :: r.map (·.Client')))
    refine List.Perm.cons _ ?_
    exact (List.Perm.cons _ ih).trans List.perm_middle.symm

theorem leaseNDirs_perm (k : Nat) :
    ((startAddrs k).map (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm
      (leaseNDirs k) := by
  unfold startAddrs leaseNDirs startOf
  simp only [List.map_map]
  exact List.Perm.refl _

theorem leaseNDirs_nodup (k : Nat) (hk : k ≤ 1000) : (leaseNDirs k).Nodup := by
  unfold leaseNDirs
  rw [show (fun m : GMember => m.Name' ++ go!".etcd") = (fun n => n ++ go!".etcd") ∘ (·.Name') from rfl,
    ← List.map_map]
  exact List.Pairwise.map _ (fun a b h e => h (List.append_cancel_right e)) (members_names_nodup k hk)

/-- Every address of the program is `127.0.0.1:<p>` with `p` in one of the two ranges. -/
theorem addr_port (k : Nat) (a : GoString) (ha : a ∈ leaseNAddrs k) :
    ∃ b i, (b = 10000 ∨ b = 11000) ∧ i < k ∧
      a = go!"127.0.0.1:" ++ decStr (W64 ((b + i : Nat) : Int)) := by
  unfold leaseNAddrs at ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨i, hi, hp, -⟩ := member_port k m hm
    exact ⟨10000, i, Or.inl rfl, hi, hp⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨i, hi, -, hc⟩ := member_port k m hm
    exact ⟨11000, i, Or.inr rfl, hi, hc⟩

theorem leaseNAddrs_lit (k : Nat) (hk : k ≤ 1000) :
    ∀ a ∈ leaseNAddrs k, netAddrLit a = true := by
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
  rw [show (W64 11000 : w64) = W64 ((11000 : Nat) : Int) from rfl,
    port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

theorem members_client_plain (k : Nat) : ∀ m ∈ members k, plainEndpoint m.Client' := by
  intro m hm
  obtain ⟨i, -, -, hc⟩ := member_port k m hm
  rw [hc]; exact loopback_plainEndpoint _

theorem leaseNAddrs_nodup (k : Nat) (hk : k ≤ 1000) : (leaseNAddrs k).Nodup := by
  unfold leaseNAddrs
  rw [List.nodup_append]
  refine ⟨members_peers_nodup k hk, members_clients_nodup k hk, ?_⟩
  intro a ha c hc e
  subst e
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  obtain ⟨m', hm', he⟩ := List.mem_map.1 hc
  obtain ⟨i, hi, hp, -⟩ := member_port k m hm
  obtain ⟨j, hj, -, hc'⟩ := member_port k m' hm'
  rw [hp, hc'] at he
  have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left he))
  simp [W64] at this
  omega

end pure

end etcd_leaseN
end EtcdGrove
end Perennial
