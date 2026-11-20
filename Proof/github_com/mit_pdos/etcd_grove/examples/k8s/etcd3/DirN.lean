/-
**The k8s etcd3 driver's k-member cluster's members, addresses and directory: the pure facts** (stage A of `notes/k8s-7f6-scope.md`; txnlinfaultsN's `Dir.lean`).
Lean-first (no Rocq counterpart). putgetN's (`putgetN/Dir.lean`) at this program's members, every
member's client address served, plus the bridges' addresses: for `k ≤ 1000` members the names
distinct and valid UTF-8, the peer addresses distinct plain peer URLs, the bridges' plain endpoints,
every address a loopback literal and the program's addresses distinct (`etcd_adequate_members`'
premises). The directory is putgetN's `dirN`, whose laws (`dirN_ok`, `dirN_host`, `dirN_ne_nil`,
`dirN_of_mem`) hold for any members and ids.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClusterN
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3N

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart
open etcd_putgetN (port_toNat loopback_plain loopback_plainEndpoint)

section pure
variable [GooseExts]

/-! ## The members' addresses -/

theorem members_mem (k : Nat) (m : GMember) (h : m ∈ members k) :
    ∃ i, i < k ∧ m = memberAt go!"k8setcd3N" (W64 20000) (W64 21000) (W64 (i : Int)) := by
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
  rw [show (W64 20000 : w64) = W64 ((20000 : Nat) : Int) from rfl,
    port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

theorem members_peer_plain (k : Nat) :
    ∀ m ∈ members k, types.plainPeerURL (go!"http://" ++ m.Peer') := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact loopback_plain _

/-- A member's addresses, by its index. -/
theorem member_port (k : Nat) (m : GMember) (hm : m ∈ members k) :
    ∃ i, i < k ∧ m.Peer' = go!"127.0.0.1:" ++ decStr (W64 ((20000 + i : Nat) : Int)) ∧
      m.Client' = go!"127.0.0.1:" ++ decStr (W64 ((21000 + i : Nat) : Int)) := by
  obtain ⟨i, hi, rfl⟩ := members_mem k m hm
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [memberAt] <;> congr 2 <;> apply BitVec.eq_of_toNat_eq <;>
    simp [W64] <;> omega

/-! ## The bridges' addresses -/

theorem bridges_length (k : Nat) : (bridges k).length = k := by simp [bridges]

theorem bridges_getElem (k i : Nat) (h : i < k) :
    (bridges k)[i]? = some (bridgeAt (W64 (i : Int))) := by
  simp [bridges, h]

theorem bridges_succ (k : Nat) : bridges (k + 1) = bridges k ++ [bridgeAt (W64 (k : Int))] := by
  simp [bridges, List.range_succ]

theorem bridge_port (k : Nat) (b : GoString) (hb : b ∈ bridges k) :
    ∃ i, i < k ∧ b = go!"127.0.0.1:" ++ decStr (W64 ((22000 + i : Nat) : Int)) := by
  unfold bridges at hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  refine ⟨i, List.mem_range.1 hi, ?_⟩
  have hi' := List.mem_range.1 hi
  unfold bridgeAt
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [W64]
  omega

theorem bridges_plain (k : Nat) (hk : 1 ≤ k) : plainEndpoints (bridges k) := by
  refine ⟨fun h => ?_, fun b hb => ?_⟩
  · have := congrArg List.length h
    rw [bridges_length] at this; simp at this; omega
  obtain ⟨i, -, rfl⟩ := bridge_port k b hb
  exact loopback_plainEndpoint _

theorem bridges_nodup (k : Nat) (hk : k ≤ 1000) : (bridges k).Nodup := by
  unfold bridges
  refine List.pairwise_map.2 (List.Pairwise.imp_of_mem ?_ List.nodup_range)
  intro i j hi hj hne h
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  unfold bridgeAt at h
  have h' := decStr_inj (List.append_cancel_left h)
  have := congrArg BitVec.toNat h'
  rw [show (W64 22000 : w64) = W64 ((22000 : Nat) : Int) from rfl,
    port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

/-! ## The program's addresses and data directories (`etcd_adequate_members`' premises) -/

/-- **The program's addresses**: the members' peer addresses, their client addresses and the
bridges' addresses. -/
def k8setcd3NAddrs (k : Nat) : List GoString :=
  (members k).map (·.Peer') ++ (members k).map (·.Client') ++ bridges k

/-- **The program's data directories**: the members' `k8setcd3N-i.etcd`. -/
def k8setcd3NDirs (k : Nat) : List GoString := (members k).map (fun m => memberDataDir m.Name')

/-- The program's start bundles, as `etcd_adequate_members` takes them. -/
def startAddrs (k : Nat) : List (GoString × MemberAddrs) :=
  (startOf (members k)).map (fun m => (m.1, ⟨some m.2.1, m.2.2⟩))

/-- (wal-fsfix2) The start bundles' names are at most 200 bytes (`etcd_adequate_members`' `hmsL`). -/
theorem startAddrs_names_len (k : Nat) : ∀ m ∈ startAddrs k, m.1.length ≤ 200 := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact members_names_len k y hy

theorem k8setcd3NAddrs_perm (k : Nat) :
    ((startAddrs k).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++ bridges k).Perm
      (k8setcd3NAddrs k) := by
  unfold startAddrs k8setcd3NAddrs startOf
  refine List.Perm.append_right _ ?_
  generalize members k = ms
  induction ms with
  | nil => exact List.Perm.refl _
  | cons m r ih =>
    simp only [List.map_cons, List.flatMap_cons]
    show (m.Peer' :: m.Client' :: _).Perm (m.Peer' :: (r.map (·.Peer') ++ m.Client' :: r.map (·.Client')))
    refine List.Perm.cons _ ?_
    exact (List.Perm.cons _ ih).trans List.perm_middle.symm

theorem k8setcd3NDirs_perm (k : Nat) :
    ((startAddrs k).map (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm
      (k8setcd3NDirs k) := by
  unfold startAddrs k8setcd3NDirs startOf
  simp only [List.map_map]
  exact List.Perm.refl _

theorem k8setcd3NDirs_nodup (k : Nat) (hk : k ≤ 1000) : (k8setcd3NDirs k).Nodup := by
  unfold k8setcd3NDirs
  rw [show (fun m : GMember => memberDataDir m.Name') = memberDataDir ∘ (·.Name') from rfl,
    ← List.map_map]
  exact List.Pairwise.map _ (fun a b h e => h (memberDataDir_inj e)) (members_names_nodup k hk)

/-- Every address of the program is `127.0.0.1:<p>` with `p` in one of the three ranges. -/
theorem addr_port (k : Nat) (a : GoString) (ha : a ∈ k8setcd3NAddrs k) :
    ∃ b i, (b = 20000 ∨ b = 21000 ∨ b = 22000) ∧ i < k ∧
      a = go!"127.0.0.1:" ++ decStr (W64 ((b + i : Nat) : Int)) := by
  unfold k8setcd3NAddrs at ha
  rcases List.mem_append.1 ha with h | h
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
      obtain ⟨i, hi, hp, -⟩ := member_port k m hm
      exact ⟨20000, i, Or.inl rfl, hi, hp⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
      obtain ⟨i, hi, -, hc⟩ := member_port k m hm
      exact ⟨21000, i, Or.inr (Or.inl rfl), hi, hc⟩
  · obtain ⟨i, hi, hb⟩ := bridge_port k a h
    exact ⟨22000, i, Or.inr (Or.inr rfl), hi, hb⟩

theorem k8setcd3NAddrs_lit (k : Nat) (hk : k ≤ 1000) :
    ∀ a ∈ k8setcd3NAddrs k, netAddrLit a = true := by
  intro a ha
  obtain ⟨b, i, hb, hi, rfl⟩ := addr_port k a ha
  exact netAddrLit_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

theorem k8setcd3NAddrs_nodup (k : Nat) (hk : k ≤ 1000) : (k8setcd3NAddrs k).Nodup := by
  have hport : ∀ (b i b' i' : Nat), (b = 20000 ∨ b = 21000 ∨ b = 22000) →
      (b' = 20000 ∨ b' = 21000 ∨ b' = 22000) → i < k → i' < k →
      (go!"127.0.0.1:" ++ decStr (W64 ((b + i : Nat) : Int)) : GoString) =
        go!"127.0.0.1:" ++ decStr (W64 ((b' + i' : Nat) : Int)) → b = b' ∧ i = i' := by
    intro b i b' i' hb hb' hi hi' he
    have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left he))
    simp [W64] at this
    omega
  unfold k8setcd3NAddrs
  rw [List.nodup_append, List.nodup_append]
  have hcl : ((members k).map (·.Client')).Nodup := by
    unfold members membersOf
    rw [List.map_map]
    refine List.pairwise_map.2 (List.Pairwise.imp_of_mem ?_ List.nodup_range)
    intro i j hi hj hne h
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    simp only [Function.comp, memberAt] at h
    have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left h))
    rw [show (W64 21000 : w64) = W64 ((21000 : Nat) : Int) from rfl,
      port_toNat _ _ (by omega) (by omega), port_toNat _ _ (by omega) (by omega)] at this
    exact hne (by omega)
  refine ⟨⟨members_peers_nodup k hk, hcl, ?_⟩, bridges_nodup k hk, ?_⟩
  · intro a ha c hc e
    subst e
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨m', hm', he⟩ := List.mem_map.1 hc
    obtain ⟨i, hi, hp, -⟩ := member_port k m hm
    obtain ⟨j, hj, -, hc'⟩ := member_port k m' hm'
    rw [hp, hc'] at he
    have := hport _ _ _ _ (Or.inr (Or.inl rfl)) (Or.inl rfl) hj hi he
    omega
  · intro a ha c hc e
    subst e
    obtain ⟨i, hi, rfl⟩ := bridge_port k a hc
    rcases List.mem_append.1 ha with h | h
    · obtain ⟨m, hm, he⟩ := List.mem_map.1 h
      obtain ⟨j, hj, hp, -⟩ := member_port k m hm
      rw [hp] at he
      have := hport _ _ _ _ (Or.inl rfl) (Or.inr (Or.inr rfl)) hj hi he
      omega
    · obtain ⟨m, hm, he⟩ := List.mem_map.1 h
      obtain ⟨j, hj, -, hc'⟩ := member_port k m hm
      rw [hc'] at he
      have := hport _ _ _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hj hi he
      omega

end pure

end k8s_etcd3N
end EtcdGrove
end Perennial
