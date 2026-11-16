/-
**restartN's members, addresses and directory: the pure facts** (`notes/restartN-plan.md`). Lean-first
(no Rocq counterpart). putgetN's (`putgetN/Dir.lean`) at restartN's members (`Members("restartN", k,
29000, 30000)`), for `k ≤ 1000`: the names distinct and valid UTF-8, the peer addresses distinct plain
peer URLs and loopback literals (the program's addresses: no client address is served); the directory
facts are putgetN's `dirN_*`, which hold for any members.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open go_etcd_io.etcd.server.v3.etcdserver etcdstart

section pure
variable [GooseExts]

theorem members_mem (k : Nat) (m : GMember) (h : m ∈ members k) :
    ∃ i, i < k ∧ m = memberAt go!"restartN" (W64 29000) (W64 30000) (W64 (i : Int)) := by
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
  rw [show (W64 29000 : w64) = W64 ((29000 : Nat) : Int) from rfl,
    etcd_putgetN.port_toNat _ _ (by omega) (by omega),
    etcd_putgetN.port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

theorem members_peer_plain (k : Nat) : ∀ m ∈ members k, types.plainPeerURL (go!"http://" ++ m.Peer') := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact etcd_putgetN.loopback_plain _

theorem member_port (k : Nat) (m : GMember) (hm : m ∈ members k) :
    ∃ i, i < k ∧ m.Peer' = go!"127.0.0.1:" ++ decStr (W64 ((29000 + i : Nat) : Int)) ∧
      m.Client' = go!"127.0.0.1:" ++ decStr (W64 ((30000 + i : Nat) : Int)) := by
  obtain ⟨i, hi, rfl⟩ := members_mem k m hm
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [memberAt] <;> congr 2 <;> apply BitVec.eq_of_toNat_eq <;>
    simp [W64] <;> omega

/-! ## The program's addresses and data directories (`etcd_adequate_members`' premises) -/

/-- **The program's addresses**: the members' peer addresses (no client address is served). -/
def restartNAddrs (k : Nat) : List GoString := (members k).map (·.Peer')

/-- **The program's data directories**: the members' `restartN-i.etcd`. -/
def restartNDirs (k : Nat) : List GoString := (members k).map (fun m => m.Name' ++ go!".etcd")

/-- The program's start bundles, as `etcd_adequate_members` takes them: every member's name and peer
address, no client address. -/
def startAddrs (k : Nat) : List (GoString × MemberAddrs) :=
  (members k).map (fun m => (m.Name', ⟨some m.Peer', none⟩))

theorem restartNAddrs_perm (k : Nat) :
    ((startAddrs k).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++ []).Perm
      (restartNAddrs k) := by
  unfold startAddrs restartNAddrs
  rw [List.append_nil]
  generalize members k = ms
  induction ms with
  | nil => exact List.Perm.refl _
  | cons a r ih => simp only [List.map_cons, List.flatMap_cons]; exact List.Perm.cons _ ih

theorem restartNDirs_perm (k : Nat) :
    ((startAddrs k).map (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm
      (restartNDirs k) := by
  unfold startAddrs restartNDirs
  rw [List.map_map]
  exact List.Perm.refl _

theorem restartNDirs_nodup (k : Nat) (hk : k ≤ 1000) : (restartNDirs k).Nodup := by
  unfold restartNDirs
  rw [show (fun m : GMember => m.Name' ++ go!".etcd") = (fun n => n ++ go!".etcd") ∘ (·.Name') from rfl,
    ← List.map_map]
  exact List.Pairwise.map _ (fun a b h e => h (List.append_cancel_right e)) (members_names_nodup k hk)

theorem restartNAddrs_lit (k : Nat) (hk : k ≤ 1000) : ∀ a ∈ restartNAddrs k, netAddrLit a = true := by
  intro a ha
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  obtain ⟨i, hi, hp, -⟩ := member_port k m hm
  rw [hp]; exact netAddrLit_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

theorem restartNAddrs_nodup (k : Nat) (hk : k ≤ 1000) : (restartNAddrs k).Nodup :=
  members_peers_nodup k hk

end pure

end etcd_restartN
end EtcdGrove
end Perennial
