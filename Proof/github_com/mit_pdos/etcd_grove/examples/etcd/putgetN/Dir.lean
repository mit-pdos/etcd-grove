/-
**putgetN's members, addresses and directory: the pure facts** (the clusterN Scope, its stage S3).
Lean-first (no Rocq counterpart). For `k ≤ 1000` members: the names distinct and valid UTF-8, the
peer addresses distinct plain peer URLs, every address a loopback literal and the program's
addresses distinct (`etcd_adequate_members`' premises); the directory `dirN`'s laws for any
members (`netDirOk`, the peers, each member's peer URL its entry; putget3's `dir3_*`) are in
`etcdstart/DirN.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetN

open go_etcd_io.etcd.server.v3.etcdserver etcdstart

section pure
variable [GooseExts]

/-! ## The members' addresses -/

theorem members_mem (k : Nat) (m : GMember) (h : m ∈ members k) :
    ∃ i, i < k ∧ m = memberAt go!"putgetN" (W64 24000) (W64 25000) (W64 (i : Int)) := by
  unfold members membersOf at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  exact ⟨i, List.mem_range.1 hi, rfl⟩

theorem port_toNat (b : Nat) (i : Nat) (hb : b < 2 ^ 32) (hi : i < 2 ^ 32) :
    (W64 (b : Int) + W64 (i : Int)).toNat = b + i := by
  simp [W64]
  omega

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
  rw [show (W64 24000 : w64) = W64 ((24000 : Nat) : Int) from rfl, port_toNat _ _ (by omega) (by omega),
    port_toNat _ _ (by omega) (by omega)] at this
  exact hne (by omega)

/-- `127.0.0.1:<p>` is `host:port` with a numeric port. -/
theorem loopback_plain (p : w64) :
    types.plainPeerURL (go!"http://" ++ (go!"127.0.0.1:" ++ decStr p)) := by
  have hne := decStr_ne_nil p
  have hd := decStr_digits p
  unfold types.plainPeerURL types.plainHostPort
  refine ⟨List.isPrefixOf_iff_prefix.2 (List.prefix_append _ _), ?_⟩
  have hdrop : (go!"http://" ++ (go!"127.0.0.1:" ++ decStr p) : List w8).drop 7 =
      go!"127.0.0.1:" ++ decStr p := by simp
  rw [hdrop]
  have hidx : (go!"127.0.0.1:" ++ decStr p : List w8).idxOf (58 : w8) = 9 := by
    rw [List.idxOf_append]; simp only [show (58 : w8) ∈ (go!"127.0.0.1:" : List w8) from by decide, ite_true]; decide
  simp only [hidx]
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp; exact List.length_pos_iff.2 hne
  · rw [List.take_append_of_le_length (by decide)]; decide
  · intro c hc
    rw [List.drop_append_of_le_length (by decide)] at hc
    simp at hc
    exact hd c hc

theorem members_peer_plain (k : Nat) : ∀ m ∈ members k, types.plainPeerURL (go!"http://" ++ m.Peer') := by
  intro m hm
  obtain ⟨i, -, rfl⟩ := members_mem k m hm
  exact loopback_plain _

/-- A loopback address is a plain endpoint (`clientv3.New`'s premise). -/
theorem loopback_plainEndpoint (p : w64) : plainEndpoint (go!"127.0.0.1:" ++ decStr p) := by
  have hd := decStr_digits p
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hm : (47 : w8) ∈ (go!"127.0.0.1:" ++ decStr p : List w8) := h.subset (by decide)
    rcases List.mem_append.1 hm with h1 | h1
    · revert h1; decide
    · have := hd _ h1; simp at this
  · obtain ⟨t, ht⟩ := h
    have := congrArg List.head? ht
    simp at this
  · obtain ⟨t, ht⟩ := h
    have := congrArg List.head? ht
    simp at this

/-! ## The program's addresses and data directories (`etcd_adequate_members`' premises) -/

/-- **The program's addresses**: the members' peer addresses and member `0`'s client address. -/
def putgetNAddrs (k : Nat) : List GoString :=
  (members k).map (·.Peer') ++ ((members k).take 1).map (·.Client')

/-- **The program's data directories**: the members' `putgetN-i.etcd`. -/
def putgetNDirs (k : Nat) : List GoString := (members k).map (fun m => memberDataDir m.Name')

/-- The program's start bundles, as `etcd_adequate_members` takes them. -/
def startAddrs (k : Nat) : List (GoString × MemberAddrs) :=
  (startOf (members k)).map (fun m => (m.1, ⟨some m.2.1, m.2.2⟩))

theorem startOf_names (ms : List GMember) : (startOf ms).map (·.1) = ms.map (·.Name') := by
  cases ms with
  | nil => rfl
  | cons m r => simp [startOf, Function.comp_def]

/-- (wal-fsfix2) The start bundles' names are at most 200 bytes (`etcd_adequate_members`' `hmsL`). -/
theorem startAddrs_names_len (k : Nat) : ∀ m ∈ startAddrs k, m.1.length ≤ 200 := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  have h1 : x.1 ∈ (startOf (members k)).map (·.1) := List.mem_map_of_mem hx
  rw [startOf_names] at h1
  obtain ⟨y, hy, hxy⟩ := List.mem_map.1 h1
  show x.1.length ≤ 200
  rw [← hxy]; exact members_names_len k y hy

theorem flat_none (r : List GMember) :
    ((r.map (fun m => (m.Name', m.Peer', (none : Option GoString)))).map
      (fun m => (m.1, (⟨some m.2.1, m.2.2⟩ : MemberAddrs)))).flatMap (fun m => m.2.addrs) =
      r.map (·.Peer') := by
  induction r with
  | nil => rfl
  | cons a r ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

theorem putgetNAddrs_perm (k : Nat) :
    ((startAddrs k).flatMap (fun (m : GoString × MemberAddrs) => m.2.addrs) ++ []).Perm
      (putgetNAddrs k) := by
  unfold startAddrs putgetNAddrs
  rw [List.append_nil]
  generalize members k = ms
  cases ms with
  | nil => exact List.Perm.refl _
  | cons m r =>
    simp only [startOf, List.map_cons, List.flatMap_cons, flat_none, List.take_succ_cons,
      List.take_zero, List.map_nil]
    show (m.Peer' :: m.Client' :: r.map (·.Peer')).Perm (m.Peer' :: (r.map (·.Peer') ++ [m.Client']))
    exact List.Perm.cons _ (List.perm_middle.trans (by simp)).symm

theorem putgetNDirs_perm (k : Nat) :
    ((startAddrs k).map (fun (m : GoString × MemberAddrs) => memberDataDir m.1)).Perm
      (putgetNDirs k) := by
  unfold startAddrs putgetNDirs
  rw [List.map_map]
  have := congrArg (List.map memberDataDir) (startOf_names (members k))
  simp only [List.map_map] at this
  rw [show ((fun m : GoString × MemberAddrs => memberDataDir m.1) ∘
      fun m : GoString × GoString × Option GoString => (m.1, (⟨some m.2.1, m.2.2⟩ : MemberAddrs))) =
      memberDataDir ∘ (·.1) from rfl, this]
  rfl

theorem putgetNDirs_nodup (k : Nat) (hk : k ≤ 1000) : (putgetNDirs k).Nodup := by
  unfold putgetNDirs
  rw [show (fun m : GMember => memberDataDir m.Name') = memberDataDir ∘ (·.Name') from rfl,
    ← List.map_map]
  exact List.Pairwise.map _ (fun a b h e => h (memberDataDir_inj e)) (members_names_nodup k hk)

theorem member_port (k : Nat) (m : GMember) (hm : m ∈ members k) :
    ∃ i, i < k ∧ m.Peer' = go!"127.0.0.1:" ++ decStr (W64 ((24000 + i : Nat) : Int)) ∧
      m.Client' = go!"127.0.0.1:" ++ decStr (W64 ((25000 + i : Nat) : Int)) := by
  obtain ⟨i, hi, rfl⟩ := members_mem k m hm
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [memberAt] <;> congr 2 <;> apply BitVec.eq_of_toNat_eq <;>
    simp [W64] <;> omega

theorem putgetNAddrs_lit (k : Nat) (hk : k ≤ 1000) : ∀ a ∈ putgetNAddrs k, netAddrLit a = true := by
  intro a ha
  unfold putgetNAddrs at ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨i, hi, hp, -⟩ := member_port k m hm
    rw [hp]; exact netAddrLit_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    obtain ⟨i, hi, -, hc⟩ := member_port k m (List.mem_of_mem_take hm)
    rw [hc]; exact netAddrLit_loopback _ (by simp [W64]; omega) (by simp [W64]; omega)

theorem putgetNAddrs_nodup (k : Nat) (hk : k ≤ 1000) : (putgetNAddrs k).Nodup := by
  unfold putgetNAddrs
  rw [List.nodup_append]
  refine ⟨members_peers_nodup k hk, ?_, ?_⟩
  · cases members k with
    | nil => simp
    | cons m r => simp
  · intro a ha b hb e
    subst e
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨m', hm', he⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, hp, -⟩ := member_port k m hm
    obtain ⟨j, hj, -, hc⟩ := member_port k m' (List.mem_of_mem_take hm')
    rw [hp, hc] at he
    have := congrArg BitVec.toNat (decStr_inj (List.append_cancel_left he))
    simp [W64] at this
    omega

end pure

end etcd_putgetN
end EtcdGrove
end Perennial
