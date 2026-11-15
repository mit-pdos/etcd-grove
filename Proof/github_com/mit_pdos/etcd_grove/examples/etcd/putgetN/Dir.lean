/-
**putgetN's members, addresses and directory: the pure facts** (the clusterN Scope, its stage S3).
Lean-first (no Rocq counterpart). For `k ≤ 1000` members: the names distinct and valid UTF-8, the
peer addresses distinct plain peer URLs, every address a loopback literal and the program's
addresses distinct (`etcd_adequate_members`' premises); the directory `dirN` well formed
(`netDirOk`), naming the peers, each member's peer URL its entry (putget3's `dir3_*`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
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

/-! ## The directory, for any members and ids -/

theorem dirN_of_mem (ms : List GMember) (ids : List w64) (hnd : ids.Nodup) (m : GMember)
    (id : w64) (h : (m, id) ∈ ms.zip ids) : dirN ms ids id = [go!"http://" ++ m.Peer'] := by
  unfold dirN
  induction ms generalizing ids with
  | nil => simp at h
  | cons a ms ih =>
    cases ids with
    | nil => simp at h
    | cons b ids =>
      rw [List.zip_cons_cons, List.find?_cons]
      rw [List.zip_cons_cons] at h
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp
      · have hb : b ≠ id := fun e => (List.nodup_cons.1 hnd).1 (e ▸ (List.of_mem_zip h).2)
        simp only [hb, decide_false]
        exact ih ids (List.nodup_cons.1 hnd).2 h

theorem dirN_cases (ms : List GMember) (ids : List w64) (id : w64) :
    dirN ms ids id = [] ∨
      ∃ m, (m, id) ∈ ms.zip ids ∧ dirN ms ids id = [go!"http://" ++ m.Peer'] := by
  unfold dirN
  cases h : (ms.zip ids).find? (fun p => decide (p.2 = id)) with
  | none => left; rfl
  | some p =>
    right
    have he : p.2 = id := by have := List.find?_some h; simpa using this
    refine ⟨p.1, ?_, rfl⟩
    rw [← he]
    exact List.mem_of_find?_eq_some h

theorem zip_peer_inj (ms : List GMember) (ids : List w64) (hp : (ms.map (·.Peer')).Nodup)
    (m m' : GMember) (id id' : w64) (h : (m, id) ∈ ms.zip ids) (h' : (m', id') ∈ ms.zip ids)
    (he : m.Peer' = m'.Peer') : id = id' := by
  induction ms generalizing ids with
  | nil => simp at h
  | cons a ms ih =>
    cases ids with
    | nil => simp at h
    | cons b ids =>
      rw [List.zip_cons_cons] at h h'
      simp only [List.map_cons, List.nodup_cons] at hp
      rcases List.mem_cons.1 h with h1 | h2 <;> rcases List.mem_cons.1 h' with h1' | h2'
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h1
        obtain ⟨-, rfl⟩ := Prod.mk.inj h1'
        rfl
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h1
        exact absurd (he ▸ List.mem_map_of_mem (f := (·.Peer')) (List.of_mem_zip h2').1) hp.1
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h1'
        exact absurd (he.symm ▸ List.mem_map_of_mem (f := (·.Peer')) (List.of_mem_zip h2).1) hp.1
      · exact ih ids hp.2 h2 h2'

/-- **The directory is well formed** (`netDirOk`, `NewServer`'s premise; putget3's `dir3_ok`). -/
theorem dirN_ok (ms : List GMember) (ids : List w64) (hnd : ids.Nodup) (h0 : W64 0 ∉ ids)
    (hp : (ms.map (·.Peer')).Nodup)
    (hpl : ∀ m ∈ ms, types.plainPeerURL (go!"http://" ++ m.Peer')) :
    netDirOk (dirN ms ids) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases dirN_cases ms ids 0 with h | ⟨m, hm, -⟩
    · exact h
    · exact absurd (List.of_mem_zip hm).2 h0
  · intro i j h hi hj
    rcases dirN_cases ms ids i with hd | ⟨m, hm, hd⟩
    · rw [hd] at hi; simp at hi
    rcases dirN_cases ms ids j with hd' | ⟨m', hm', hd'⟩
    · rw [hd'] at hj; simp at hj
    rw [hd, List.mem_singleton] at hi
    rw [hd', List.mem_singleton] at hj
    exact zip_peer_inj ms ids hp m m' i j hm hm'
      ((List.append_cancel_left hi).symm.trans (List.append_cancel_left hj))
  · intro i s hs
    rcases dirN_cases ms ids i with hd | ⟨m, hm, hd⟩
    · rw [hd] at hs; simp at hs
    rw [hd, List.mem_singleton] at hs
    rw [hs]
    exact hpl m (List.of_mem_zip hm).1

/-- **A host of the directory is a member's peer address** (putget3's `dir3_host`). -/
theorem dirN_host (ms : List GMember) (ids : List w64) (i : w64) (h : GoString)
    (hm : go!"http://" ++ h ∈ dirN ms ids i) : h ∈ ms.map (·.Peer') := by
  rcases dirN_cases ms ids i with hd | ⟨m, hmz, hd⟩
  · rw [hd] at hm; simp at hm
  rw [hd, List.mem_singleton] at hm
  rw [List.append_cancel_left hm]
  exact List.mem_map_of_mem (List.of_mem_zip hmz).1

/-- **The directory's members are the ids** (`rafthttp.bootCfg`'s first half). -/
theorem dirN_ne_nil (ms : List GMember) (ids : List w64) (hlen : ms.length = ids.length)
    (hnd : ids.Nodup) (f : w64) : dirN ms ids f ≠ [] ↔ f ∈ ids := by
  constructor
  · intro h
    rcases dirN_cases ms ids f with hd | ⟨m, hm, -⟩
    · exact absurd hd h
    · exact (List.of_mem_zip hm).2
  · intro hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
    have hm : (ms[i]'(by omega), ids[i]) ∈ ms.zip ids := by
      have : (ms.zip ids)[i]'(by simp; omega) = (ms[i]'(by omega), ids[i]) := by simp
      rw [← this]; exact List.getElem_mem _
    rw [dirN_of_mem ms ids hnd _ _ hm]
    simp

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
def putgetNDirs (k : Nat) : List GoString := (members k).map (fun m => m.Name' ++ go!".etcd")

/-- The program's start bundles, as `etcd_adequate_members` takes them. -/
def startAddrs (k : Nat) : List (GoString × MemberAddrs) :=
  (startOf (members k)).map (fun m => (m.1, ⟨some m.2.1, m.2.2⟩))

theorem startOf_names (ms : List GMember) : (startOf ms).map (·.1) = ms.map (·.Name') := by
  cases ms with
  | nil => rfl
  | cons m r => simp [startOf, Function.comp_def]

theorem flat_none (r : List GMember) :
    ((r.map (fun m => (m.Name', m.Peer', (none : Option GoString)))).map
      (fun m => (m.1, (⟨some m.2.1, m.2.2⟩ : MemberAddrs)))).flatMap (fun m => m.2.addrs) =
      r.map (·.Peer') := by
  induction r with
  | nil => rfl
  | cons a r ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

theorem putgetNAddrs_perm (k : Nat) :
    ((startAddrs k).flatMap (fun m => m.2.addrs) ++ []).Perm (putgetNAddrs k) := by
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
    ((startAddrs k).map (fun m => memberDataDir m.1)).Perm (putgetNDirs k) := by
  unfold startAddrs putgetNDirs
  rw [List.map_map]
  have := congrArg (List.map (fun n => n ++ go!".etcd")) (startOf_names (members k))
  simp only [List.map_map] at this
  rw [show ((fun m : GoString × MemberAddrs => memberDataDir m.1) ∘
      fun m : GoString × GoString × Option GoString => (m.1, (⟨some m.2.1, m.2.2⟩ : MemberAddrs))) =
      (fun n => n ++ go!".etcd") ∘ (·.1) from rfl, this]
  rfl

theorem putgetNDirs_nodup (k : Nat) (hk : k ≤ 1000) : (putgetNDirs k).Nodup := by
  unfold putgetNDirs
  rw [show (fun m : GMember => m.Name' ++ go!".etcd") = (fun n => n ++ go!".etcd") ∘ (·.Name') from rfl,
    ← List.map_map]
  exact (members_names_nodup k hk).map (fun a b h => List.append_cancel_right h)

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
