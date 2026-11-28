/-
The hraft kit's server machine (`server.go`; notes/dsv-hraft.md, S5d): the pure vocabulary of its
helpers. Server `k`'s raft ID and address are its number in decimal (`sidOf`, Perennial's
`strconv.Itoa` model); the first configuration is servers `1..n0`, voters (`bootSrvs`); the
protocol's servers are the six (`allSids`). The facts the server machine's proof needs of them:
`sidOf` of `1..9` is one digit (so distinct, non-empty), `bootSrvs n0` is a valid configuration over
`allSids` for `1 ≤ n0 ≤ 6`, and its voters are `1..n0`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net
public import Dsverify.Proof.github_com.hashicorp.raft.core.Defs
public import Perennial.Proof.internal.strconv.FormatBasics
public import Perennial.Std.GMap
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Addrs

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft github_com.hashicorp.raft.proto

section pure
variable [GooseExts]

/-- Server `s`'s raft ID and address (`serverID`, `serverAddr`): `strconv.Itoa(int(s))`. -/
def sidOf (s : w64) : GoString := internal.strconv.fmtInt s (W64 10)

/-- Server `k`'s entry of the first configuration (`bootConfiguration`): a voter, its ID its
address. -/
def srvOfK (k : Nat) : Server := Server.mk (W64 0) (sidOf (W64 (k : Int))) (sidOf (W64 (k : Int)))

/-- The first configuration: servers `1..n`, voters. -/
def bootSrvs (n : Nat) : List Server := (List.range n).map (fun k => srvOfK (k + 1))

/-- The IDs of servers `1..n`. -/
def sidsUpTo (n : Nat) : List SID := (List.range n).map (fun k => sidOf (W64 ((k + 1 : Nat) : Int)))

/-- The protocol's servers: the six server machines. -/
def allSids : List SID := sidsUpTo 6

theorem bootSrvs_succ (n : Nat) : bootSrvs (n + 1) = bootSrvs n ++ [srvOfK (n + 1)] := by
  simp [bootSrvs, List.range_succ]

theorem bootSrvs_length (n : Nat) : (bootSrvs n).length = n := by simp [bootSrvs]

/-- `sidOf` of a one-digit number is its digit. -/
theorem sidOf_small (k : Nat) (hk : k < 10) :
    sidOf (W64 (k : Int)) = [internal.strconv.digitChar k] := by
  unfold sidOf internal.strconv.fmtInt
  have hpos : ¬ sint.Z (W64 (k : Int)) < 0 := by
    have : sint.Z (W64 (k : Int)) = (k : Int) := by word
    omega
  rw [if_neg hpos, internal.strconv.fmtUint10_lt10 _ (by
    show (W64 (k : Int)).toNat < 10
    simp only [W64, BitVec.toNat_ofInt]; omega)]
  congr 2
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- A server ID is never empty (`fmtUint` has a digit). -/
theorem sidOf_ne_nil (s : w64) : sidOf s ≠ [] := by
  unfold sidOf internal.strconv.fmtInt
  split
  · simp
  · obtain ⟨c, cs, h, -, -⟩ := internal.strconv.fmtUint10_head s
    rw [h]; simp

theorem sidOf_inj (a b : Nat) (ha : a < 10) (hb : b < 10)
    (h : sidOf (W64 (a : Int)) = sidOf (W64 (b : Int))) : a = b := by
  rw [sidOf_small a ha, sidOf_small b hb] at h
  simp only [List.cons.injEq, and_true] at h
  exact internal.strconv.digitChar_inj (by omega) (by omega) h

theorem sidOf_length (a : Nat) (ha : a < 10) : (sidOf (W64 (a : Int))).length = 1 := by
  rw [sidOf_small a ha]; rfl

theorem sidsUpTo_nodup (n : Nat) (hn : n ≤ 9) : (sidsUpTo n).Nodup := by
  unfold sidsUpTo List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro a b ha hb hab h
  have ha' := List.mem_range.mp ha
  have hb' := List.mem_range.mp hb
  have := sidOf_inj (a + 1) (b + 1) (by omega) (by omega) h
  omega

theorem allSids_nodup : allSids.Nodup := sidsUpTo_nodup 6 (by omega)

theorem sidOf_mem_sidsUpTo (k n : Nat) (h : 1 ≤ k ∧ k ≤ n) : sidOf (W64 (k : Int)) ∈ sidsUpTo n := by
  unfold sidsUpTo
  simp only [List.mem_map, List.mem_range]
  exact ⟨k - 1, by omega, by congr 2; omega⟩

theorem sidOf_mem_allSids (k : Nat) (h : 1 ≤ k ∧ k ≤ 6) : sidOf (W64 (k : Int)) ∈ allSids :=
  sidOf_mem_sidsUpTo k 6 h

theorem allSids_ne_nil : ∀ j ∈ allSids, j ≠ [] := by
  intro j hj
  unfold allSids sidsUpTo at hj
  simp only [List.mem_map, List.mem_range] at hj
  obtain ⟨k, -, rfl⟩ := hj
  exact sidOf_ne_nil _

theorem srvIds_bootSrvs (n : Nat) : srvIds (bootSrvs n) = sidsUpTo n := by
  simp [srvIds, bootSrvs, sidsUpTo, srvOfK, Function.comp_def]

/-- The first configuration's voters are servers `1..n0`. -/
theorem srvVoters_bootSrvs (n : Nat) : srvVoters (bootSrvs n) = sidsUpTo n := by
  unfold srvVoters
  rw [List.filter_eq_self.mpr (fun s hs => by
    simp only [bootSrvs, List.mem_map, List.mem_range] at hs
    obtain ⟨k, -, rfl⟩ := hs
    simp [srvOfK])]
  simp [bootSrvs, sidsUpTo, srvOfK, Function.comp_def]

/-- The first configuration, servers `1..n0` all voters, is a valid configuration over the six
servers. -/
theorem srvsOkIn_bootSrvs (n0 : Nat) (h0 : 1 ≤ n0 ∧ n0 ≤ 6) : srvsOkIn allSids (bootSrvs n0) := by
  have hsrv : ∀ s ∈ bootSrvs n0, s.Suffrage' = W64 0 ∧ s.Address' = s.ID' ∧ s.ID' ≠ [] ∧
      s.ID'.length < 2 ^ 63 := by
    intro s hs
    simp only [bootSrvs, List.mem_map, List.mem_range] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    refine ⟨rfl, rfl, sidOf_ne_nil _, ?_⟩
    show (sidOf (W64 ((k + 1 : Nat) : Int))).length < 2 ^ 63
    rw [sidOf_length (k + 1) (by omega)]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [srvIds_bootSrvs]; exact sidsUpTo_nodup n0 (by omega)
  · intro j hj
    rw [srvIds_bootSrvs] at hj
    unfold sidsUpTo at hj
    simp only [List.mem_map, List.mem_range] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact sidOf_mem_allSids (k + 1) (by omega)
  · intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hsrv s hs
    exact ⟨Or.inl h1, h2, h3, h4⟩
  · rw [srvVoters_bootSrvs]; unfold sidsUpTo
    cases n0 with
    | zero => omega
    | succ m => simp [List.range_succ]
  · rw [bootSrvs_length]; omega


/-- The transport's peers (`peers()`) of servers `1..n`: each one's raft address to its net/rpc
address. -/
def peersUpTo : Nat → GMap GoString GoString
  | 0 => ∅
  | n + 1 => <[sidOf (W64 ((n + 1 : Nat) : Int)) := serverAddrs.getD n go!""]> (peersUpTo n)

/-- Every peer is a server's. -/
theorem peersUpTo_lookup (n : Nat) (a na : GoString) (h : peersUpTo n !! a = some na) :
    ∃ k, k < n ∧ a = sidOf (W64 ((k + 1 : Nat) : Int)) ∧ na = serverAddrs.getD k go!"" := by
  induction n with
  | zero => simp [peersUpTo] at h
  | succ n ih =>
    simp only [peersUpTo] at h
    rcases (lookup_insert_Some _ _ _ _ _).1 h with ⟨he, hv⟩ | ⟨-, hm⟩
    · exact ⟨n, by omega, he.symm, hv.symm⟩
    · obtain ⟨k, hk, rfl, rfl⟩ := ih hm
      exact ⟨k, by omega, rfl, rfl⟩

end pure

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
