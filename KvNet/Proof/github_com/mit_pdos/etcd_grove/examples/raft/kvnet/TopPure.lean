/-
# kvnet's top level: the pure facts its proof needs of the statement's premises (2026-11-22)

`notes/kvnet-part.md`, the last sections. From the premises of `raft_kvnet_robust.spec` and the checks of its programs
(`KvNet/Spec/.../kvnet/TopLevelRobustness.lean`):

* the replica's file (`kvDFile dir J id`, `durable`'s `DFile` of `dir`'s root inode `J`): `durable`
  manages it (`kvDFile_ok`, from `dir` a root, `dir.length < 2^39`, the id below `2^32`) and its path
  is the program's (`kvDFile_name`);
* the first generation's directory is empty (`fsInit_entry_none`: from `FsInit` and the statement's
  "nothing at `dir/c`", nothing at any valid name of `dir`'s root directory in the durable tree);
* what `RunNode`'s and `Check`'s checks give: the machines' addresses joined then split are at least
  as many as the machines (`splitAddrs_intercalate_length`), `validCluster`'s `validAddrs` and
  options (`clOk_of_validCluster`), the replica's id and address (`replica_id`), the options raft's
  `RestartNode` takes (`kvOptsOk_of_clOk`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Fs Net

/-! ## The replica's file -/

/-- Replica `id`'s file: `dir/replica-<id>`, `dir`'s root inode `J`. -/
def kvDFile (dir : GoString) (J : Ino) (id : w64) : DurFs.DFile :=
  ⟨dir, J, go!"replica-" ++ decimalB (uint.nat id)⟩

/-- The decimal digits' bytes are digits. -/
theorem decimalB_digit (n : Nat) : ∀ x ∈ decimalB n, 48 ≤ x.toNat ∧ x.toNat ≤ 57 := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  have h := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : 48 ≤ c.toNat := h.1
  have h2 : c.toNat ≤ 57 := h.2
  have : (W8 (c.toNat : Int)).toNat = c.toNat := by
    simp only [BitVec.toNat_ofInt]
    omega
  rw [this]
  exact ⟨h1, h2⟩

/-- At most ten digits below `2^32`. -/
theorem decimalB_length (n : Nat) (hn : n < 2 ^ 32) : (decimalB n).length ≤ 10 := by
  unfold decimalB
  rw [List.length_map]
  exact (Nat.length_toDigits_le_iff (by decide) (by decide)).2 (by omega)

/-- A byte list of literal bytes and digits has no `/` and no NUL. -/
theorem noSlashNul (p : GoString) (n : Nat) (hp : ∀ x ∈ p, x ≠ (47 : w8) ∧ x ≠ (0 : w8)) :
    ∀ x ∈ p ++ decimalB n, x ≠ (47 : w8) ∧ x ≠ (0 : w8) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hp x h
  · have := decimalB_digit n x h
    constructor <;> intro e <;> subst e <;> simp at this

theorem slash_eq : path.slash = slashB := rfl
theorem dot_eq : path.dot = dotB := rfl

/-- A name of length at least 3 with no `/` and no NUL is a valid name and a clean segment. -/
theorem name_of_long (s : GoString) (hl : 3 ≤ s.length)
    (h : ∀ x ∈ s, x ≠ (47 : w8) ∧ x ≠ (0 : w8)) : NameOk s ∧ path.cleanSeg s := by
  have hne : s ≠ [] := by rintro rfl; simp at hl
  have h1 : ∀ a, s ≠ [a] := by rintro a rfl; simp at hl
  have h2 : ∀ a b, s ≠ [a, b] := by rintro a b rfl; simp at hl
  refine ⟨⟨hne, h1 _, h2 _ _, fun m => (h _ m).1 rfl, fun m => (h _ m).2 rfl⟩,
    ⟨hne, fun c hc => (h c hc).1, h1 _, h2 _ _⟩⟩

/-- A valid name is a clean segment. -/
theorem cleanSeg_of_nameOk (c : GoString) (h : NameOk c) : path.cleanSeg c :=
  ⟨h.1, fun x hx e => h.2.2.2.1 (by rw [← slash_eq, ← e]; exact hx), h.2.1, h.2.2.1⟩

theorem segsPath_flatMap : ∀ cs : List GoString, path.segsPath cs = cs.flatMap (slashB :: ·)
  | [] => rfl
  | c :: cs => by
    rw [path.segsPath_cons, segsPath_flatMap cs]
    simp
    rfl

/-- A root's path is a clean absolute path. -/
theorem cleanAbs_of_rootForm (r : GoString) (h : RootForm r) : filepath.CleanAbs r := by
  obtain ⟨cs, hne, hok, rfl⟩ := h
  refine ⟨cs, hne, fun c hc => cleanSeg_of_nameOk c (hok c hc), ?_⟩
  rw [segsPath_flatMap]
  simp [joinPath]

theorem replica_lit : ∀ x ∈ (go!"replica-" : GoString), x ≠ (47 : w8) ∧ x ≠ (0 : w8) := by
  decide

theorem durable_replica_lit :
    ∀ x ∈ (go!".durable-" ++ go!"replica-" : GoString), x ≠ (47 : w8) ∧ x ≠ (0 : w8) := by
  decide

/-- **`durable` manages the replica's file**: `dir` a root, short enough, the id below `2^32`. -/
theorem kvDFile_ok (dir : GoString) (J : Ino) (id : w64) (hr : RootForm dir)
    (hd : dir.length < 2 ^ 39) (hid : uint.nat id < 2 ^ 32) : (kvDFile dir J id).Ok := by
  have hlen := decimalB_length (uint.nat id) hid
  have hb := name_of_long (go!"replica-" ++ decimalB (uint.nat id)) (by simp)
    (noSlashNul _ _ replica_lit)
  have htb := name_of_long (go!".durable-" ++ go!"replica-" ++ decimalB (uint.nat id)) (by simp)
    (noSlashNul _ _ durable_replica_lit)
  have htb' : (kvDFile dir J id).tb = go!".durable-" ++ go!"replica-" ++ decimalB (uint.nat id) := by
    simp [kvDFile, DurFs.DFile.tb]
  refine ⟨cleanAbs_of_rootForm dir hr, hb.2, ?_, hb.1, ?_, ?_⟩
  · rw [htb']; exact htb.2
  · rw [htb']; exact htb.1
  · rw [htb', show (kvDFile dir J id).d = dir from rfl]
    simp only [List.length_append]
    have : (go!".durable-" : GoString).length = 9 := by decide
    have : (go!"replica-" : GoString).length = 8 := by decide
    omega

/-- **The replica's file's path is the program's** (`kdFileName`). -/
theorem kvDFile_name (dir : GoString) (J : Ino) (id : w64) :
    (kvDFile dir J id).name = kdFileName dir id := by
  have : (go!"/replica-" : GoString) = slashB :: go!"replica-" := by decide
  simp [kvDFile, DurFs.DFile.name, kdFileName, this]

/-! ## The first generation's directory -/

/-- A root's form, from `FsInit`. -/
theorem rootForm_of_fsInit {st : OsState} (hst : FsInit st) {dir : GoString} {J : Ino}
    (hr : (dir, J) ∈ st.fs.roots) : RootForm dir :=
  (hst.2.2.2.1.2.2 (dir, J) hr).1

/-- **Nothing in `dir` at the first start**: from `FsInit` and nothing at `dir/c` for every `c`, the
durable tree names nothing at any valid name of `dir`'s root directory. -/
theorem fsInit_entry_none {st : OsState} (hst : FsInit st) {dir : GoString} {J : Ino}
    (hr : (dir, J) ∈ st.fs.roots) (hl : ∀ c, st.lookup (joinPath dir [c]) = none)
    (b : GoString) (hb : NameOk b) : st.fs.treeDur.entry J b = none := by
  have h := lookup_joinPath hst.2.2.2.1 hr (cs := [b]) (by simpa using hb)
  rw [hl b] at h
  have ht : st.tree = st.fs.treeDur := by
    unfold OsState.tree; rw [hst.2.1]; rfl
  rw [ht] at h
  cases he : st.fs.treeDur.entry J b with
  | none => rfl
  | some n => simp [walk, he] at h

/-! ## What `RunNode`'s and `Check`'s checks give -/

/-- `splitBy` gives one piece more than the separators in the string. -/
theorem splitBy_length (sep : w8) : ∀ (s cur : GoString),
    (splitBy sep s cur).length = s.count sep + 1
  | [], cur => by simp [splitBy]
  | c :: s, cur => by
    unfold splitBy
    split
    · rename_i hc
      have hc' : c = sep := (w8_toNat_eq_iff _ _).mp hc
      subst hc'
      simp [splitBy_length c s []]
    · rename_i hc
      have hc' : c ≠ sep := fun e => hc ((w8_toNat_eq_iff _ _).mpr e)
      rw [splitBy_length sep s (c :: cur), List.count_cons]
      simp [hc']

/-- A list joined by a separator holds at least one separator fewer than it has elements. -/
theorem intercalate_count (sep : w8) : ∀ (l : List GoString),
    l.length ≤ (List.intercalate [sep] l).count sep + 1
  | [] => by simp
  | [_] => by simp
  | x :: y :: r => by
    have ih := intercalate_count sep (y :: r)
    rw [List.intercalate_cons_cons, List.count_append, List.count_append]
    simp only [List.length_cons, List.count_singleton_self] at ih ⊢
    omega

/-- **The machines' addresses joined by commas, split back, are at least as many** (the programs
see the split: a machine's address with a comma in it is several): so fewer than `2^32` machines
whenever `ValidAddrs` holds of the split. -/
theorem splitAddrs_intercalate_length (l : List GoString) :
    l.length ≤ (splitAddrs (List.intercalate go!"," l)).length := by
  have e : (go!"," : GoString) = [(44 : w8)] := by decide
  unfold splitAddrs
  rw [e, splitBy_length]
  exact intercalate_count 44 l

/-- `ValidCluster` checks `ValidAddrs`. -/
theorem validAddrs_of_validCluster {l : List GoString} {v msz mcs mif : Nat}
    (h : validCluster l v msz mcs mif = true) : validAddrs l v = true := by
  unfold validCluster at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- **`ValidCluster` checks the options raft and kvnet accept** (`ClusterConfig.Ok`). -/
theorem clOk_of_validCluster (rs : List GoString) (cl : ClusterConfig)
    (h : validCluster rs (uint.nat cl.voters) (uint.nat cl.maxSizePerMsg)
      (uint.nat cl.maxCommittedSizePerReady) (uint.nat cl.maxInflightMsgs) = true) :
    cl.Ok rs.length := by
  simp only [validCluster, validAddrs, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨-, -, -, h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, ?_, h4, h5⟩
  rintro ⟨ha, hb⟩
  rw [ha, hb] at h3
  simp at h3

/-- **Replica `i + 1`'s id and address**: the id is in range and the `i`-th address is its. -/
theorem replica_id (rs : List GoString) (i : Nat) (hi : i < rs.length) (hlen : rs.length < 2 ^ 32) :
    1 ≤ uint.nat (W64 ((i : Int) + 1)) ∧ uint.nat (W64 ((i : Int) + 1)) ≤ rs.length ∧
      uint.nat (W64 ((i : Int) + 1)) < 2 ^ 32 ∧
      rs[uint.nat (W64 ((i : Int) + 1)) - 1]? = some rs[i] := by
  have h : uint.nat (W64 ((i : Int) + 1)) = i + 1 := by
    simp only [uint.nat, BitVec.toNat_ofInt]
    omega
  rw [h]
  refine ⟨by omega, by omega, by omega, ?_⟩
  simp [hi]

/-- **The options raft's `RestartNode` takes**, from the statement's `cl.Ok` (and fewer than `2^32`
replicas). -/
theorem kvOptsOk_of_clOk [GooseExts] (cl : ClusterConfig) (n : Nat) (hcl : cl.Ok n) (hn : n < 2 ^ 32) :
    kvOptsOk ⟨cl.voters, cl.preVote, cl.checkQuorum, cl.stepDownOnRemoval, cl.maxSizePerMsg,
      cl.maxCommittedSizePerReady, cl.maxInflightMsgs⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcl
  unfold kvOptsOk
  simp only
  refine ⟨by word, by word, by word, by word, ?_⟩
  rcases Classical.em (cl.maxCommittedSizePerReady = 0) with hc | hc
  · right; intro hm; exact h3 ⟨hm, hc⟩
  · left; exact hc

end raft_kvnet
end EtcdGrove
end Perennial
