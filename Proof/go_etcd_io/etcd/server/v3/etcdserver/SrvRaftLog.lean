/-
**Raft's committed log, at the server, over raft's node API** (2026-10-27, branch `server-port`;
`notes/decisions.md`, "etcd's server on raft's node API"). Until then (stage R7b, 2026-10-16) the
server's contract predicates were definitions over raft's protocol (`rLog`, `isCommitted`,
`propIs`, `readReq`, ...); now they are over raft's node API (`InvNode.lean`) and the server's own ghost state, and name nothing of raft's internals.

**The two logs.** Raft's committed log, as the server's records (`EntryModel`, with their
indices), is known through lower bounds (`srvRLogLb γ L`: the node API's `isCommittedLogLb` of
`pre ++ L`, the indices consecutive after `ai0`): what a `Ready` hands out, fillers included. The
log the KV invariant owns (`srvRLog γ L`, half of a mono list whose other half the server's log
invariant holds, `srvRaftLogInv`) is the log of the **requested entries** only, each at the index
it would have without the fillers (raft commits its fillers without the client: the node API's
`ownCommittedOps`). The two agree on their requested entries (`srvEqv`), which is all the KV model
reads (`kvModel_eqv`).

**Proposals** (`srvPropAu1`, unchanged): the server's update over `srvRLog`. Raft's `Propose`
takes an update over `ownCommittedOps`; the server's log invariant turns one into the other
(`srvPropAu_api`), keeping the proposals' registry raft kept until then: a proposal of `d` is
registered once (its fresh token, `srvPropFresh`), with its result predicate (`props`, a saved
predicate), fires once (its token `γt`), and its result at the log before its entry is left in the
registry (`fired`): `srvPropWits` reads it back at any committed log holding `d`'s entry, through
the result predicate's invariance under `srvEqv` (`srvQInv`).

**Reads** (`srvReadAu`, unchanged): the server's persistent update over `srvRLog`. Raft's read
contexts fire an update once, when the read takes effect; the server's log invariant registers the
read then (`pend`) and fires it again at every later requested entry (in `srvPropAu_api`), so
`srvReadWit` gives the read's result at every committed log past the read index, as raft's
registry did.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Spec.go_etcd_io.raft.v3.Api
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.ConfPolicy
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-! ## Names and the entries' two views -/

/-- The server's raft namespace: the node API's cluster (`srvClusterN`) and the server's log
invariant (`srvLogN`) are inside it, so that the masks `⊤ \ ↑srvRaftN` the server's updates have
exclude both. -/
def srvRaftN : Namespace := nroot .@ "raft_commit"

/-- The node API cluster's namespace (`cluster_alloc`'s `N`). -/
def srvClusterN : Namespace := srvRaftN .@ "cluster"

/-- The server's log invariant's namespace. -/
def srvLogN : Namespace := srvRaftN .@ "log"

theorem srvClusterN_sub : (↑srvClusterN : CoPset) ⊆ ↑srvRaftN := nclose_subseteq _ _
theorem srvLogN_sub : (↑srvLogN : CoPset) ⊆ ↑srvRaftN := nclose_subseteq _ _
@[simp] theorem srvLogN_clusterN : (↑srvLogN : CoPset) ⊆ ⊤ \ ↑srvClusterN :=
  mask_ndot_ne' srvRaftN "log" "cluster" (by decide)

/-- (2026-10-30, the repair) **The cluster's conf-change policy's namespace** (`confPolicy`'s `N'`):
outside `srvRaftN`, so that the apply thread decides a conf entry under any mask the server's
updates leave. -/
def srvConfN : Namespace := nroot .@ "server_conf"

/-- (2026-10-30, the repair; D2(i)) **The namespace of the cluster's snapshot registry**, which the
server holds empty for good (`srvClusterOk`): outside `srvRaftN`, so that a snapshot fact is refuted
under any mask the server's updates leave. -/
def srvSnapsN : Namespace := nroot .@ "server_snaps"

/-- **The cluster, as the server sees it** (2026-10-27; 2026-10-30, the repair: one mode): the node
API's cluster, the voters it started with (`vs`), the rule its conf entries are decided by (`rule`,
the cluster's `confPolicy`: `srvRule`, `InvCfgView.lean`, tied by `rnEnvOk`; until the repair a
static or dynamic mode, `dyn`, and the dynamic mode's decoder `dec`), and the server's ghost names:
the requested entries' log (`log`, a mono list), the proposals' fresh tokens (`fresh`), their
registry (`props`: data ↦ result predicate and one-shot token), the fired proposals (`fired`: data ↦
the log before its entry), the read contexts' fresh tokens (`rdFresh`) and the reads to fire again
(`pend`). -/
structure SrvRaft [GooseExts] where
  cl : Cluster
  vs : List w64
  rule : ConfRule
  /-- the bootstrap log, as raft's records (raft's `reBoot` until 2026-10-27): the members'
  `ConfChange`s the cluster started with, which the server's membership model folds -/
  boot : List EntryM
  /-- the `MemoryStorage` registry's ghost name (raft's storage API, `MemStorReg`): the storage
  model the node API's node predicates are stated at (`srvStor`) -/
  reg : GName
  /-- the members' snapshot directories' ghost names (raft's `reSnapLoc` until 2026-10-27; the
  snapshot path's `snapDirInv`, unreachable since the server's clusters send no snapshot) -/
  snapLoc : w64 → Option GName
  log : GName
  fresh : GName
  props : GName
  fired : GName
  rdFresh : GName
  pend : GName

/-- The voters the cluster started with, as a set (raft's `reCfg` until 2026-10-27). -/
def SrvRaft.cfg [GooseExts] (γ : SrvRaft) : GSet w64 := GMap.listToSet γ.vs

/-- The ghost names of the server's raft contract: the cluster, the committed log before the
server's start index (`uint.Z ai0 = pre.length`, `srvRaftLogInv`; the composition starts at `[]`)
and the start index itself. -/
structure ServerRaftNames [GooseExts] where
  raft : SrvRaft
  /-- raft's committed log before the server's start index -/
  pre : List EntryModel
  /-- the index the log starts after -/
  ai0 : w64

section pure
variable [GooseExts]

/-- Raft's full committed log holding the server's `L` after its start: `pre ++ L`, as raft's
records. -/
def srvLogOf (γ : ServerRaftNames) (L : List EntryModel) : List EntryM :=
  (γ.pre ++ L).map EntryModel.toM

theorem srvLogOf_prefix (γ : ServerRaftNames) (A B : List EntryModel) :
    srvLogOf γ A <+: srvLogOf γ B ↔ A <+: B := by
  unfold srvLogOf
  rw [List.prefix_map_iff_of_injective EntryModel.toM_injective, List.prefix_append_right_inj]

theorem srvLogOf_length (γ : ServerRaftNames) (L : List EntryModel) :
    (srvLogOf γ L).length = γ.pre.length + L.length := by
  simp [srvLogOf]

theorem srvLogOf_snoc (γ : ServerRaftNames) (L : List EntryModel) (e : EntryModel) :
    srvLogOf γ (L ++ [e]) = srvLogOf γ L ++ [e.toM] := by
  simp [srvLogOf]

theorem srvLogOf_drop (γ : ServerRaftNames) (L : List EntryModel) :
    (srvLogOf γ L).drop γ.pre.length = L.map EntryModel.toM := by
  unfold srvLogOf
  rw [List.map_append, List.drop_left' (by simp)]

theorem srvLogOf_take (γ : ServerRaftNames) (L : List EntryModel) (m : Nat) :
    (srvLogOf γ L).take (γ.pre.length + m) = srvLogOf γ (L.take m) := by
  unfold srvLogOf
  rw [List.map_append, List.map_append, List.map_take]
  have h : γ.pre.length = (γ.pre.map EntryModel.toM).length := by simp
  rw [h, List.take_length_add_append]

theorem srvLogOf_pre_prefix (γ : ServerRaftNames) (L : List EntryModel) :
    γ.pre.map EntryModel.toM <+: srvLogOf γ L := by
  unfold srvLogOf; rw [List.map_append]; exact List.prefix_append _ _

theorem srvLogOf_lookup (γ : ServerRaftNames) (L : List EntryModel) (m : Nat) (e : EntryModel)
    (h : L[m]? = some e) : (srvLogOf γ L)[γ.pre.length + m]? = some e.toM := by
  unfold srvLogOf
  rw [List.getElem?_map, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, h]
  rfl

/-- **The bootstrap log of the peers `ps`**, as raft's records (2026-10-27: the server's copy of
raft's `srvBootLogOk`): one entry per peer, at term `1`, at its position, a `ConfChange` whose bytes
decode to an `AddNode` of the peer. -/
def srvBootLogOk (ps : List w64) (bootLog : List EntryM) : Prop :=
  bootLog.length = ps.length ∧ (bootLog.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : EntryM), bootLog[k]? = some e →
    e.Term' = W64 1 ∧ uint.Z e.Index' = (k : Int) + 1 ∧ e.Type' = W32 1 ∧
    (∃ m : ConfChangeM, ccDecodeV1 e.Data' = some m ∧ m.type = W32 0 ∧ ps[k]? = some m.nodeId)

/-- The node API's bootstrap log, as raft's records. -/
theorem srvBootLogOk_of_BootLog (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (h : BootLog ps ctxs boot) :
    srvBootLogOk ps (LogEntry.toEntries boot 0) := by
  obtain ⟨hl, hlt, hk⟩ := h
  have hlen : (LogEntry.toEntries boot 0).length = boot.length := by
    simp [LogEntry.toEntries]
  refine ⟨by rw [hlen, hl], by rw [hlen]; exact hlt, ?_⟩
  intro k e he
  unfold LogEntry.toEntries at he
  rw [List.getElem?_mapIdx] at he
  cases hb : boot[k]? with
  | none => rw [hb] at he; cases he
  | some x =>
    rw [hb] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨id, ctx, hp, -, ht, hty, hm⟩ := hk k x hb
    have hkb : k < boot.length := (List.getElem?_eq_some_iff.1 hb).1
    refine ⟨ht, ?_, hty, ⟨_, hm, rfl, hp⟩⟩
    simp only [LogEntry.toEntryM]
    have : ((0 + k + 1 : Nat) : Int) < 2 ^ 64 := by omega
    simp only [Nat.zero_add] at this ⊢
    word

/-- An entry as raft's node API sees it: its index dropped. -/
def EntryModel.toLE (m : EntryModel) : LogEntry := ⟨m.term, m.typ, m.data⟩

/-- The committed log holding the server's `L` after its start, as raft's node API sees it. -/
def srvLE (γ : ServerRaftNames) (L : List EntryModel) : List LogEntry :=
  (γ.pre ++ L).map EntryModel.toLE

theorem srvLE_append (γ : ServerRaftNames) (A B : List EntryModel) :
    srvLE γ (A ++ B) = srvLE γ A ++ B.map EntryModel.toLE := by
  simp [srvLE]

theorem srvLE_length (γ : ServerRaftNames) (L : List EntryModel) :
    (srvLE γ L).length = γ.pre.length + L.length := by
  simp [srvLE]

theorem opsOf_append (a b : List LogEntry) :
    opsOf (a ++ b) = opsOf a ++ opsOf b := by
  simp only [opsOf, List.filter_append]

/-- (2026-10-30, the repair: raft's `opsOf` also drops empty `ConfChangeV2`s, `isEmptyV2`) -/
theorem opsOf_nofill (a : List LogEntry) (h : ∀ e ∈ a, ¬ e.isFiller ∧ ¬ e.isEmptyV2) :
    opsOf a = a := by
  unfold opsOf
  rw [List.filter_eq_self]
  intro e he
  simp [(h e he).1, (h e he).2]

theorem opsOf_length_le (a : List LogEntry) : (opsOf a).length ≤ a.length := by
  unfold opsOf; exact List.length_filter_le _ _

theorem opsOf_prefix {a b : List LogEntry} (h : a <+: b) :
    opsOf a <+: opsOf b := by
  obtain ⟨r, rfl⟩ := h
  rw [opsOf_append]; exact List.prefix_append _ _

/-- An entry of a log whose index is its position: two such logs whose entries agree but for the
index are the same log. -/
theorem idx_list_eq (ai₀ : w64) (A B : List EntryModel) (hA : srvIdxOkW ai₀ A)
    (hB : srvIdxOkW ai₀ B) (h : A.map EntryModel.toLE = B.map EntryModel.toLE) : A = B := by
  have hl : A.length = B.length := by
    have := congrArg List.length h; simpa using this
  apply List.ext_getElem?
  intro n
  rcases Nat.lt_or_ge n A.length with hn | hn
  · obtain ⟨a, ha⟩ : ∃ a, A[n]? = some a := ⟨_, List.getElem?_eq_getElem hn⟩
    obtain ⟨b, hb⟩ : ∃ b, B[n]? = some b := ⟨_, List.getElem?_eq_getElem (hl ▸ hn)⟩
    rw [ha, hb]
    have hab : a.toLE = b.toLE := by
      have := congrArg (fun l => l[n]?) h
      simp only [List.getElem?_map, ha, hb, Option.map_some] at this
      exact Option.some.inj this
    have ia := (hA n a ha).1
    have ib := (hB n b hb).1
    have hidx : a.index = b.index := by
      have : uint.Z a.index = uint.Z b.index := by rw [ia, ib]
      word
    cases a; cases b
    simp only [EntryModel.toLE, LogEntry.mk.injEq] at hab
    obtain ⟨rfl, rfl, rfl⟩ := hab
    simp only at hidx
    rw [hidx]
  · rw [List.getElem?_eq_none hn, List.getElem?_eq_none (hl ▸ hn)]

theorem idx_prefix (ai₀ : w64) (A B : List EntryModel) (hA : srvIdxOkW ai₀ A)
    (hB : srvIdxOkW ai₀ B) (h : A.map EntryModel.toLE <+: B.map EntryModel.toLE) : A <+: B := by
  have hlen : A.length ≤ B.length := by
    have := h.length_le; simpa using this
  have hBt : srvIdxOkW ai₀ (B.take A.length) := srvIdxOkW_prefix ai₀ _ B hB (List.take_prefix _ _)
  have heq : A.map EntryModel.toLE = (B.take A.length).map EntryModel.toLE := by
    rw [List.map_take]
    have := List.prefix_iff_eq_take.1 h
    simpa using this
  have := idx_list_eq ai₀ A (B.take A.length) hA hBt heq
  rw [this]; exact List.take_prefix _ _

theorem srvLE_prefix (γ : ServerRaftNames) (A B : List EntryModel) (hA : srvIdxOkW γ.ai0 A)
    (hB : srvIdxOkW γ.ai0 B) (h : srvLE γ A <+: srvLE γ B) : A <+: B := by
  unfold srvLE at h
  rw [List.map_append, List.map_append] at h
  exact idx_prefix γ.ai0 A B hA hB ((List.prefix_append_right_inj _).1 h)

theorem srvLE_prefix_of (γ : ServerRaftNames) (A B : List EntryModel) (h : A <+: B) :
    srvLE γ A <+: srvLE γ B := by
  obtain ⟨r, rfl⟩ := h
  rw [srvLE_append]; exact List.prefix_append _ _

/-- **Two server logs with the same requested entries** (both consecutive after `ai0`): what the
KV model and the server's result predicates cannot tell apart. -/
def srvEqv (γ : ServerRaftNames) (A B : List EntryModel) : Prop :=
  srvIdxOkW γ.ai0 A ∧ srvIdxOkW γ.ai0 B ∧
    opsOf (A.map EntryModel.toLE) = opsOf (B.map EntryModel.toLE)

theorem srvEqv_refl (γ : ServerRaftNames) (A : List EntryModel) (h : srvIdxOkW γ.ai0 A) :
    srvEqv γ A A := ⟨h, h, rfl⟩

theorem toLE_isFiller (m : EntryModel) :
    m.toLE.isFiller ↔ (m.data = [] ∧ m.typ = W32 0) := Iff.rfl

end pure

section pure2
variable [GooseExts]

/-- **Facts of the server's log, on a committed log with its requested entries** (2026-10-27): an
entry-wise fact that reads only an entry's term, type and data, and holds of an empty normal
entry and of an empty `ConfChangeV2` (2026-10-30, the repair: raft's `opsOf` drops both), holds of
every entry of a committed log `A` whose requested entries are a prefix of the server's log `L`'s,
when it holds of `L`'s (`A`'s fillers are empty normal entries: `srvIdxOkW`). -/
theorem srv_entry_transfer (ai₀ : w64) (A L : List EntryModel) (P : EntryModel → Prop)
    (hP : ∀ m m', m.toLE = m'.toLE → P m' → P m)
    (hfill : ∀ m : EntryModel, m.typ = W32 0 → m.data = [] → P m)
    (hv2 : ∀ m : EntryModel, m.typ = W32 2 → m.data = [] → P m)
    (hA : srvIdxOkW ai₀ A) (h : opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (hL : ∀ m ∈ L, P m) : ∀ m ∈ A, P m := by
  intro m hm
  by_cases hf : m.toLE.isFiller
  · obtain ⟨hd, hty⟩ := hf
    simp only [EntryModel.toLE] at hd hty
    exact hfill m hty hd
  by_cases hv : m.toLE.isEmptyV2
  · obtain ⟨hd, hty⟩ := hv
    simp only [EntryModel.toLE] at hd hty
    exact hv2 m hty hd
  · have hin : m.toLE ∈ opsOf (A.map EntryModel.toLE) := by
      unfold opsOf
      rw [List.mem_filter]
      exact ⟨List.mem_map_of_mem hm, by simp [hf, hv]⟩
    obtain ⟨m', hm', he⟩ := List.mem_map.1 (h.subset hin)
    exact hP m m' he.symm (hL m' hm')

/-- **Where a committed log's entry comes from** (2026-10-27): an entry of a committed log `A`
whose requested entries are a prefix of the server's log `L`'s is an empty normal entry (a filler),
an empty `ConfChangeV2` (2026-10-30, the repair: raft commits one to leave a joint configuration,
`committed_emptyV2_joint`, which the server's static membership never has) or has the term, type
and data of one of `L`'s. -/
theorem srv_entry_src (ai₀ : w64) (A L : List EntryModel) (hA : srvIdxOkW ai₀ A)
    (h : opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE) :
    ∀ m ∈ A, (m.typ = W32 0 ∧ m.data = []) ∨ (m.typ = W32 2 ∧ m.data = []) ∨
      ∃ m' ∈ L, m'.toLE = m.toLE := by
  intro m hm
  by_cases hf : m.toLE.isFiller
  · obtain ⟨hd, hty⟩ := hf
    simp only [EntryModel.toLE] at hd hty
    exact .inl ⟨hty, hd⟩
  by_cases hv : m.toLE.isEmptyV2
  · obtain ⟨hd, hty⟩ := hv
    simp only [EntryModel.toLE] at hd hty
    exact .inr (.inl ⟨hty, hd⟩)
  · have hin : m.toLE ∈ opsOf (A.map EntryModel.toLE) := by
      unfold opsOf
      rw [List.mem_filter]
      exact ⟨List.mem_map_of_mem hm, by simp [hf, hv]⟩
    obtain ⟨m', hm', he⟩ := List.mem_map.1 (h.subset hin)
    exact .inr (.inr ⟨m', hm', he⟩)

/-- **A committed log's equivalent prefix of the server's log** (2026-10-27): the prefix of `L`
holding a committed log `A`'s requested entries, with the same requested entries. -/
theorem srv_eqv_prefix (γ : ServerRaftNames) (A L : List EntryModel) (hA : srvIdxOkW γ.ai0 A)
    (hL : srvIdxOkW γ.ai0 L) (hnf : ∀ m ∈ L, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2)
    (h : opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE) :
    ∃ A', A' <+: L ∧ srvEqv γ A A' := by
  refine ⟨L.take (opsOf (A.map EntryModel.toLE)).length, List.take_prefix _ _, hA,
    srvIdxOkW_prefix _ _ L hL (List.take_prefix _ _), ?_⟩
  have hnf' : ∀ x ∈ (L.take (opsOf (A.map EntryModel.toLE)).length).map EntryModel.toLE,
      ¬ x.isFiller ∧ ¬ x.isEmptyV2 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hnf y (List.mem_of_mem_take hy)
  rw [opsOf_nofill _ hnf', List.map_take]
  exact List.prefix_iff_eq_take.1 h

end pure2

/-! ## The server's two views of the committed log -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server's half of its log of requested entries** `L` (exclusive; the KV invariant's).
(2026-10-27: until then raft's `rLog`, the client's half of the whole committed log.) -/
def srvRLog (γ : ServerRaftNames) (L : List EntryModel) : IProp GF :=
  monoListAuthOwn γ.raft.log (1 : Qp).half L

instance srvRLog_timeless (γ : ServerRaftNames) (L : List EntryModel) :
    Timeless (srvRLog (GF := GF) γ L) := by
  unfold srvRLog; infer_instance

/-- **A prefix of the committed raft log** (persistent): the node API's lower bound of `pre ++ L`,
`L`'s indices consecutive after `ai0`. -/
def srvRLogLb (γ : ServerRaftNames) (L : List EntryModel) : IProp GF :=
  iprop(isCommittedLogLb γ.raft.cl (srvLE γ L) ∗ ⌜srvIdxOkW γ.ai0 L⌝)

instance srvRLogLb_persistent (γ : ServerRaftNames) (L : List EntryModel) :
    Persistent (srvRLogLb (GF := GF) γ L) := by
  unfold srvRLogLb; infer_instance

instance srvRLogLb_timeless (γ : ServerRaftNames) (L : List EntryModel) :
    Timeless (srvRLogLb (GF := GF) γ L) := by
  unfold srvRLogLb; infer_instance

theorem srvRLogLb_idx (γ : ServerRaftNames) (L : List EntryModel) :
    srvRLogLb (GF := GF) γ L ⊢ ⌜srvIdxOkW γ.ai0 L⌝ := by
  unfold srvRLogLb; iintro ⟨-, %H⟩; ipureintro; exact H

/-- **The cluster's storage model** (raft's storage API at the `MemoryStorage` registry `reg`):
the instance the node API's node predicates are stated at, for the server. -/
abbrev srvStor (γ : SrvRaft) : StorageModel GF :=
  letI : MemStorReg GF := ⟨γ.reg⟩
  inferInstance

/-- Any storage model (the node API's laws take one, unused). -/
abbrev srvAnyStor : StorageModel GF :=
  letI : MemStorReg GF := ⟨default⟩
  inferInstance

/-- Two prefixes of the committed log are comparable. -/
theorem srvRLogLb_prefix (γ : ServerRaftNames) (A B : List EntryModel) :
    srvRLogLb (GF := GF) γ A ∗ srvRLogLb γ B ⊢ ⌜A <+: B ∨ B <+: A⌝ := by
  unfold srvRLogLb
  iintro ⟨⟨#HA, %hA⟩, ⟨#HB, %hB⟩⟩
  icases isCommittedLogLb_agree γ.raft.cl (srvLE γ A) (srvLE γ B) $$ [HA HB] with %H
  · iframe HA HB
  ipureintro
  rcases H with h | h
  · exact .inl (srvLE_prefix γ A B hA hB h)
  · exact .inr (srvLE_prefix γ B A hB hA h)

/-- A prefix of a committed prefix. -/
theorem srvRLogLb_mono (γ : ServerRaftNames) (A B : List EntryModel) (h : A <+: B) :
    srvRLogLb (GF := GF) γ B ⊢ srvRLogLb γ A := by
  unfold srvRLogLb
  iintro ⟨#HB, %hB⟩
  isplitl
  · iapply isCommittedLogLb_mono γ.raft.cl _ _ (srvLE_prefix_of γ A B h) $$ HB
  · ipureintro; exact srvIdxOkW_prefix γ.ai0 A B hB h

end ghost

/-! ## The conf-change policy (pure) -/

section policy
variable [GooseExts]

/-- **`json.Unmarshal` of a conf change's context into a `membership.ConfigChangeContext`**
(audit phase B3, 2026-10-18; `encoding/json` is not modelled, so opaque, a function of the
bytes): the member's `ID` and `IsPromote` when the bytes unmarshal, `none` when they do not
(where `applyConfChange` and `ValidateConfigurationChange` panic, `lg.Panic`). A
`ConfigChangeContext` embeds the `Member`, so the JSON of a `Member` (what etcd's bootstrap puts in
each peer's context) unmarshals to its `ID` with `IsPromote` false. -/
opaque membership.ccContextOf : List w8 → Option (w64 × Bool)

/-- **A conf change the server's `applyConfChange` takes** (audit phase B3, 2026-10-18): an
`AddNode` (type `0`) of a member of raft's configuration `cfg`, whose context unmarshals to that
member, not a promotion. -/
def ccApplyOk (cfg : GSet w64) (m : ConfChangeM) : Prop :=
  m.type = W32 0 ∧ m.nodeId ∈ cfg ∧ membership.ccContextOf m.context = some (m.nodeId, false)

/-- **A conf change `applyConfChange` takes** (D43 M5d/M5e; 2026-10-30, the repair, D3: static
membership after boot, so `ccApplyOk` only; until then, in a dynamic cluster, also a `RemoveNode` of
a member of the configuration). (2026-10-27: of the server's `SrvRaft`'s `cfg`.) -/
def ccApplyOkR (γ : SrvRaft) (m : ConfChangeM) : Prop :=
  ccApplyOk γ.cfg m

/-- `ccApplyOkR` at the server's raft. -/
abbrev ccApplyOkM (γs : ServerRaftNames) (m : ConfChangeM) : Prop := ccApplyOkR γs.raft m

/-- The bytes `d` of a conf-change entry decode to a change `applyConfChange` takes. -/
def ccBootOk (cfg : GSet w64) (d : List w8) : Prop :=
  ∀ m, ccDecodeV1 d = some m → ccApplyOk cfg m

/-- **The bytes `d` of a conf-change entry decode to a change `applyConfChange` takes** (D43 M5d). -/
def ccPolOk (γ : SrvRaft) (d : List w8) : Prop :=
  ∀ m, ccDecodeV1 d = some m → ccApplyOkR γ m

theorem ccPolOk_of_boot (γ : SrvRaft) (d : List w8) (h : ccBootOk γ.cfg d) : ccPolOk γ d :=
  fun m hm => h m hm

/-- `ccPolOk` is `ccBootOk` (2026-10-30, the repair: one mode; until then in a static cluster). -/
theorem ccPolOk_static (γ : SrvRaft) (d : List w8) (h : ccPolOk γ d) :
    ccBootOk γ.cfg d :=
  fun m hm => h m hm

/-- **A v1 change raft's node applies without changing its configuration `cfg`** (raft's static
mode admits only such changes, `CCShrink`): an `AddNode` of a voter, or of the node `0`. -/
def ccRaftOk (cfg : GSet w64) (m : ConfChangeM) : Prop :=
  m.type = W32 0 ∧ ∃ k, k ∈ cfg ∧ (m.nodeId = k ∨ m.nodeId = W64 0)

/-- (2026-10-30, the repair; D3, static membership after boot) **The rule keeps the voters'
membership** `simple cfg`: a v1 conf entry whose bytes decode to changes the server takes
(`ccBootOk`: an `AddNode` of a voter) is decided a change that leaves it as it is (the change, or
it with `NodeId` `0` when it does not validate: `Membership.applyChange_addVoter`/`_nodeZero`), and
every other entry (an empty `ConfChangeV2`, raft's; the server proposes none) is skipped. What the
cluster's `confPolicy` rule satisfies (`srvClusterOk`; `srvRule_keeps`, `InvCfgView.lean`). -/
def srvRuleKeeps (r : ConfRule) (cfg : GSet w64) : Prop :=
  ∀ (pre : List LogEntry) (e : LogEntry),
    (e.type = W32 1 → ccBootOk cfg e.data → ∀ o, r pre (Membership.simple cfg) e = some o →
      Membership.applyChange o (Membership.simple cfg) = some (Membership.simple cfg)) ∧
    (e.type ≠ W32 1 → r pre (Membership.simple cfg) e = none)

end policy

/-! ## The server's updates and their registries -/

section regs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A proposal's one-shot token** (exclusive): it fires once. -/
def srvPropTk (γt : GName) : IProp GF := dghostVar γt (DFrac.own 1) ()

instance srvPropTk_timeless (γt : GName) : Timeless (srvPropTk (GF := GF) γt) := by
  unfold srvPropTk; infer_instance

theorem srvPropTk_excl (γt : GName) : ⊢ srvPropTk (GF := GF) γt -∗ srvPropTk γt -∗ False := by
  iintro H1 H2
  unfold srvPropTk
  ihave %Hv := dghostVar_valid_2 _ _ _ _ _ $$ H1 H2
  exfalso
  have h := DFrac.valid_own_op Hv.1
  exact absurd h (by decide)

/-- The token for registering `d` the first time (the server mints it, `srvPropMint`). -/
def srvPropFresh (γ : ServerRaftNames) (d : List w8) : IProp GF := d ↪[γ.raft.fresh] ()

/-- `d` was registered (persistent). -/
def srvDeposited (γ : ServerRaftNames) (d : List w8) : IProp GF :=
  iprop(∃ x : GName × GName, d ↪[γ.raft.props]□ x)

instance srvDeposited_persistent (γ : ServerRaftNames) (d : List w8) :
    Persistent (srvDeposited (GF := GF) γ d) := by
  unfold srvDeposited; infer_instance

/-- **A result predicate the server's two logs agree on** (persistent): it holds of a log as of
any log with the same requested entries (`srvEqv`), a step later (an update at `⊤`: a server
result's invariance reads the KV invariant's facts). The server's results are of the
KV model of the log, which the requested entries determine (`kvModel_eqv`). -/
def srvQInv (γ : ServerRaftNames) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(□ ∀ (A B : List EntryModel), ⌜srvEqv γ A B⌝ -∗ □ Q A ={⊤}=∗ ▷ □ Q B)

instance srvQInv_persistent (γ : ServerRaftNames) (Q : List EntryModel → IProp GF) :
    Persistent (srvQInv (GF := GF) γ Q) := by
  unfold srvQInv; infer_instance

/-- A predicate of the log's requested entries is one the logs agree on. -/
theorem srvQInv_of_eq (γ : ServerRaftNames) (Q : List EntryModel → IProp GF)
    (h : ∀ A B, srvEqv γ A B → Q A = Q B) : ⊢ srvQInv (GF := GF) γ Q := by
  unfold srvQInv
  iintro !> %A %B %Hab #HA
  rw [← h A B Hab]
  imodintro; inext; iexact HA

/-- **The proposer's handle on its proposal**, with result `Q` (persistent): `d` registered with
the result predicate `Q`, one the logs agree on. -/
def srvIsProp (γ : ServerRaftNames) (d : List w8) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ γQ γt : GName, d ↪[γ.raft.props]□ (γQ, γt) ∗ savedPredOwn γQ DFrac.discard Q ∗
    srvQInv γ Q)

instance srvIsProp_persistent (γ : ServerRaftNames) (d : List w8)
    (Q : List EntryModel → IProp GF) : Persistent (srvIsProp (GF := GF) γ d Q) := by
  unfold srvIsProp; infer_instance

/-- **The proposer's update for `d`, fired at most once** (the server's; unchanged since D21 M6):
fired at the requested entry `e` holding `d` (normal, at the next index of the server's log), its
result persistent and of the log before the entry. -/
def srvPropAu1 (γ : ServerRaftNames) (d : List w8) (Q : List EntryModel → IProp GF) :
    IProp GF :=
  iprop(AU <{ ∃∃ (L : List EntryModel), srvRLog γ L }> @ ⊤ \ ↑srvRaftN, ∅
          <{ ∀∀ (e : EntryModel),
               ⌜e.typ = W32 0 ∧ e.data = d ∧ uint.Z e.index = uint.Z γ.ai0 + 1 + L.length⌝ ∗
               srvRLog γ (L ++ [e]), COMM □ Q L }>)

/-- What `Propose` takes for `d`: its fresh token, its update, fired at most once, and its result
predicate's invariance. (2026-10-27: the invariance added.) -/
def srvPropArg (γ : ServerRaftNames) (d : List w8) (Q : List EntryModel → IProp GF) :
    IProp GF :=
  iprop(srvPropFresh γ d ∗ srvPropAu1 γ d Q ∗ srvQInv γ Q)

/-- What it gives back: `d` registered, and the proposal's handle. -/
def srvPropRes (γ : ServerRaftNames) (d : List w8) (Q : List EntryModel → IProp GF) :
    IProp GF :=
  iprop(srvDeposited γ d ∗ srvIsProp γ d Q)

/-- **The proposals' witnesses** (persistent): for a registered proposal of `d` with result `Q`
and an entry `e` of data `d` (not empty) at position `m` of a committed log `L`, `□ Q` of the log
before it (`L.take m`), for three later credits (the registry's invariant, the result predicate's
agreement and its invariance). (2026-10-27: until then two credits, raft's collection.) -/
def srvPropWits (γ : ServerRaftNames) : IProp GF :=
  iprop(□ ∀ (d : List w8) (Q : List EntryModel → IProp GF) (L : List EntryModel) (m : Nat)
      (e : EntryModel),
    srvIsProp γ d Q -∗ srvRLogLb γ L -∗ ⌜L[m]? = some e ∧ e.typ = W32 0 ∧ e.data = d ∧ d ≠ []⌝ -∗
      £ 3 ={⊤}=∗ □ Q (L.take m))

instance srvPropWits_persistent (γ : ServerRaftNames) : Persistent (srvPropWits (GF := GF) γ) := by
  unfold srvPropWits; infer_instance

/-- **A read's persistent update** (the server's; unchanged): the log unchanged, a persistent
result; and (2026-10-27) the result predicate one the logs agree on. -/
def srvReadAu (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop((□ AU <{ ∃∃ (L : List EntryModel), srvRLog γ L }> @ ⊤ \ ↑srvRaftN, ∅
          <{ srvRLog γ L, COMM □ Qr L }>) ∗ srvQInv γ Qr)

instance srvReadAu_persistent (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF) :
    Persistent (srvReadAu (GF := GF) γ Qr) := by
  unfold srvReadAu; infer_instance

/-- **A read's witness at the read index `i`** (persistent): `□ Qr L` of every committed log `L`
through a raft index at least `i`, for five later credits (raft's read state, two; the server's
log invariant, the result predicate's agreement, its invariance). -/
def srvReadWit (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF) (i : w64) : IProp GF :=
  iprop(□ ∀ L : List EntryModel, srvRLogLb γ L -∗ ⌜uint.Z i ≤ uint.Z γ.ai0 + L.length⌝ -∗
    £ 5 ={⊤}=∗ □ Qr L)

instance srvReadWit_persistent (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF)
    (i : w64) : Persistent (srvReadWit (GF := GF) γ Qr i) := by
  unfold srvReadWit; infer_instance


/-- **The fresh token of a read context** `c` (the server mints it from its id generator). -/
def srvRdFresh (γ : ServerRaftNames) (c : List w8) : IProp GF := c ↪[γ.raft.rdFresh] ()

/-! ### The server's log invariant -/

/-- **The log invariant's timeless part**, at the server's log `Lf` of requested entries: the node
API's committed requested entries (`pre`'s and `Lf`'s), the other half of `Lf`; the proposals'
registry `P` (each registered data's fresh token kept), the fired proposals `F`, the reads `R`;
`Lf` consecutive, without fillers, each of its normal entries fired at the log before it, each
read registered at most at `Lf`'s length. -/
def srvLogCore (γ : ServerRaftNames) (Lf : List EntryModel) (P : GMap (List w8) (GName × GName))
    (F : GMap (List w8) (List EntryModel)) (R : List (GName × Nat)) : IProp GF :=
  iprop(ownCommittedOps γ.raft.cl (opsOf (srvLE γ Lf)) ∗
    monoListAuthOwn γ.raft.log (1 : Qp).half Lf ∗
    ghostMapAuth γ.raft.props 1 P ∗ ghostMapAuth γ.raft.fired 1 F ∗
    monoListAuthOwn γ.raft.pend 1 R ∗
    ([∗map] d ↦ _x ∈ P, d ↪[γ.raft.fresh] ()) ∗
    ⌜srvIdxOkW γ.ai0 Lf ∧ (∀ m ∈ Lf, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2) ∧
      (∀ (j : Nat) (m : EntryModel), Lf[j]? = some m → m.typ = W32 0 →
        F.lookup m.data = some (Lf.take j)) ∧
      (∀ r ∈ R, r.2 ≤ Lf.length) ∧
      -- (2026-10-30, the repair; D3) its conf entries changes the server takes (the boot log's)
      (∀ m ∈ Lf, m.typ = W32 1 → ccPolOk γ.raft m.data)⌝)

instance srvLogCore_timeless (γ : ServerRaftNames) (Lf : List EntryModel)
    (P : GMap (List w8) (GName × GName)) (F : GMap (List w8) (List EntryModel))
    (R : List (GName × Nat)) : Timeless (srvLogCore (GF := GF) γ Lf P F R) := by
  unfold srvLogCore; infer_instance

/-- A registered read, at the server's log `Lf`: its result predicate (saved), its update, and its
result at every log from its registration to `Lf`. -/
def srvPendRead (γ : ServerRaftNames) (Lf : List EntryModel) (r : GName × Nat) : IProp GF :=
  iprop(∃ Qr : List EntryModel → IProp GF, savedPredOwn r.1 DFrac.discard Qr ∗ srvReadAu γ Qr ∗
    □ (∀ j : Nat, ⌜r.2 ≤ j ∧ j ≤ Lf.length⌝ -∗ □ Qr (Lf.take j)))

instance srvPendRead_persistent (γ : ServerRaftNames) (Lf : List EntryModel) (r : GName × Nat) :
    Persistent (srvPendRead (GF := GF) γ Lf r) := by
  unfold srvPendRead; infer_instance

/-- **The log invariant's other part**: each fired proposal's result at the log before its entry
(with its one-shot token), and the registered reads. -/
def srvLogRegs (γ : ServerRaftNames) (Lf : List EntryModel)
    (F : GMap (List w8) (List EntryModel)) (R : List (GName × Nat)) : IProp GF :=
  iprop(([∗map] d ↦ Lb ∈ F, ∃ (γQ γt : GName) (Q : List EntryModel → IProp GF),
      d ↪[γ.raft.props]□ (γQ, γt) ∗ savedPredOwn γQ DFrac.discard Q ∗ □ Q Lb ∗ srvPropTk γt) ∗
    [∗list] r ∈ R, srvPendRead γ Lf r)

/-- **The server's log invariant**. -/
def srvLogInv (γ : ServerRaftNames) : IProp GF :=
  inv srvLogN iprop(∃ (Lf : List EntryModel) (P : GMap (List w8) (GName × GName))
      (F : GMap (List w8) (List EntryModel)) (R : List (GName × Nat)),
    srvLogCore γ Lf P F R ∗ srvLogRegs γ Lf F R)

instance srvLogInv_persistent (γ : ServerRaftNames) : Persistent (srvLogInv (GF := GF) γ) := by
  unfold srvLogInv; infer_instance

/-- **The cluster** (persistent; 2026-10-30, the repair: one kind of cluster, raft's unified API):
the node API's cluster at the server's storage model (`srvStor`); its conf entries decided by the
server's rule (`confPolicy` at `γ.raft.rule`; `rnEnvOk` ties it to `srvRule`); the voters it started
with (`confAt 0`); the `Ready`s' entries within `MemoryStorage.Append`'s bound (`readyFits`);
proposals not duplicated (`dup = false`); and (D2(i), the user's decision 2026-10-30) the cluster's
snapshot registry held empty for good (`ownSnapsMade cl []` in an invariant): the server makes no
snapshot, so every snapshot certificate, snapshot validity, `MsgSnap` and `Ready` snapshot is
refuted (`srv_snapMade_false`). Until the repair: a static or dynamic cluster
(`isStaticCluster`/`isDynamicCluster`), leader transfer off, `bootedCluster`. -/
def srvClusterOk (γ : ServerRaftNames) : IProp GF :=
  letI := srvStor (GF := GF) γ.raft
  iprop(isCluster γ.raft.cl srvClusterN ∗ confPolicy γ.raft.cl srvConfN γ.raft.rule ∗
    confAt γ.raft.cl 0 (Membership.simple γ.raft.cfg) ∗ readyFits γ.raft.cl srvClusterN ∗
    ⌜γ.raft.cl.dup = false⌝ ∗ inv srvSnapsN (ownSnapsMade γ.raft.cl []) ∗
    ⌜srvRuleKeeps γ.raft.rule γ.raft.cfg⌝)

instance srvClusterOk_persistent (γ : ServerRaftNames) : Persistent (srvClusterOk (GF := GF) γ) := by
  unfold srvClusterOk; infer_instance

/-- **Raft's committed log, at the server** (persistent; the contract's ghost interface): the
server's log invariant, the cluster, the start log committed and the start index its length; and
(2026-10-30, the repair: one mode, the old dynamic mode's fresh start) the start log empty, so the
start index `0`. (2026-10-27: until then raft's commit invariant and the conf-change policy.) -/
def srvRaftLogInv (γ : ServerRaftNames) : IProp GF :=
  iprop(srvLogInv γ ∗ srvClusterOk γ ∗ srvRLogLb γ [] ∗ ⌜uint.Z γ.ai0 = γ.pre.length⌝ ∗
    ⌜γ.pre = []⌝)

instance srvRaftLogInv_persistent (γ : ServerRaftNames) :
    Persistent (srvRaftLogInv (GF := GF) γ) := by
  unfold srvRaftLogInv; infer_instance

theorem srvRaftLogInv_facts (γ : ServerRaftNames) :
    srvRaftLogInv (GF := GF) γ ⊢ ⌜uint.Z γ.ai0 = γ.pre.length⌝ := by
  unfold srvRaftLogInv
  iintro ⟨-, -, -, %H, -⟩
  ipureintro; exact H

end regs

/-! ## Pure facts of the two logs -/

section purefacts
variable [GooseExts]

theorem srvLE_ops_nofill (γ : ServerRaftNames) (L : List EntryModel)
    (h : ∀ m ∈ L, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2) :
    opsOf (srvLE γ L) = opsOf (srvLE γ []) ++ L.map EntryModel.toLE := by
  have : srvLE γ L = srvLE γ [] ++ L.map EntryModel.toLE := by
    rw [← srvLE_append]; rfl
  rw [this, opsOf_append, opsOf_nofill (L.map EntryModel.toLE)]
  intro e he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
  exact h m hm

theorem srvLE_ops (γ : ServerRaftNames) (A : List EntryModel) :
    opsOf (srvLE γ A) = opsOf (srvLE γ []) ++ opsOf (A.map EntryModel.toLE) := by
  have : srvLE γ A = srvLE γ [] ++ A.map EntryModel.toLE := by
    rw [← srvLE_append]; rfl
  rw [this, opsOf_append]

/-- A committed log's requested entries, as a prefix of the server's log's. -/
theorem srv_ops_prefix (γ : ServerRaftNames) (A Lf : List EntryModel)
    (hnf : ∀ m ∈ Lf, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2)
    (h : opsOf (srvLE γ A) <+: opsOf (srvLE γ Lf)) :
    opsOf (A.map EntryModel.toLE) <+: Lf.map EntryModel.toLE := by
  rw [srvLE_ops, srvLE_ops_nofill γ Lf hnf] at h
  exact (List.prefix_append_right_inj _).1 h

/-- The server's log after one more requested entry has a next index that fits: the committed
log `l` holding its requested entries extends the start log. -/
theorem srv_next_bound (γ : ServerRaftNames) (Lf : List EntryModel) (l : List LogEntry)
    (x : LogEntry) (hnf : ∀ m ∈ Lf, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2)
    (hops : opsOf l = opsOf (srvLE γ Lf) ++ [x])
    (hag : srvLE γ [] <+: l ∨ l <+: srvLE γ []) :
    γ.pre.length + Lf.length + 1 ≤ l.length := by
  rw [srvLE_ops_nofill γ Lf hnf] at hops
  rcases hag with ⟨r, rfl⟩ | h
  · rw [opsOf_append] at hops
    have h2 := List.append_cancel_left (hops.trans (List.append_assoc _ _ _))
    have := opsOf_length_le r
    rw [h2] at this
    simp [srvLE] at this ⊢
    omega
  · have := (opsOf_prefix h).length_le
    rw [hops] at this
    simp at this; omega

end purefacts

/-! ## The server's half and the committed log -/

section lb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server's half bounds every prefix of the committed log**, by their requested entries:
a committed log's requested entries are those of a prefix of the server's log (2026-10-27: until
then the committed log itself was a prefix of the server's, which held raft's fillers too). -/
theorem srvRLog_lb (γ : ServerRaftNames) (E : CoPset) (hE0 : ↑srvRaftN ⊆ E)
    (L A : List EntryModel) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvRLog γ L -∗ srvRLogLb γ A ={E}=∗
      srvRLog γ L ∗ ⌜srvIdxOkW γ.ai0 L ∧ (∀ m ∈ L, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2) ∧
        opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE⌝ := by
  have hE : (↑srvLogN : CoPset) ⊆ E := fun p hp => hE0 p (srvLogN_sub p hp)
  iintro #Hinv HL #HA
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, -⟩
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfr, %Hfacts⟩
  iunfold srvRLog at HL
  ihave %Hag := monoListAuthOwn_agree $$ Hlog HL
  obtain ⟨-, rfl⟩ := Hag
  iunfold srvRLogLb at HA
  icases HA with ⟨#HA, %HAi⟩
  ihave %Hp := ownCommittedOps_lb_prefix γ.raft.cl _ _ $$ [Hown HA]
  · iframe Hown HA
  imod Hclose $$ [Hown Hlog HP HF HR Hfr Hregs] with -
  · inext
    iexists Lf, P, F, R
    iunfold srvLogCore
    iframe Hown Hlog HP HF HR Hfr Hregs
    ipureintro; exact Hfacts
  imodintro
  iunfold srvRLog
  iframe HL
  ipureintro
  exact ⟨Hfacts.1, Hfacts.2.1, srv_ops_prefix γ A Lf Hfacts.2.1 Hp⟩

/-- (2026-10-30, the repair; D3) **The cluster's membership is the voters' at every index of a
committed log**: each conf entry of it is one of the server's log's (`srv_entry_src`: the boot
log's, whose changes the server takes, the log invariant's `ccPolOk`) or an empty `ConfChangeV2`
(raft's, to leave a joint configuration), each decided by the cluster's rule (`confPolicy_decide`),
which keeps `simple cfg` (`srvRuleKeeps`), from the voters' at `0` (`srvClusterOk`). -/
theorem srv_confAt_simple (γ : ServerRaftNames) (l : List LogEntry) (k : Nat) (hk : k ≤ l.length)
    (E : CoPset) (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) γ ∗ isCommittedLogLb γ.raft.cl l ⊢
      |={E}=> (letI := srvStor (GF := GF) γ.raft
        confAt γ.raft.cl k (Membership.simple γ.raft.cfg)) := by
  sorry

/-- (2026-10-30, the repair; D3) **No empty `ConfChangeV2` is committed**: raft commits one only at
a joint configuration (`committed_emptyV2_joint`), which the voters' simple one is not
(`srv_confAt_simple`). So every committed entry is a normal entry or a v1 conf change. -/
theorem srv_committed_noV2 (γ : ServerRaftNames) (l : List LogEntry)
    (E : CoPset) (hC : ↑srvConfN ⊆ E) (hL : ↑srvLogN ⊆ E) :
    srvRaftLogInv (GF := GF) γ ∗ isCommittedLogLb γ.raft.cl l ⊢
      |={E}=> ⌜∀ e ∈ l, ¬ e.isEmptyV2⌝ := by
  sorry
/-- **A committed log, as the server's** (2026-10-27): a committed log after the start log whose
indices are consecutive is a `srvRLogLb`: its entries are normal or v1 conf changes, its requested
entries being the server's (whose are), its fillers empty normal entries
(`LogEntry.isFiller_normal`); (2026-10-30, the repair) none an empty `ConfChangeV2`
(`srv_committed_noV2`). -/
theorem srvRLogLb_intro (γ : ServerRaftNames) (E : CoPset) (hE : ↑srvLogN ⊆ E)
    (hC : ↑srvConfN ⊆ E)
    (L : List EntryModel)
    (hidx : ∀ (n : Nat) (m : EntryModel), L[n]? = some m → uint.Z m.index = uint.Z γ.ai0 + 1 + n) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ isCommittedLogLb γ.raft.cl (srvLE γ L) ={E}=∗
      srvRLogLb γ L := by
  sorry
/- REPAIR-OLD
  iintro #Hinv #HL
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, -⟩
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfrs, %Hfacts⟩
  ihave %Hp := ownCommittedOps_lb_prefix γ.raft.cl _ _ $$ [Hown HL]
  · iframe Hown HL
  imod Hclose $$ [Hown Hlog HP HF HR Hfrs Hregs] with -
  · inext
    iexists Lf, P, F, R
    iunfold srvLogCore
    iframe Hown Hlog HP HF HR Hfrs Hregs
    ipureintro; exact Hfacts
  imodintro
  iunfold srvRLogLb
  iframe HL
  ipureintro
  obtain ⟨Hidx, Hnf, -, -⟩ := Hfacts
  have Hops := srv_ops_prefix γ L Lf Hnf Hp
  intro n m hm
  refine ⟨hidx n m hm, ?_⟩
  by_cases hf : m.toLE.isFiller
  · have : m.toLE ∈ srvLE γ L := by
      unfold srvLE; rw [List.map_append]
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_of_getElem? hm))
    exact .inl (LogEntry.isFiller_normal _ hf)
  · -- a requested entry: one of the server's
    have hin : m.toLE ∈ opsOf (L.map EntryModel.toLE) := by
      unfold opsOf
      rw [List.mem_filter]
      exact ⟨List.mem_map_of_mem (List.mem_of_getElem? hm), by simp [hf]⟩
    obtain ⟨m', hm', he⟩ := List.mem_map.1 (Hops.subset hin)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hm'
    have ht := (Hidx j m' hj).2
    have h1 := congrArg LogEntry.type he
    have h2 := congrArg LogEntry.data he
    simp only [EntryModel.toLE] at h1 h2
    rw [← h1, ← h2]; exact ht
-/


/-- **A prefix of the server's log of requested entries** (persistent; the auth-mode merge's step 5,
2026-10-29): a lower bound in the view of the KV invariant's log (`srvRLog`), which holds no raft
fillers; `srvRLogLb` bounds raft's committed log, fillers included, and converts to it
(`srvReqLogLb_of_rlogLb`). -/
def srvReqLogLb (γ : ServerRaftNames) (L : List EntryModel) : IProp GF :=
  monoListLbOwn γ.raft.log L

instance srvReqLogLb_persistent (γ : ServerRaftNames) (L : List EntryModel) :
    Persistent (srvReqLogLb (GF := GF) γ L) := by
  unfold srvReqLogLb; infer_instance

/-- The empty prefix. -/
theorem srvReqLogLb_nil (γ : ServerRaftNames) : ⊢ |==> srvReqLogLb (GF := GF) γ [] := by
  unfold srvReqLogLb; exact monoListLbOwn_nil _

/-- The server's half extends every prefix. -/
theorem srvReqLogLb_prefix (γ : ServerRaftNames) (L L₀ : List EntryModel) :
    srvRLog (GF := GF) γ L ∗ srvReqLogLb γ L₀ ⊢ srvRLog γ L ∗ ⌜L₀ <+: L⌝ := by
  unfold srvRLog srvReqLogLb
  iintro ⟨Hl, #Hlb⟩
  ihave %Hp := mono_list_auth_lb_valid γ.raft.log _ L L₀ $$ Hl Hlb
  iframe Hl
  ipureintro; exact Hp.2

/-- **A committed prefix as a prefix of the requested entries**: a lower bound of raft's committed
log gives one of the server's log with the same requested entries. -/
theorem srvReqLogLb_of_rlogLb (γ : ServerRaftNames) (E : CoPset) (hE0 : ↑srvRaftN ⊆ E)
    (A : List EntryModel) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvRLogLb γ A ={E}=∗
      ∃ L₀, srvReqLogLb γ L₀ ∗ ⌜srvEqv γ A L₀⌝ := by
  have hE : (↑srvLogN : CoPset) ⊆ E := fun p hp => hE0 p (srvLogN_sub p hp)
  iintro #Hinv #HA
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, -⟩
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfr, %Hfacts⟩
  ihave #Hlb := monoListLbOwn_get γ.raft.log _ Lf $$ Hlog
  iunfold srvRLogLb at HA
  icases HA with ⟨#HAc, %HAi⟩
  ihave %Hp := ownCommittedOps_lb_prefix γ.raft.cl _ _ $$ [Hown HAc]
  · iframe Hown HAc
  imod Hclose $$ [Hown Hlog HP HF HR Hfr Hregs] with -
  · inext
    iexists Lf, P, F, R
    iunfold srvLogCore
    iframe Hown Hlog HP HF HR Hfr Hregs
    ipureintro; exact Hfacts
  have hpre := srv_ops_prefix γ A Lf Hfacts.2.1 Hp
  let k := (opsOf (A.map EntryModel.toLE)).length
  have htk : (Lf.take k).map EntryModel.toLE = opsOf (A.map EntryModel.toLE) := by
    rw [List.map_take]
    obtain ⟨r, hr⟩ := hpre
    rw [← hr]; simp [k]
  imodintro
  iexists Lf.take k
  isplitl
  · iunfold srvReqLogLb
    iapply monoListLbOwn_le _ (List.take_prefix _ _) $$ Hlb
  ipureintro
  refine ⟨HAi, srvIdxOkW_prefix _ _ _ Hfacts.1 (List.take_prefix _ _), ?_⟩
  rw [opsOf_nofill ((Lf.take k).map EntryModel.toLE), htk]
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    exact Hfacts.2.1 m (List.mem_of_mem_take hm)

end lb

/-! ## The server's updates as the node API's -/

section bridges
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

theorem srv_mask_inner : (⊤ \ ↑srvRaftN : CoPset) ⊆ (⊤ \ ↑srvClusterN) \ ↑srvLogN :=
  mask_diff_ndot2 srvRaftN "cluster" "log"

/-- **Firing the registered reads** at the server's log after one more entry `e`: each read's
update, at the log `Lf ++ [e]` (the KV invariant's half, through the update). -/
theorem srvFireReads (γ : ServerRaftNames) (Lf : List EntryModel) (e : EntryModel) :
    ∀ (R : List (GName × Nat)),
    ⊢ monoListAuthOwn (GF := GF) γ.raft.log (1 : Qp).half (Lf ++ [e]) -∗
      ([∗list] r ∈ R, srvPendRead γ Lf r) ={⊤ \ ↑srvRaftN}=∗
      monoListAuthOwn γ.raft.log (1 : Qp).half (Lf ++ [e]) ∗
      [∗list] r ∈ R, srvPendRead γ (Lf ++ [e]) r
  | [] => by
    iintro Hlog -
    imodintro
    iframe Hlog
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | r :: R => by
    iintro Hlog Hrs
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    imod srvFireReads γ Lf e R $$ Hlog Hrs with ⟨Hlog, Hrs⟩
    iunfold srvPendRead at Hr
    icases Hr with ⟨%Qr, #HQs, #Hau, #Hres⟩
    iunfold srvReadAu at Hau
    icases Hau with ⟨#Hau, #Hinv⟩
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%L, HL, Hcl⟩
    iunfold srvRLog at HL
    ihave %Hag := monoListAuthOwn_agree $$ Hlog HL
    obtain ⟨-, Heq⟩ := Hag
    subst Heq
    icases Hcl with ⟨-, Hcommit⟩
    imod Hcommit $$ [HL] with #HQL
    · iunfold srvRLog; iexact HL
    imodintro
    iframe Hlog
    iapply BigSepL.bigSepL_cons.2
    iframe Hrs
    iunfold srvPendRead
    iexists Qr
    iframe HQs
    isplitr
    · iunfold srvReadAu; iframe Hau Hinv
    iintro !> %j %Hj
    rcases Nat.lt_or_ge j (Lf ++ [e]).length with hj | hj
    · have hj' : j ≤ Lf.length := by simp at hj; omega
      rw [List.take_append_of_le_length hj']
      iapply Hres
      ipureintro; exact ⟨Hj.1, hj'⟩
    · have : j = (Lf ++ [e]).length := by omega
      rw [this, List.take_length]
      iexact HQL

/-- **Registering a proposal** of `d` with the result `Q`, by its fresh token: the registry's
element, the result predicate's name and the proposal's one-shot token. -/
theorem srvProp_register (γ : ServerRaftNames) (d : List w8) (Q : List EntryModel → IProp GF)
    (E : CoPset) (hE : ↑srvLogN ⊆ E) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvPropFresh γ d ={E}=∗
      ∃ γQ γt : GName, d ↪[γ.raft.props]□ (γQ, γt) ∗ savedPredOwn γQ DFrac.discard Q ∗
        srvPropTk γt := by
  iintro #Hinv Hfr
  imod saved_pred_alloc Q DFrac.discard DFrac.valid_discard with ⟨%γQ, #HQ⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htk⟩
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, -⟩
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfrs, %Hfacts⟩
  have hcase : P.lookup d = none ∨ ∃ x, P.lookup d = some x := by
    cases P.lookup d <;> simp
  rcases hcase with HPd | ⟨x, HPd⟩
  rotate_left
  · iexfalso
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun d _x => iprop(d ↪[γ.raft.fresh] ()))
      (m := P) HPd).1 $$ Hfrs with ⟨Hfr', -⟩
    iunfold srvPropFresh at Hfr
    ihave %Hne := ghostMapElem_ne γ.raft.fresh d d (DFrac.own 1) () () $$ Hfr Hfr'
    exact absurd rfl Hne
  imod ghost_map_insert_persist d (γQ, γt) HPd $$ HP with ⟨HP, #Hel⟩
  imod Hclose $$ [Hown Hlog HP HF HR Hfrs Hfr Hregs] with -
  · inext
    iexists Lf, P.insert d (γQ, γt), F, R
    iunfold srvLogCore
    iframe Hown Hlog HP HF HR Hregs
    isplitl [Hfrs Hfr]
    · iapply (BigSepM.bigSepM_insert (Φ := fun d _x => iprop(d ↪[γ.raft.fresh] ())) HPd).2
      iunfold srvPropFresh at Hfr
      iframe Hfr Hfrs
    ipureintro; exact Hfacts
  imodintro
  iexists γQ, γt
  iframe Hel HQ
  unfold srvPropTk
  iexact Htk

/-- The fired registry after one more fired proposal. -/
theorem srv_fired_snoc (Lf : List EntryModel) (F : GMap (List w8) (List EntryModel))
    (e : EntryModel) (d : List w8) (hed : e.data = d) (HFd : F.lookup d = none)
    (H : ∀ (j : Nat) (m : EntryModel), Lf[j]? = some m → m.typ = W32 0 →
      F.lookup m.data = some (Lf.take j)) :
    ∀ (j : Nat) (m : EntryModel), (Lf ++ [e])[j]? = some m → m.typ = W32 0 →
      (F.insert d Lf).lookup m.data = some ((Lf ++ [e]).take j) := by
  intro j m hm ht
  rcases Nat.lt_or_ge j Lf.length with hj | hj
  · rw [List.getElem?_append_left hj] at hm
    have h1 := H j m hm ht
    have hne : m.data ≠ d := fun h => by rw [h, HFd] at h1; cases h1
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne), h1, List.take_append_of_le_length (by omega)]
  · rw [List.getElem?_append_right hj] at hm
    have hj' : j = Lf.length := by
      have := (List.getElem?_eq_some_iff.mp hm).1
      simp only [List.length_singleton] at this
      omega
    subst hj'
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hm
    subst hm
    rw [hed, GMap.lookup_insert_eq, List.take_left]

/-- **A proposal's update, as the node API's `Propose` takes it** (2026-10-27): when raft commits
the requested entry `⟨t, normal, d⟩`, the server's log grows by it (its index the next of the
server's log), the server's update fires (the KV invariant's half), the registered reads fire again,
and the result is left in the registry. One later credit, for the registries. -/
theorem srvPropAu_api (γ : ServerRaftNames) (d : List w8) (Q : List EntryModel → IProp GF)
    (γQ γt : GName) (hd : d ≠ []) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ d ↪[γ.raft.props]□ (γQ, γt) -∗
      savedPredOwn γQ DFrac.discard Q -∗ srvPropTk γt -∗ £ 1 -∗ srvPropAu1 γ d Q -∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ.raft.cl ops }>
          @ ⊤ \ ↑srvClusterN, ∅
         <{ ∀∀ (t : w64), ownCommittedOps γ.raft.cl (ops ++ [⟨t, W32 0, d⟩]), COMM True }> := by
  sorry
/- REPAIR-OLD
  letI := srvAnyStor (GF := GF)
  iintro #Hinv #Hp #HQ Htk Hlc Hau
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, #Hcl, #Hlb0, %Hai0⟩
  iauintro
  unfold atomic_acc
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfrs, %Hfacts⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists opsOf (srvLE γ Lf)
  iframe Hown
  isplit
  · -- abort
    iintro Hown
    imod Hmask with -
    imod Hclose $$ [Hown Hlog HP HF HR Hfrs Hregs] with -
    · inext
      iexists Lf, P, F, R
      iunfold srvLogCore
      iframe Hown Hlog HP HF HR Hfrs Hregs
      ipureintro; exact Hfacts
    imodintro
    iframe Htk Hlc Hau
  · -- commit: the requested entry `⟨t, normal, d⟩`
    iintro %t Hown
    imod Hmask with -
    obtain ⟨Hidx, Hnf, Hfired, HRle⟩ := Hfacts
    imod lc_fupd_elim_later $$ Hlc Hregs with Hregs
    iunfold srvLogRegs at Hregs
    icases Hregs with ⟨HFr, HRr⟩
    -- the proposal fires once: not fired before
    have hcase : F.lookup d = none ∨ ∃ Lb, F.lookup d = some Lb := by
      cases F.lookup d <;> simp
    rcases hcase with HFd | ⟨Lb, HFd⟩
    rotate_left
    · iexfalso
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun d Lb => iprop(∃ (γQ γt : GName)
          (Q : List EntryModel → IProp GF), d ↪[γ.raft.props]□ (γQ, γt) ∗
          savedPredOwn γQ DFrac.discard Q ∗ □ Q Lb ∗ srvPropTk γt)) (m := F) HFd).1 $$ HFr
        with ⟨⟨%γQ', %γt', %Q', #Hp', -, -, Htk'⟩, -⟩
      ihave %Hag := ghostMapElem_agree d γ.raft.props _ _ _ _ $$ Hp Hp'
      cases Hag
      iapply srvPropTk_excl γt $$ Htk Htk'
    -- the next index fits
    ihave ⟨Hown, %l, #Hl, %Hlops⟩ := ownCommittedOps_get_lb γ.raft.cl _ $$ Hown
    ihave #Hcl' := Hcl
    iunfold srvClusterOk at Hcl'
    icases Hcl' with ⟨-, -, #Hfits, -⟩
    ihave %Hllen := isCommittedLogLb_length γ.raft.cl srvClusterN l $$ [Hfits Hl]
    · iframe Hfits Hl
    iunfold srvRLogLb at Hlb0
    icases Hlb0 with ⟨#Hl0, -⟩
    ihave %Hag0 := isCommittedLogLb_agree γ.raft.cl (srvLE γ []) l $$ [Hl0 Hl]
    · iframe Hl0 Hl
    have Hb := srv_next_bound γ Lf l ⟨t, W32 0, d⟩ Hnf Hlops Hag0
    let e : EntryModel := ⟨t, W64 (uint.Z γ.ai0 + 1 + Lf.length), W32 0, d⟩
    have He : uint.Z e.index = uint.Z γ.ai0 + 1 + Lf.length := by
      show uint.Z (W64 (uint.Z γ.ai0 + 1 + Lf.length)) = _
      have : (l.length : Int) ≥ γ.pre.length + Lf.length + 1 := by exact_mod_cast Hb
      word
    -- the server's update
    imod (fupd_mask_subseteq (PROP := IProp GF) srv_mask_inner) with Hback
    iunfold srvPropAu1 at Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%L, HL, Hcl⟩
    iunfold srvRLog at HL
    ihave %Hag := monoListAuthOwn_agree $$ Hlog HL
    obtain ⟨-, Heq⟩ := Hag
    subst Heq
    icombine Hlog HL as Hlog
    imod monoListAuthOwn_update_app [e] $$ Hlog with ⟨Hlog, -⟩
    icases ((monoListAuthOwn_fractional (GF := GF) γ.raft.log (Lf ++ [e])).fractional
        (1 : Qp).half (1 : Qp).half).1 $$ [Hlog] with ⟨Hlog, HL⟩
    · rw [Qp.half_add_half]; iexact Hlog
    icases Hcl with ⟨-, Hcommit⟩
    imod Hcommit $$ %e [HL] with #HQL
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, He⟩
      iunfold srvRLog; iexact HL
    -- the registered reads, again
    imod srvFireReads γ Lf e R $$ Hlog HRr with ⟨Hlog, HRr⟩
    imod Hback with -
    -- the registries
    imod ghost_map_insert d Lf HFd $$ HF with ⟨HF, -⟩
    have Hnfe : ¬ e.toLE.isFiller := fun h => hd h.1
    imod Hclose $$ [Hown Hlog HP HF HR Hfrs HFr HRr Htk] with -
    · inext
      iexists Lf ++ [e], P, F.insert d Lf, R
      iunfold srvLogCore
      have Hops : opsOf (srvLE γ Lf) ++ [⟨t, W32 0, d⟩] = opsOf (srvLE γ (Lf ++ [e])) := by
        rw [srvLE_append, opsOf_append, opsOf_nofill ([e].map EntryModel.toLE) (by simpa using Hnfe)]
        rfl
      rw [← Hops]
      iframe Hown Hlog HP HF HR Hfrs
      isplitr
      · ipureintro
        refine ⟨srvIdxOkW_snoc γ.ai0 Lf e Hidx He (Or.inl rfl), ?_,
          srv_fired_snoc Lf F e d rfl HFd Hfired, ?_⟩
        · intro m hm
          rcases List.mem_append.1 hm with hm | hm
          · exact Hnf m hm
          · rw [List.mem_singleton.1 hm]; exact Hnfe
        · intro r hr; have := HRle r hr; simp; omega
      iunfold srvLogRegs
      iframe HRr
      iapply (BigSepM.bigSepM_insert (Φ := fun d Lb => iprop(∃ (γQ γt : GName)
          (Q : List EntryModel → IProp GF), d ↪[γ.raft.props]□ (γQ, γt) ∗
          savedPredOwn γQ DFrac.discard Q ∗ □ Q Lb ∗ srvPropTk γt)) HFd).2
      iframe HFr
      iexists γQ, γt, Q
      iframe Hp HQ HQL Htk
    imodintro
    itrivial
-/

/-- Where a committed requested entry sits in the server's log. -/
theorem srv_pos (L Lf : List EntryModel) (m : Nat) (e : EntryModel) (hm : L[m]? = some e)
    (hnf : ¬ e.toLE.isFiller ∧ ¬ e.toLE.isEmptyV2)
    (h : opsOf (L.map EntryModel.toLE) <+: Lf.map EntryModel.toLE) :
    ∃ m', Lf[(opsOf ((L.take m).map EntryModel.toLE)).length]? = some m' ∧
      m'.toLE = e.toLE ∧
      (Lf.take (opsOf ((L.take m).map EntryModel.toLE)).length).map EntryModel.toLE =
        opsOf ((L.take m).map EntryModel.toLE) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hm
  have hd : L.drop m = e :: L.drop (m + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  have hL : L = L.take m ++ e :: L.drop (m + 1) := by
    rw [← hd]; exact (List.take_append_drop m L).symm
  have hmap : L.map EntryModel.toLE =
      (L.take m).map EntryModel.toLE ++ e.toLE :: (L.drop (m + 1)).map EntryModel.toLE := by
    have := congrArg (List.map EntryModel.toLE) hL
    rw [List.map_append, List.map_cons] at this
    exact this
  have hops : opsOf (L.map EntryModel.toLE) =
      opsOf ((L.take m).map EntryModel.toLE) ++ e.toLE ::
        opsOf ((L.drop (m + 1)).map EntryModel.toLE) := by
    rw [hmap, opsOf_append]
    congr 1
    simp only [opsOf, List.filter_cons, hnf, decide_false, Bool.not_false, ↓reduceIte]
  rw [hops] at h
  obtain ⟨r, hr⟩ := h
  generalize opsOf ((L.take m).map EntryModel.toLE) = a at hr ⊢
  have hlen : a.length < Lf.length := by
    have := congrArg List.length hr; simp at this; omega
  obtain ⟨m', hm'⟩ : ∃ m', Lf[a.length]? = some m' := ⟨_, List.getElem?_eq_getElem hlen⟩
  refine ⟨m', hm', ?_, ?_⟩
  · have := congrArg (fun l => l[a.length]?) hr
    simp only [List.getElem?_map, hm', Option.map_some] at this
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self] at this
    simpa using this.symm
  · rw [List.map_take, ← hr, List.append_assoc, List.take_left]

/-- **The proposals' witnesses, from the server's registry** (2026-10-27; until then from raft's,
`prop_collect`). -/
theorem srvPropWits_of (γ : ServerRaftNames) : ⊢ srvRaftLogInv (GF := GF) γ -∗ srvPropWits γ := by
  sorry
/- REPAIR-OLD
  letI := srvAnyStor (GF := GF)
  iintro #Hinv
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, -⟩
  iunfold srvPropWits
  iintro !> %d %Q %L %m %e #Hp #HL %Hf Hlc
  obtain ⟨Hlk, Het, Hed, Hne⟩ := Hf
  iunfold srvIsProp at Hp
  icases Hp with ⟨%γQ, %γt, #Hel, #HQ, #HQinv⟩
  iunfold srvRLogLb at HL
  icases HL with ⟨#HL, %HLi⟩
  icases (lc_split (n := 1) (m := 2)).1 $$ Hlc with ⟨Hlc1, Hlc⟩
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc2, Hlc3⟩
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfrs, %Hfacts⟩
  obtain ⟨Hidx, Hnf, Hfired, HRle⟩ := Hfacts
  ihave %Hp := ownCommittedOps_lb_prefix γ.raft.cl _ _ $$ [Hown HL]
  · iframe Hown HL
  have Hnfe : ¬ e.toLE.isFiller := fun h => Hne (Hed ▸ h.1)
  obtain ⟨m', Hm', Hme, Htk⟩ := srv_pos L Lf m e Hlk Hnfe (srv_ops_prefix γ L Lf Hnf Hp)
  generalize hj : (opsOf ((L.take m).map EntryModel.toLE)).length = j at Hm' Htk
  have Hm'd : m'.data = d ∧ m'.typ = W32 0 := by
    have h := congrArg LogEntry.data Hme
    have h2 := congrArg LogEntry.type Hme
    simp only [EntryModel.toLE] at h h2
    exact ⟨h.trans Hed, h2.trans Het⟩
  have HFd := Hfired j m' Hm' Hm'd.2
  rw [Hm'd.1] at HFd
  imod lc_fupd_elim_later $$ Hlc1 Hregs with Hregs
  iunfold srvLogRegs at Hregs
  icases Hregs with ⟨HFr, HRr⟩
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun d Lb => iprop(∃ (γQ γt : GName)
      (Q : List EntryModel → IProp GF), d ↪[γ.raft.props]□ (γQ, γt) ∗
      savedPredOwn γQ DFrac.discard Q ∗ □ Q Lb ∗ srvPropTk γt)) (m := F) HFd).1 $$ HFr
    with ⟨⟨%γQ', %γt', %Q', #Hel', #HQ', #HQL', Htk'⟩, Hacc⟩
  ihave %Hag := ghostMapElem_agree d γ.raft.props _ _ _ _ $$ Hel Hel'
  cases Hag
  ihave #Hsag := saved_pred_agree γQ DFrac.discard DFrac.discard Q' Q (Lf.take j) $$ HQ' HQ
  ihave HFr := Hacc $$ [Htk']
  · iexists γQ, γt, Q'
    iframe Hel' HQ' HQL' Htk'
  imod Hclose $$ [Hown Hlog HP HF HR Hfrs HFr HRr] with -
  · inext
    iexists Lf, P, F, R
    iunfold srvLogCore
    iunfold srvLogRegs
    iframe Hown Hlog HP HF HR Hfrs HFr HRr
    ipureintro; exact ⟨Hidx, Hnf, Hfired, HRle⟩
  ihave HQL : iprop(▷ □ Q (Lf.take j)) $$ []
  · inext
    ihave #Hiff := internalEq_iff _ _ $$ Hsag
    iintro !>
    icases Hiff with ⟨Hto, -⟩
    iapply Hto $$ HQL'
  imod lc_fupd_elim_later $$ Hlc2 HQL with #HQL
  iunfold srvQInv at HQinv
  imod HQinv $$ %(Lf.take j) %(L.take m) [] HQL with HQm
  · ipureintro
    refine ⟨srvIdxOkW_prefix γ.ai0 _ Lf Hidx (List.take_prefix _ _),
      srvIdxOkW_prefix γ.ai0 _ L HLi (List.take_prefix _ _), ?_⟩
    rw [opsOf_nofill _ (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact Hnf y (List.mem_of_mem_take hy)), Htk]
  imod lc_fupd_elim_later $$ Hlc3 HQm with #HQm
  imodintro
  iexact HQm
-/

/-- **What a read context's update records** (persistent), at the requested entries `ops` the
read took effect at: the read registered, at the server's log `Lk` whose requested entries those
are, with its result predicate. -/
def srvReadQ (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF)
    (ops : List LogEntry) : IProp GF :=
  iprop(∃ (γQ : GName) (k : Nat) (Lk : List EntryModel), monoListLbOwn γ.raft.log Lk ∗
    monoListIdxOwn γ.raft.pend k (γQ, Lk.length) ∗ savedPredOwn γQ DFrac.discard Qr ∗
    ⌜opsOf (srvLE γ Lk) = ops⌝)

instance srvReadQ_persistent (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF)
    (ops : List LogEntry) : Persistent (srvReadQ (GF := GF) γ Qr ops) := by
  unfold srvReadQ; infer_instance

/-- **A read's update, as a read context's** (2026-10-27): when the read takes effect, the server's
read update fires at the server's log, and the read is registered, to fire again at every later
requested entry (`srvPropAu_api`). -/
theorem srvReadAu_api (γ : ServerRaftNames) (Qr : List EntryModel → IProp GF) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvReadAu γ Qr -∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ.raft.cl ops }>
          @ ⊤ \ ↑srvClusterN, ∅
         <{ ownCommittedOps γ.raft.cl ops, COMM □ srvReadQ γ Qr ops }> := by
  sorry
/- REPAIR-OLD
  iintro #Hinv #Hra
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, -⟩
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfrs, %Hfacts⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists opsOf (srvLE γ Lf)
  iframe Hown
  isplit
  · iintro Hown
    imod Hmask with -
    imod Hclose $$ [Hown Hlog HP HF HR Hfrs Hregs] with -
    · inext
      iexists Lf, P, F, R
      iunfold srvLogCore
      iframe Hown Hlog HP HF HR Hfrs Hregs
      ipureintro; exact Hfacts
    imodintro
    itrivial
  · iintro Hown
    imod Hmask with -
    obtain ⟨Hidx, Hnf, Hfired, HRle⟩ := Hfacts
    -- the read's update, at the server's log
    imod (fupd_mask_subseteq (PROP := IProp GF) srv_mask_inner) with Hback
    ihave #Hra' := Hra
    iunfold srvReadAu at Hra'
    icases Hra' with ⟨#Hau, -⟩
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%L, HL, Hcl⟩
    iunfold srvRLog at HL
    ihave %Hag := monoListAuthOwn_agree $$ Hlog HL
    obtain ⟨-, Heq⟩ := Hag
    subst Heq
    icases Hcl with ⟨-, Hcommit⟩
    imod Hcommit $$ [HL] with #HQL
    · iunfold srvRLog; iexact HL
    imod Hback with -
    -- registered
    imod saved_pred_alloc Qr DFrac.discard DFrac.valid_discard with ⟨%γQ, #HQ⟩
    imod monoListAuthOwn_update_app [(γQ, Lf.length)] $$ HR with ⟨HR, #HRlb⟩
    ihave #Hix := monoListIdxOwn_get (γ := γ.raft.pend) R.length (γQ, Lf.length)
      (by simp) $$ HRlb
    ihave #Hlb := monoListLbOwn_get γ.raft.log _ Lf $$ Hlog
    imod Hclose $$ [Hown Hlog HP HF HR Hfrs Hregs] with -
    · inext
      iexists Lf, P, F, R ++ [(γQ, Lf.length)]
      iunfold srvLogCore
      iunfold srvLogRegs at Hregs
      icases Hregs with ⟨HFr, HRr⟩
      iunfold srvLogRegs
      iframe Hown Hlog HP HF HR Hfrs HFr
      isplitr
      · ipureintro
        refine ⟨Hidx, Hnf, Hfired, ?_⟩
        intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact HRle r hr
        · rw [List.mem_singleton.1 hr]; exact Nat.le_refl _
      iapply BigSepL.bigSepL_snoc.2
      iframe HRr
      iunfold srvPendRead
      iexists Qr
      iframe HQ Hra
      iintro !> %j %Hj
      have : j = Lf.length := by simp at Hj; omega
      rw [this, List.take_length]
      iexact HQL
    imodintro
    iintro !>
    iunfold srvReadQ
    iexists γQ, R.length, Lf
    iframe Hlb Hix HQ
    ipureintro; rfl
-/

/-- **A read's witness, from a read state** (2026-10-27; until then from raft's, `read_collect`):
the read state of a context committed to the server's read (`srvReadQ`). -/
theorem srvReadWit_of (γ : ServerRaftNames) (c : List w8) (Qr : List EntryModel → IProp GF)
    (i : w64) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ readStateOk γ.raft.cl srvClusterN c i -∗
      isReadCtx γ.raft.cl srvClusterN c (srvReadQ γ Qr) -∗ srvReadWit γ Qr i := by
  sorry
/- REPAIR-OLD
  letI := srvAnyStor (GF := GF)
  iintro #Hinv #Hst #Hctx
  iunfold srvRaftLogInv at Hinv
  icases Hinv with ⟨#Hli, -, -, %Hai0⟩
  iunfold srvReadWit
  iintro !> %L #HL %Hi Hlc
  iunfold srvRLogLb at HL
  icases HL with ⟨#HL, %HLi⟩
  icases (lc_split (n := 2) (m := 3)).1 $$ Hlc with ⟨Hlc2, Hlc⟩
  icases (lc_split (n := 1) (m := 2)).1 $$ Hlc with ⟨Hlc3, Hlc⟩
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc4, -⟩
  have Hle : uint.nat i ≤ (srvLE γ L).length := by
    rw [srvLE_length]
    have : (uint.nat i : Int) = uint.Z i := by word
    omega
  imod readStateOk_ctx γ.raft.cl srvClusterN c i (srvReadQ γ Qr) (srvLE γ L) ⊤
    (fun _ _ => CoPset.mem_full) Hle $$ Hst Hctx HL with ⟨%l, %Hll, #Hl, HQ⟩
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc2 with ⟨Hlc2a, Hlc2b⟩
  imod lc_fupd_elim_later $$ Hlc2a HQ with HQ
  imod lc_fupd_elim_later $$ Hlc2b HQ with #HQ
  iunfold srvReadQ at HQ
  icases HQ with ⟨%γQ, %k, %Lk, #HLk, #Hix, #HQs, %HLkops⟩
  -- `l` is a prefix of `pre ++ L`
  ihave %Hlag := isCommittedLogLb_agree γ.raft.cl l (srvLE γ L) $$ [Hl HL]
  · iframe Hl HL
  have HlL : opsOf l <+: opsOf (srvLE γ L) := by
    rcases Hlag with h | h
    · exact opsOf_prefix h
    · have hl := h.length_le
      have : l = srvLE γ L := (h.eq_of_length (by omega)).symm
      rw [this]; exact List.prefix_refl _
  iunfold srvLogInv at Hli
  iinv Hli with ⟨%Lf, %P, %F, %R, >Hcore, Hregs⟩ Hclose
  iunfold srvLogCore at Hcore
  icases Hcore with ⟨Hown, Hlog, HP, HF, HR, Hfrs, %Hfacts⟩
  obtain ⟨Hidx, Hnf, Hfired, HRle⟩ := Hfacts
  ihave %Hp := ownCommittedOps_lb_prefix γ.raft.cl _ _ $$ [Hown HL]
  · iframe Hown HL
  ihave %HLkp := mono_list_auth_lb_valid γ.raft.log _ Lf Lk $$ Hlog HLk
  ihave %HRk := mono_list_auth_idx_lookup γ.raft.pend 1 R k _ $$ HR Hix
  have HLops := srv_ops_prefix γ L Lf Hnf Hp
  have HLknf : ∀ m ∈ Lk, ¬ m.toLE.isFiller := fun m hm => Hnf m (HLkp.2.subset hm)
  -- the read was registered before `L`'s requested entries
  have HLkle : Lk.length ≤ (opsOf (L.map EntryModel.toLE)).length := by
    rw [← HLkops, srvLE_ops_nofill γ Lk HLknf, srvLE_ops γ L] at HlL
    have := ((List.prefix_append_right_inj _).1 HlL).length_le
    simpa using this
  have Hjle : (opsOf (L.map EntryModel.toLE)).length ≤ Lf.length := by
    have := HLops.length_le; simpa using this
  imod lc_fupd_elim_later $$ Hlc3 Hregs with Hregs
  iunfold srvLogRegs at Hregs
  icases Hregs with ⟨HFr, HRr⟩
  ihave #Hpend := (BigSepL.bigSepL_lookup (Φ := fun _ r => srvPendRead (GF := GF) γ Lf r) HRk) $$ HRr
  iunfold srvPendRead at Hpend
  icases Hpend with ⟨%Qr', #HQs', #Hra', #Hres⟩
  ihave #HQL := Hres $$ %(opsOf (L.map EntryModel.toLE)).length []
  · ipureintro; exact ⟨HLkle, Hjle⟩
  iunfold srvReadAu at Hra'
  icases Hra' with ⟨-, #HQinv⟩
  iunfold srvQInv at HQinv
  have Heqv : srvEqv γ (Lf.take (opsOf (L.map EntryModel.toLE)).length) L := by
    refine ⟨srvIdxOkW_prefix γ.ai0 _ Lf Hidx (List.take_prefix _ _), HLi, ?_⟩
    rw [opsOf_nofill _ (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact Hnf y (List.mem_of_mem_take hy))]
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 HLops).symm
  ihave #Hsag := saved_pred_agree γQ DFrac.discard DFrac.discard Qr' Qr L $$ HQs' HQs
  imod Hclose $$ [Hown Hlog HP HF HR Hfrs HFr HRr] with -
  · inext
    iexists Lf, P, F, R
    iunfold srvLogCore
    iunfold srvLogRegs
    iframe Hown Hlog HP HF HR Hfrs HFr HRr
    ipureintro; exact ⟨Hidx, Hnf, Hfired, HRle⟩
  imod HQinv $$ %_ %L %Heqv HQL with HQL'
  ihave HQr : iprop(▷ □ Qr L) $$ [HQL']
  · inext
    ihave #HQL' := HQL'
    ihave #Hiff := internalEq_iff _ _ $$ Hsag
    iintro !>
    icases Hiff with ⟨Hto, -⟩
    iapply Hto $$ HQL'
  imod lc_fupd_elim_later $$ Hlc4 HQr with #HQr
  imodintro
  iexact HQr
-/

/-- **No snapshot is made in the server's cluster** (2026-10-30, the repair; D2(i), the user's
decision): the cluster's snapshot registry is empty for good (`srvClusterOk`'s invariant), so a
made snapshot is refuted (`snapMade_elem`). The masks the server's updates leave contain
`srvSnapsN`. -/
theorem srv_snapMade_false (γ : ServerRaftNames) (s : SnapRec) (E : CoPset)
    (hE : ↑srvSnapsN ⊆ E) :
    srvClusterOk (GF := GF) γ ∗ (letI := srvStor (GF := GF) γ.raft; snapMade γ.raft.cl s) ⊢
      |={E}=> False := by
  sorry

/-- **No snapshot certificate in the server's cluster** (D2(i)): `snapshotCert_made`, then
`srv_snapMade_false`. -/
theorem srv_snapshotCert_false (γ : ServerRaftNames) (k : SnapTrip) (E : CoPset)
    (hE : ↑srvSnapsN ⊆ E) :
    srvClusterOk (GF := GF) γ ∗
      (letI := srvStor (GF := GF) γ.raft; snapshotCert γ.raft.cl srvClusterN k) ⊢
      |={E}=> False := by
  sorry

/-- **No valid snapshot in the server's cluster** (D2(i)): what the storage's `Snapshot()` answers
of a non-empty snapshot (`isStorage`'s `snapshotValid`) is refuted. -/
theorem srv_snapshotValid_false (γ : ServerRaftNames) (sv : SnapshotM) (E : CoPset)
    (hE : ↑srvSnapsN ⊆ E) :
    srvClusterOk (GF := GF) γ ∗
      (letI := srvStor (GF := GF) γ.raft; snapshotValid γ.raft.cl sv) ⊢
      |={E}=> False := by
  sorry

/-- **The server's cluster sends no `MsgSnap`** (2026-10-27; 2026-10-30, the repair, D2(i): a
`MsgSnap` carries a snapshot certificate, `sentMsg_snapshot`, refuted by
`srv_snapshotCert_false`; until then a dynamic cluster sent none and a static one vouched for no
snapshot's data). -/
theorem srv_sentMsg_notSnap (γ : ServerRaftNames) (src : w64) (st : MsgSt) (E : CoPset)
    (hE : ↑srvSnapsN ⊆ E) :
    srvClusterOk (GF := GF) γ ∗
      (letI := srvStor (GF := GF) γ.raft; sentMsg γ.raft.cl srvClusterN src st) ⊢
      |={E}=> ⌜st.msg.Type' ≠ MsgSnap⌝ := by
  sorry

/-- **The server's cluster's `Ready`s carry no snapshot** (2026-10-27; 2026-10-30, the repair,
D2(i): a `Ready`'s snapshot comes with its certificate, `readySnap`, refuted by
`srv_snapshotCert_false`), at the server's storage model. -/
theorem srv_readySnap_none (γ : ServerRaftNames) (id : w64) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (l : SnapLoan) (E : CoPset) (hE : ↑srvSnapsN ⊆ E) :
    srvClusterOk (GF := GF) γ ∗
      (letI := srvStor (GF := GF) γ.raft
       readySnap γ.raft.cl srvClusterN id rd st ce es (some l)) ⊢ |={E}=> False := by
  sorry
/- REPAIR-OLD
/-- **The server's cluster sends no `MsgSnap`** (2026-10-27): a dynamic cluster sends none, a static
one vouches for no snapshot's data. -/
theorem srv_sentMsg_notSnap (γ : ServerRaftNames) (src : w64) (st : MsgSt) :
    srvClusterOk (GF := GF) γ ∗ sentMsg γ.raft.cl srvClusterN src st ⊢
      ⌜st.msg.Type' ≠ MsgSnap⌝ := by
  letI := srvAnyStor (GF := GF)
  iintro ⟨#Hcl, #Hs⟩
  iunfold srvClusterOk at Hcl
  cases hd : γ.raft.dyn
  · isimp only [hd, Bool.false_eq_true, ↓reduceIte] at Hcl
    icases Hcl with ⟨#Hk, -, -, -⟩
    by_cases hsn : st.msg.Type' = MsgSnap
    · iexfalso
      icases sentMsg_snapshot γ.raft.cl srvClusterN src st hsn $$ Hs with ⟨%sv, -, #Hc⟩
      icases snapshotCert_data γ.raft.cl srvClusterN γ.raft.vs (fun _ _ => False) _
        $$ [Hk Hc] with ⟨%l, -, %Hf⟩
      · iframe Hk Hc
      exact Hf.2.elim
    · ipureintro; exact hsn
  · isimp only [hd, ↓reduceIte] at Hcl
    icases Hcl with ⟨#Hk, -, -, -⟩
    iapply sentMsg_dynamic_notSnapshot $$ [Hk Hs]
    iframe Hk Hs

/-- **The server's cluster's `Ready`s carry no snapshot** (2026-10-27), at the server's storage
model: a dynamic cluster's carry none, a static one vouches for no snapshot's data. -/
theorem srv_readySnap_none (γ : ServerRaftNames) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (l : SnapLoan) :
    srvClusterOk (GF := GF) γ ∗
      (letI := srvStor (GF := GF) γ.raft
       readySnap γ.raft.cl srvClusterN rd st ce es (some l)) ⊢ False := by
  letI := srvStor (GF := GF) γ.raft
  iintro ⟨#Hcl, Hs⟩
  iunfold srvClusterOk at Hcl
  cases hd : γ.raft.dyn
  · isimp only [hd, Bool.false_eq_true, ↓reduceIte] at Hcl
    icases Hcl with ⟨#Hk, -, -, -⟩
    simp only [readySnap]
    icases Hs with ⟨-, -, -, #Hc, -⟩
    icases snapshotCert_data γ.raft.cl srvClusterN γ.raft.vs (fun _ _ => False) _
      $$ [Hk Hc] with ⟨%l', -, %Hf⟩
    · iframe Hk Hc
    exact Hf.2.elim
  · isimp only [hd, ↓reduceIte] at Hcl
    icases Hcl with ⟨#Hk, -, -, -⟩
    iapply readySnap_dynamic $$ [Hk Hs]
    iframe Hk Hs
-/

end bridges


/-! ## The read contexts' mint (2026-10-16, stage R7b, B2; 2026-10-27: over the node API's read
contexts, moved here from `InvRequest.lean`) -/

section mint
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- The big-endian bytes of `id` (`binary.BigEndian.PutUint64`, `read.uint64ToBigEndianBytes`):
the read loop's request contexts (until stage R7b in `read/Inv.lean`). -/
def beBytes (id : w64) : List w8 := (u64Le id).reverse

theorem beBytes_length (id : w64) : (beBytes id).length = 8 := by
  simp [beBytes, u64Le_length]

/-- Eight bytes are the big-endian bytes of what `binary.BigEndian.Uint64` reads from them. -/
theorem beBytes_of_length (bs : List w8) (h : bs.length = 8) : bs = beBytes (leToU64 bs.reverse) := by
  unfold beBytes
  rw [leToU64_le _ (by simp [h]), List.reverse_reverse]

/-- `binary.BigEndian.Uint64` reads `id` back from its big-endian bytes. -/
theorem leToU64_beBytes (id : w64) : leToU64 (beBytes id).reverse = id := by
  unfold beBytes
  rw [List.reverse_reverse, u64Le_to_word]

theorem beBytes_inj {id id' : w64} (h : beBytes id = beBytes id') : id = id' := by
  have h' := congrArg (fun bs => leToU64 bs.reverse) h
  simp only [leToU64_beBytes] at h'
  exact h'

/-- The fresh-token map of the contexts of the ids `U` (`beBytes` of each). -/
def ctxMap (U : List w64) : GMap (List w8) Unit :=
  U.foldr (fun id m => <[beBytes id := ()]> m) ∅

theorem ctxMap_nil : ctxMap [] = ∅ := rfl

theorem ctxMap_cons (id : w64) (U : List w64) :
    ctxMap (id :: U) = <[beBytes id := ()]> (ctxMap U) := rfl

theorem ctxMap_lookup_some (U : List w64) (c : List w8) (h : (ctxMap U) !! c = some ()) :
    ∃ id, id ∈ U ∧ c = beBytes id := by
  induction U with
  | nil => simp [ctxMap_nil] at h
  | cons id U ih =>
    rw [ctxMap_cons, GMap.lookup_insert_eq_iff] at h
    by_cases hc : beBytes id = c
    · exact ⟨id, List.mem_cons.2 (Or.inl rfl), hc.symm⟩
    · simp only [hc, ↓reduceIte] at h
      obtain ⟨id', hm, hc'⟩ := ih h
      exact ⟨id', List.mem_cons.2 (Or.inr hm), hc'⟩

theorem ctxMap_lookup_none (U : List w64) (id : w64) (h : id ∉ U) :
    (ctxMap U) !! beBytes id = none := by
  induction U with
  | nil => simp [ctxMap_nil]
  | cons id' U ih =>
    rw [ctxMap_cons, GMap.lookup_insert_eq_iff]
    have hne : beBytes id' ≠ beBytes id := fun e =>
      h (by rw [← beBytes_inj e]; exact List.mem_cons.2 (Or.inl rfl))
    simp only [hne, ↓reduceIte]
    exact ih (fun hm => h (List.mem_cons.2 (Or.inr hm)))

/-- A list of issued ids of the generator (`idIssued`: the first `k`) with no duplicates has at
most `k` elements. -/
theorem idIssued_length_le (pfx s0 : w64) (k : Nat) (U : List w64) (Hnd : U.Nodup)
    (H : ∀ id ∈ U, idIssued pfx s0 k id) : U.length ≤ k := by
  have hsub : U ⊆ (List.range k).map
      (fun j => pfx ||| ((s0 + W64 ((j + 1 : Nat) : Int)) &&& W64 (2 ^ 48 - 1))) := by
    intro id hid
    obtain ⟨j, hj1, hjk, hid'⟩ := H id hid
    rw [List.mem_map]
    refine ⟨j - 1, List.mem_range.2 (by omega), ?_⟩
    rw [Nat.sub_add_cancel hj1]
    exact hid'.symm
  have := Hnd.length_le_of_subset hsub
  simpa using this

/-- The namespace of the read contexts' mint. -/
def srvRdFreshN : Namespace := nroot .@ "server_rdfresh"

instance srv_idSlot_timeless (γi : IdNames) (id : w64) : Timeless (idSlot (GF := GF) γi id) := by
  unfold idSlot; infer_instance
/-- Opening the id generator's invariant with the mint's open (`iinv`'s side condition). -/
@[simp] theorem idN_rdFreshN : (↑idN : CoPset) ⊆ ⊤ \ ↑srvRdFreshN :=
  mask_ndot_ne' nroot "idutil" "server_rdfresh" (by decide)


/-- The namespace of the cluster's read contexts' map (D21e (A), stage M4). -/
def srvRdCtxN : Namespace := nroot .@ "server_rdctx"

@[simp] theorem srvRdCtxN_rdFreshN : (↑srvRdCtxN : CoPset) ⊆ ⊤ \ ↑srvRdFreshN :=
  mask_ndot_ne' nroot "server_rdctx" "server_rdfresh" (by decide)

/-- The namespace of the committed read contexts (2026-10-27). -/
def srvRdUsedN : Namespace := nroot .@ "server_rdused"

@[simp] theorem srvRdUsedN_rdCtxN : (↑srvRdUsedN : CoPset) ⊆ ⊤ \ ↑srvRdCtxN :=
  mask_ndot_ne' nroot "server_rdused" "server_rdctx" (by decide)
@[simp] theorem srvRdCtxN_rdUsedN : (↑srvRdCtxN : CoPset) ⊆ ⊤ \ ↑srvRdUsedN :=
  mask_ndot_ne' nroot "server_rdctx" "server_rdused" (by decide)

/-- **The cluster's read contexts** (persistent; stage M4, 2026-10-19): the authority of raft's
fresh read-context tokens (`rdFresh`, `srvRdFresh`), minted for the contexts `beBytes id` of the
request ids `U` the members' read loops took from their generators, each id's element of the
cluster's issued map kept unclaimed (`idUnclaimed`, exclusive across members: so an id is minted
once, `U` has no duplicates, D21e (A)). Allocated once for the cluster (`srvRdCtxInv_alloc`):
raft's registry of reads is the cluster's. (Until M4 inside the member's mint, with the ids'
whole `idFresh`.) -/
def srvRdCtxInv (γ : ServerRaftNames) (issued : GName) : IProp GF :=
  iprop(inv srvRdCtxN iprop(∃ U : List w64, ghostMapAuth γ.raft.rdFresh 1 (ctxMap U) ∗ ⌜U.Nodup⌝ ∗
    [∗list] id ∈ U, id ↪[issued] (none : Option (List w8 × GName))) ∗
    -- (2026-10-27) the read contexts committed with raft's node API, each with its fresh token
    inv srvRdUsedN iprop(∃ (Uc : GSet (List w8)) (Lc : List (List w8)),
      ownReadCtxs γ.raft.cl Uc ∗ ([∗list] c ∈ Lc, c ↪[γ.raft.rdFresh] ()) ∗
      ⌜∀ c, c ∈ Uc ↔ c ∈ Lc⌝))

instance srvRdCtxInv_persistent (γ : ServerRaftNames) (issued : GName) :
    Persistent (srvRdCtxInv (GF := GF) γ issued) := by
  unfold srvRdCtxInv; infer_instance

/-- **The read contexts' mint** (persistent; 2026-10-16, stage R7b; split at stage M4,
2026-10-19): the member's read credits not yet spent, out of its share of raft's budget (`2 ^ 48`
of `2 ^ 64 - 2`, `rdCredInv`), one per request id `U` its read loop took from its generator `γi`
(their wait slots kept, so an id is counted once), which the generator's own budget (fewer than
`2 ^ 48` ids, `idGen`) keeps from running out (`srvRdFresh_mint`); and the cluster's read contexts
(`srvRdCtxInv`). So raft's read credit comes with the request id: the read loop's one `ReadIndex`
per id (`sendReadIndex`) is paid by the id budget the server already assumes (`idCred`), and no
premise on the number of linearizable reads is added at the gRPC layer. (Until M4 the member held
raft's whole budget and the contexts' authority.) -/
def srvRdFreshInv (γ : ServerRaftNames) (γi : IdNames) : IProp GF :=
  -- (2026-10-30, the repair) raft's read credits are gone (`ReadIndex` takes none): the minted ids
  -- (their slots) are kept, no credit with them
  iprop(inv srvRdFreshN iprop(∃ U : List w64, ⌜U.Nodup⌝ ∗ [∗list] id ∈ U, idSlot γi id) ∗
    srvRdCtxInv γ γi.issued)

instance srvRdFreshInv_persistent (γ : ServerRaftNames) (γi : IdNames) :
    Persistent (srvRdFreshInv (GF := GF) γ γi) := by
  unfold srvRdFreshInv; infer_instance

/-- **The cluster's read contexts, allocated** (stage M4): from raft's authority of the fresh
read-context tokens (`allocClientBoot`'s continuation output). -/
theorem srvRdCtxInv_alloc (γ : ServerRaftNames) (issued : GName) (E : CoPset) :
    ⊢ ghostMapAuth γ.raft.rdFresh 1 (∅ : GMap (List w8) Unit) -∗
      ownReadCtxs γ.raft.cl ∅ ={E}=∗ srvRdCtxInv (GF := GF) γ issued := by
  iintro Ha Hu
  unfold srvRdCtxInv
  isplitl [Ha]
  · iapply inv_alloc srvRdCtxN E
    inext
    iexists []
    rw [ctxMap_nil]
    iframe Ha
    isplitr
    · ipureintro; exact List.nodup_nil
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  iapply inv_alloc srvRdUsedN E
  inext
  iexists ∅, []
  iframe Hu
  isplitl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  ipureintro; intro c; simp [GMap.not_elem_of_empty]

/-- **The mint's allocation**: from the cluster's read contexts. (2026-10-30, the repair: no read
credits, raft's `ReadIndex` takes none; until then the member's share of raft's read budget,
`2 ^ 48` credits.) -/
theorem srvRdFreshInv_alloc (γ : ServerRaftNames) (γi : IdNames) (E : CoPset) :
    ⊢ srvRdCtxInv γ γi.issued ={E}=∗ srvRdFreshInv (GF := GF) γ γi := by
  iintro #Hctx
  unfold srvRdFreshInv
  iframe Hctx
  iapply inv_alloc srvRdFreshN E
  inext
  iexists []
  isplitr
  · ipureintro; exact List.nodup_nil
  iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
  itrivial

/-- The slots of a list are issued ids of the generator's map `S`. -/
theorem idSlots_issued (γi : IdNames) (S : GMap w64 Unit) (U : List w64) :
    ⊢ ghostMapAuth γi.slot 1 S -∗ ([∗list] id ∈ U, idSlot (GF := GF) γi id) -∗
      ⌜∀ id ∈ U, S !! id = some ()⌝ := by
  induction U with
  | nil =>
    iintro - -
    ipureintro
    intro id h
    simp at h
  | cons id U ih =>
    iintro Ha Hus
    icases BigSepL.bigSepL_cons.1 $$ Hus with ⟨Hu, Hus⟩
    iunfold idSlot at Hu
    ihave %Hl := ghost_map_lookup $$ Ha Hu
    ihave %Hrest := ih $$ Ha Hus
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Hl
    · exact Hrest x hx

/-- **An id mints its context's token and a read credit**: the id is fresh (its element of the
cluster's issued map is exclusive, so it is not among the cluster's minted ids), so its context is
not in the map (`beBytes` is injective); and the member's minted ids are issued ids of its
generator (their slots), fewer than `2 ^ 48` (its invariant's time receipts under the bound
`idCred`, D19b), so a credit of the member's share is left. -/
theorem srvRdFresh_mint (γ : ServerRaftNames) (γi : IdNames) (g : Loc)
    (Φ : w64 → List w8 → GName → IProp GF) (id : w64) :
    ⊢ idGen γi g Φ -∗ idCred γi 1 -∗ srvRdFreshInv (GF := GF) γ γi -∗ idFresh γi id ={⊤}=∗
      srvRdFresh γ (beBytes id) := by
  letI := srvAnyStor (GF := GF)
  iintro #Hg #Hb #Hinv Hf
  iunfold idCred at Hb
  icases Hb with %Hb
  iunfold srvRdFreshInv at Hinv
  icases Hinv with ⟨#Hinv, #Hctx⟩
  iunfold idFresh at Hf
  icases Hf with ⟨Hun, Hsl, -⟩
  iinv Hinv with ⟨%U, >%Hnd, >Hus⟩ Hclose
  -- `id ∉ U`: its slot is exclusive
  by_cases hin : id ∈ U
  · iexfalso
    icases BigSepL.bigSepL_mem_acc (Φ := fun id => idSlot (GF := GF) γi id) hin $$ Hus
      with ⟨Hs', -⟩
    iunfold idSlot at Hsl Hs'
    ihave %Hne := ghostMapElem_ne γi.slot id id (DFrac.own 1) () () $$ Hsl Hs'
    exact absurd rfl Hne
  -- the bound: the minted ids are issued ids
  iunfold idGen at Hg
  icases Hg with ⟨%s0, %Hgn, #Hpfx, %Hs0, #Hgi, -⟩
  iinv Hgi with ⟨%k, %L, %S, >Hsuf, >Hcred, >Hcnt, >HS, >%HIS⟩ Hclose2
  imod receipt_snapshot k $$ Hcred with ⟨Hcred, #Hpk⟩
  ihave %Hkb := preceipt_lt k $$ Hpk
  have Hk : k ≤ 2 ^ 48 - 1 := by omega
  ihave %Hiss := idSlots_issued γi S U $$ HS Hus
  have Hlen : U.length ≤ k := idIssued_length_le γi.pfx s0 k U Hnd
    (fun id' hid' => (HIS id').2.1 (by rw [Hiss id' hid']; rfl))
  imod Hclose2 $$ [Hsuf Hcred Hcnt HS] with -
  · inext
    iexists k, L, S
    iframe Hsuf Hcred Hcnt HS
    ipureintro
    exact HIS
  -- the token, in the cluster's read contexts
  iunfold srvRdCtxInv at Hctx
  icases Hctx with ⟨#Hctx, -⟩
  iinv Hctx with ⟨%V, >Ha, >%HVnd, >HVs⟩ Hclose3
  by_cases hinV : id ∈ V
  · iexfalso
    icases BigSepL.bigSepL_mem_acc
      (Φ := fun id => (id ↪[γi.issued] (none : Option (List w8 × GName)) : IProp GF)) hinV $$ HVs
      with ⟨Hv', -⟩
    iunfold idUnclaimed at Hun
    ihave %Hne := ghostMapElem_ne γi.issued id id (DFrac.own 1) _ _ $$ Hun Hv'
    exact absurd rfl Hne
  imod ghost_map_insert (beBytes id) () (ctxMap_lookup_none V id hinV) $$ Ha with ⟨Ha, Hfr⟩
  imod Hclose3 $$ [Ha HVs Hun] with -
  · inext
    iexists (id :: V)
    rw [ctxMap_cons]
    iframe Ha
    isplitr
    · ipureintro; exact List.nodup_cons.2 ⟨hinV, HVnd⟩
    iapply BigSepL.bigSepL_cons.2
    iunfold idUnclaimed at Hun
    iframe Hun HVs
  imod Hclose $$ [Hus Hsl] with -
  · inext
    iexists (id :: U)
    isplitr
    · ipureintro; exact List.nodup_cons.2 ⟨hin, Hnd⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Hsl Hus
  imodintro
  unfold srvRdFresh
  iexact Hfr


/-- **The context `c` was committed with raft** (persistent): a read state of it (what a
`ReadState`'s context carries). (2026-10-27: until then raft's `readReq`.) -/
def srvCtxDeposited (γ : ServerRaftNames) (c : List w8) : IProp GF :=
  iprop(∃ i : w64, readStateOk γ.raft.cl srvClusterN c i)

instance srvCtxDeposited_persistent (γ : ServerRaftNames) (c : List w8) :
    Persistent (srvCtxDeposited (GF := GF) γ c) := by
  unfold srvCtxDeposited; infer_instance

/-- **A committed context is a minted one**: the committed contexts are those whose tokens the
server's invariant keeps (`readStateOk_used`), and the mint's authority says every token is of a
`beBytes id`. (So a `ReadState`'s context is eight bytes long.) -/
theorem srvCtxDeposited_minted (γ : ServerRaftNames) (γi : IdNames) (c : List w8) :
    ⊢ srvRdFreshInv (GF := GF) γ γi -∗ srvCtxDeposited γ c ={⊤}=∗ ⌜∃ id : w64, c = beBytes id⌝ := by
  letI := srvAnyStor (GF := GF)
  iintro #Hinv #Hd
  iunfold srvCtxDeposited at Hd
  icases Hd with ⟨%i, #Hst⟩
  iunfold srvRdFreshInv at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iunfold srvRdCtxInv at Hinv
  icases Hinv with ⟨#Hctx, #Hused⟩
  iinv Hused with ⟨%Uc, %Lc, >Hu, >Hts, >%HUL⟩ Hclose
  ihave %Hc := readStateOk_used γ.raft.cl srvClusterN c i Uc $$ [Hst Hu]
  · iframe Hst Hu
  have HcL := (HUL c).1 Hc
  icases BigSepL.bigSepL_mem_acc (Φ := fun c => (c ↪[γ.raft.rdFresh] () : IProp GF)) HcL $$ Hts
    with ⟨Ht, Hts⟩
  iinv Hctx with ⟨%U, >Ha, Hrest⟩ Hclose2
  ihave %HF := ghost_map_lookup $$ Ha Ht
  imod Hclose2 $$ [Ha Hrest] with -
  · inext; iexists U; iframe Ha Hrest
  ihave Hts := Hts $$ Ht
  imod Hclose $$ [Hu Hts] with -
  · inext; iexists Uc, Lc; iframe Hu Hts; ipureintro; exact HUL
  imodintro
  ipureintro
  obtain ⟨id, -, hc⟩ := ctxMap_lookup_some U c HF
  exact ⟨id, hc⟩

/-- **Committing a minted context to the server's read** (2026-10-27): by its fresh token, the
context `c` is unused (the invariant keeps the token of every committed one), and is committed to
the read's update (`srvReadAu_api`); the token is kept. -/
theorem srvReadCtx_commit [go_etcd_io.raft.v3.Assumptions] (γ : ServerRaftNames) (issued : GName) (c : List w8)
    (Qr : List EntryModel → IProp GF) (l0 : List LogEntry) (E : CoPset) (hE : ↑srvRdUsedN ⊆ E) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvRdCtxInv γ issued -∗ srvRdFresh γ c -∗ srvReadAu γ Qr -∗
      isCommittedLogLb γ.raft.cl l0 ={E}=∗
      isReadCtx γ.raft.cl srvClusterN c (srvReadQ γ Qr) ∗
        readCtxAfter γ.raft.cl srvClusterN c l0 := by
  letI := srvAnyStor (GF := GF)
  iintro #Hinv #Hci Ht #Hra #Hl0
  ihave #Hau := srvReadAu_api γ Qr $$ Hinv Hra
  iunfold srvRdCtxInv at Hci
  icases Hci with ⟨-, #Hused⟩
  iinv Hused with ⟨%Uc, %Lc, >Hu, >Hts, >%HUL⟩ Hclose
  by_cases hc : c ∈ Lc
  · iexfalso
    icases BigSepL.bigSepL_mem_acc (Φ := fun c => (c ↪[γ.raft.rdFresh] () : IProp GF)) hc $$ Hts
      with ⟨Ht', -⟩
    iunfold srvRdFresh at Ht
    ihave %Hne := ghostMapElem_ne γ.raft.rdFresh c c (DFrac.own 1) () () $$ Ht Ht'
    exact absurd rfl Hne
  have hcU : c ∉ Uc := fun h => hc ((HUL c).1 h)
  imod readCtx_commit_after γ.raft.cl srvClusterN Uc c (srvReadQ γ Qr) l0 hcU $$ [Hu Hau]
    with ⟨Hu, #Hrc, #Haft⟩
  · iframe Hu Hl0 Hau
  imod Hclose $$ [Hu Hts Ht] with -
  · inext
    iexists insert c Uc, c :: Lc
    iframe Hu
    isplitl
    · iapply BigSepL.bigSepL_cons.2
      iunfold srvRdFresh at Ht
      iframe Ht Hts
    ipureintro
    intro c'
    rw [GMap.elem_of_insert_set, List.mem_cons, HUL c']
  imodintro
  iframe Hrc Haft

end mint

/-! ## Allocation -/

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server's log invariant, allocated** (2026-10-27) over the node API's cluster `cl`, from
the requested entries committed so far (the bootstrap log's `Lf0`: consecutive from index `1`, no
filler, no normal entry), the server's start at index `0`: the server's names (the cluster's kind
as given), the log invariant, the KV invariant's half of `Lf0`, and the authorities of the
proposals' and the read contexts' fresh tokens (for the mints). -/
theorem srvLogInv_alloc (cl : Cluster) (vs : List w64)
    (rule : ConfRule) (boot : List EntryM) (reg : GName) (snapLoc : w64 → Option GName)
    (Lf0 : List EntryModel) (E : CoPset)
    (hidx : srvIdxOkW (W64 0) Lf0) (hnf : ∀ m ∈ Lf0, ¬ m.toLE.isFiller ∧ ¬ m.toLE.isEmptyV2)
    (hnn : ∀ m ∈ Lf0, m.typ ≠ W32 0)
    -- (2026-10-30, the repair, T1c) its conf entries changes the server takes (`srvLogCore`'s)
    (hcc : ∀ m ∈ Lf0, m.typ = W32 1 → ccBootOk (GMap.listToSet vs) m.data) :
    ⊢ ownCommittedOps (GF := GF) cl (Lf0.map EntryModel.toLE) ={E}=∗
      ∃ γr : SrvRaft, ⌜γr.cl = cl ∧ γr.vs = vs ∧ γr.rule = rule ∧ γr.boot = boot ∧ γr.reg = reg ∧
        γr.snapLoc = snapLoc⌝ ∗
        srvLogInv (⟨γr, [], W64 0⟩ : ServerRaftNames) ∗ srvRLog ⟨γr, [], W64 0⟩ Lf0 ∗
        srvRLogLb (⟨γr, [], W64 0⟩ : ServerRaftNames) [] ∗
        ghostMapAuth γr.fresh 1 (∅ : GMap (List w8) Unit) ∗
        ghostMapAuth γr.rdFresh 1 (∅ : GMap (List w8) Unit) := by
  sorry
/- REPAIR-OLD
  letI := srvAnyStor (GF := GF)
  iintro Hown
  imod mono_list_own_alloc (GF := GF) Lf0 with ⟨%γlog, Hlog, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := Unit) with ⟨%γfresh, Hfresh⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName) with ⟨%γprops, HP⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := List EntryModel) with ⟨%γfired, HF⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := Unit) with ⟨%γrd, Hrd⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (GName × Nat)) with ⟨%γpend, HR, -⟩
  let γr : SrvRaft := ⟨cl, vs, rule, boot, reg, snapLoc, γlog, γfresh, γprops, γfired, γrd, γpend⟩
  icases ((monoListAuthOwn_fractional (GF := GF) γlog Lf0).fractional
      (1 : Qp).half (1 : Qp).half).1 $$ [Hlog] with ⟨Hlog, HL⟩
  · rw [Qp.half_add_half]; iexact Hlog
  have Hops : opsOf (srvLE (⟨γr, [], W64 0⟩ : ServerRaftNames) Lf0) =
      Lf0.map EntryModel.toLE := by
    rw [opsOf_nofill]
    · rfl
    · intro e he
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (by simpa [srvLE] using he)
      exact hnf m hm
  imod inv_alloc srvLogN E iprop(∃ (Lf : List EntryModel) (P : GMap (List w8) (GName × GName))
      (F : GMap (List w8) (List EntryModel)) (R : List (GName × Nat)),
    srvLogCore (⟨γr, [], W64 0⟩ : ServerRaftNames) Lf P F R ∗
      srvLogRegs (⟨γr, [], W64 0⟩ : ServerRaftNames) Lf F R) $$ [Hown Hlog HP HF HR] with #Hli
  · inext
    iexists Lf0, ∅, ∅, []
    iunfold srvLogCore
    iunfold srvLogRegs
    rw [Hops]
    iframe Hown Hlog HP HF HR
    isplitr
    · isplitr
      · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; itrivial
      ipureintro
      refine ⟨hidx, hnf, ?_, by simp⟩
      intro j m hm ht
      exact absurd ht (hnn m (List.mem_of_getElem? hm))
    isplitr
    · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; itrivial
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  ihave #Hnil := isCommittedLogLb_nil (GF := GF) cl
  imodintro
  iexists γr
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  iunfold srvLogInv
  iframe Hli Hfresh Hrd
  iunfold srvRLog
  iframe HL
  iunfold srvRLogLb
  have Hn : srvLE (⟨γr, [], W64 0⟩ : ServerRaftNames) [] = [] := rfl
  rw [Hn]
  iframe Hnil
  ipureintro; intro n m hm; simp at hm
-/

end alloc

end EtcdGrove
end Perennial
