/-
**Raft's committed log, at the server, over raft's node API** (2026-10-27, branch `server-port`;
`notes/decisions.md`, "etcd's server on raft's node API"). Until then (stage R7b, 2026-10-16) the
server's contract predicates were definitions over raft's protocol (`rLog`, `isCommitted`,
`propIs`, `readReq`, ...); now they are over raft's node API (`NodeApiDraft.lean`, namespace
`Draft`) and the server's own ghost state, and name nothing of raft's internals.

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
public import Proof.go_etcd_io.raft.v3.NodeApiDraft
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
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
theorem srvLogN_clusterN : (↑srvLogN : CoPset) ⊆ ⊤ \ ↑srvClusterN :=
  mask_ndot_ne' srvRaftN "log" "cluster" (by decide)

/-- **The cluster, as the server sees it** (2026-10-27): the node API's cluster, the voters it
started with (`vs`), whether it is dynamic (raft's dynamic mode, its conf changes applied with the
decoder `dec`) or static, and the server's ghost names: the requested entries' log (`log`, a mono
list), the proposals' fresh tokens (`fresh`), their registry (`props`: data ↦ result predicate and
one-shot token), the fired proposals (`fired`: data ↦ the log before its entry), the read
contexts' fresh tokens (`rdFresh`) and the reads to fire again (`pend`). -/
structure SrvRaft [GooseExts] where
  cl : Draft.Cluster
  vs : List w64
  dyn : Bool
  dec : Draft.ConfChangeDecoder
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

/-- An entry as raft's node API sees it: its index dropped. -/
def EntryModel.toLE (m : EntryModel) : Draft.LogEntry := ⟨m.term, m.typ, m.data⟩

/-- The committed log holding the server's `L` after its start, as raft's node API sees it. -/
def srvLE (γ : ServerRaftNames) (L : List EntryModel) : List Draft.LogEntry :=
  (γ.pre ++ L).map EntryModel.toLE

theorem srvLE_append (γ : ServerRaftNames) (A B : List EntryModel) :
    srvLE γ (A ++ B) = srvLE γ A ++ B.map EntryModel.toLE := by
  simp [srvLE]

theorem srvLE_length (γ : ServerRaftNames) (L : List EntryModel) :
    (srvLE γ L).length = γ.pre.length + L.length := by
  simp [srvLE]

theorem opsOf_append (a b : List Draft.LogEntry) :
    Draft.opsOf (a ++ b) = Draft.opsOf a ++ Draft.opsOf b := by
  simp only [Draft.opsOf, List.filter_append]

theorem opsOf_nofill (a : List Draft.LogEntry) (h : ∀ e ∈ a, ¬ e.isFiller) :
    Draft.opsOf a = a := by
  unfold Draft.opsOf
  rw [List.filter_eq_self]
  intro e he
  simp [h e he]

theorem opsOf_length_le (a : List Draft.LogEntry) : (Draft.opsOf a).length ≤ a.length := by
  unfold Draft.opsOf; exact List.length_filter_le _ _

theorem opsOf_prefix {a b : List Draft.LogEntry} (h : a <+: b) :
    Draft.opsOf a <+: Draft.opsOf b := by
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
    simp only [EntryModel.toLE, Draft.LogEntry.mk.injEq] at hab
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
    Draft.opsOf (A.map EntryModel.toLE) = Draft.opsOf (B.map EntryModel.toLE)

theorem srvEqv_refl (γ : ServerRaftNames) (A : List EntryModel) (h : srvIdxOkW γ.ai0 A) :
    srvEqv γ A A := ⟨h, h, rfl⟩

theorem toLE_isFiller (m : EntryModel) :
    m.toLE.isFiller ↔ (m.data = [] ∧ (m.typ = W32 0 ∨ m.typ = W32 2)) := Iff.rfl

end pure

/-! ## The server's two views of the committed log -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

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
  iprop(Draft.isCommittedLogLb γ.raft.cl (srvLE γ L) ∗ ⌜srvIdxOkW γ.ai0 L⌝)

instance srvRLogLb_persistent (γ : ServerRaftNames) (L : List EntryModel) :
    Persistent (srvRLogLb (GF := GF) γ L) := by
  unfold srvRLogLb; infer_instance

instance srvRLogLb_timeless (γ : ServerRaftNames) (L : List EntryModel) :
    Timeless (srvRLogLb (GF := GF) γ L) := by
  unfold srvRLogLb; infer_instance

theorem srvRLogLb_idx (γ : ServerRaftNames) (L : List EntryModel) :
    srvRLogLb (GF := GF) γ L ⊢ ⌜srvIdxOkW γ.ai0 L⌝ := by
  unfold srvRLogLb; iintro ⟨-, %H⟩; ipureintro; exact H

variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- Any storage model (the node API's laws take one, unused). -/
abbrev srvAnyStor : StorageModel GF :=
  letI : MemStorReg GF := ⟨default⟩
  inferInstance

/-- Two prefixes of the committed log are comparable. -/
theorem srvRLogLb_prefix (γ : ServerRaftNames) (A B : List EntryModel) :
    srvRLogLb (GF := GF) γ A ∗ srvRLogLb γ B ⊢ ⌜A <+: B ∨ B <+: A⌝ := by
  letI := srvAnyStor (GF := GF)
  unfold srvRLogLb
  iintro ⟨⟨#HA, %hA⟩, ⟨#HB, %hB⟩⟩
  icases Draft.isCommittedLogLb_agree γ.raft.cl (srvLE γ A) (srvLE γ B) $$ [HA HB] with %H
  · iframe HA HB
  ipureintro
  rcases H with h | h
  · exact .inl (srvLE_prefix γ A B hA hB h)
  · exact .inr (srvLE_prefix γ B A hB hA h)

/-- A prefix of a committed prefix. -/
theorem srvRLogLb_mono (γ : ServerRaftNames) (A B : List EntryModel) (h : A <+: B) :
    srvRLogLb (GF := GF) γ B ⊢ srvRLogLb γ A := by
  letI := srvAnyStor (GF := GF)
  unfold srvRLogLb
  iintro ⟨#HB, %hB⟩
  isplitl
  · iapply Draft.isCommittedLogLb_mono γ.raft.cl _ _ (srvLE_prefix_of γ A B h) $$ HB
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

/-- **A conf change `applyConfChange` takes, in the cluster's mode** (D43 M5d/M5e): `ccApplyOk`,
and in a dynamic cluster also a `RemoveNode` of a member of the configuration. (2026-10-27: of the
server's `SrvRaft`, `cfg` and `dyn`; until then of raft's names, `reCfg` and `reDyn`.) -/
def ccApplyOkR (γ : SrvRaft) (m : ConfChangeM) : Prop :=
  ccApplyOk γ.cfg m ∨ (γ.dyn = true ∧ m.type = W32 1 ∧ m.nodeId ∈ γ.cfg)

/-- `ccApplyOkR` at the server's raft. -/
abbrev ccApplyOkM (γs : ServerRaftNames) (m : ConfChangeM) : Prop := ccApplyOkR γs.raft m

/-- The bytes `d` of a conf-change entry decode to a change `applyConfChange` takes. -/
def ccBootOk (cfg : GSet w64) (d : List w8) : Prop :=
  ∀ m, ccDecodeV1 d = some m → ccApplyOk cfg m

/-- **The bytes `d` of a conf-change entry decode to a change `applyConfChange` takes, in the
cluster's mode** (D43 M5d). -/
def ccPolOk (γ : SrvRaft) (d : List w8) : Prop :=
  ∀ m, ccDecodeV1 d = some m → ccApplyOkR γ m

theorem ccPolOk_of_boot (γ : SrvRaft) (d : List w8) (h : ccBootOk γ.cfg d) : ccPolOk γ d :=
  fun m hm => .inl (h m hm)

/-- In a static cluster `ccPolOk` is `ccBootOk`. -/
theorem ccPolOk_static (γ : SrvRaft) (d : List w8) (hs : γ.dyn = false) (h : ccPolOk γ d) :
    ccBootOk γ.cfg d := by
  intro m hm
  rcases h m hm with h | ⟨h, -⟩
  · exact h
  · rw [hs] at h; cases h

/-- **A v1 change raft's node applies without changing its configuration `cfg`** (raft's static
mode admits only such changes, `CCShrink`): an `AddNode` of a voter, or of the node `0`. -/
def ccRaftOk (cfg : GSet w64) (m : ConfChangeM) : Prop :=
  m.type = W32 0 ∧ ∃ k, k ∈ cfg ∧ (m.nodeId = k ∨ m.nodeId = W64 0)

end policy

/-! ## The server's updates and their registries -/

section regs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

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
any log with the same requested entries (`srvEqv`), a step later. The server's results are of the
KV model of the log, which the requested entries determine (`kvModel_eqv`). -/
def srvQInv (γ : ServerRaftNames) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(□ ∀ (A B : List EntryModel), ⌜srvEqv γ A B⌝ -∗ □ Q A -∗ ▷ □ Q B)

instance srvQInv_persistent (γ : ServerRaftNames) (Q : List EntryModel → IProp GF) :
    Persistent (srvQInv (GF := GF) γ Q) := by
  unfold srvQInv; infer_instance

/-- A predicate of the log's requested entries is one the logs agree on. -/
theorem srvQInv_of_eq (γ : ServerRaftNames) (Q : List EntryModel → IProp GF)
    (h : ∀ A B, srvEqv γ A B → Q A = Q B) : ⊢ srvQInv (GF := GF) γ Q := by
  unfold srvQInv
  iintro !> %A %B %Hab #HA
  rw [← h A B Hab]
  inext; iexact HA

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

/-- **A read credit** for one `ReadIndex` (the node API's). -/
def srvRdCred (γ : ServerRaftNames) : IProp GF := Draft.readCredit γ.raft.cl

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
  iprop(Draft.ownCommittedOps γ.raft.cl (Draft.opsOf (srvLE γ Lf)) ∗
    monoListAuthOwn γ.raft.log (1 : Qp).half Lf ∗
    ghostMapAuth γ.raft.props 1 P ∗ ghostMapAuth γ.raft.fired 1 F ∗
    monoListAuthOwn γ.raft.pend 1 R ∗
    ([∗map] d ↦ _x ∈ P, d ↪[γ.raft.fresh] ()) ∗
    ⌜srvIdxOkW γ.ai0 Lf ∧ (∀ m ∈ Lf, ¬ m.toLE.isFiller) ∧
      (∀ (j : Nat) (m : EntryModel), Lf[j]? = some m → m.typ = W32 0 →
        F.lookup m.data = some (Lf.take j)) ∧
      (∀ r ∈ R, r.2 ≤ Lf.length)⌝)

instance srvLogCore_timeless (γ : ServerRaftNames) (Lf : List EntryModel)
    (P : GMap (List w8) (GName × GName)) (F : GMap (List w8) (List EntryModel))
    (R : List (GName × Nat)) : Timeless (srvLogCore (GF := GF) γ Lf P F R) := by
  unfold srvLogCore; infer_instance

/-- A registered read, at the server's log `Lf`: its result predicate (saved), its update, and its
result at every log from its registration to `Lf`. -/
def srvPendRead (γ : ServerRaftNames) (Lf : List EntryModel) (r : GName × Nat) : IProp GF :=
  iprop(∃ Qr : List EntryModel → IProp GF, savedPredOwn r.1 DFrac.discard Qr ∗ srvReadAu γ Qr ∗
    □ (∀ j : Nat, ⌜r.2 ≤ j ∧ j ≤ Lf.length⌝ -∗ □ Qr (Lf.take j)))

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

/-- **The cluster's kind** (persistent): static or dynamic (`γ.raft.dyn`) at the voters it started
with, no snapshot (a static cluster vouches for no snapshot's data: `snapOk` false), leader
transfer off. -/
def srvClusterOk (γ : ServerRaftNames) : IProp GF :=
  iprop((if γ.raft.dyn then
      Draft.isDynamicCluster γ.raft.cl srvClusterN (Draft.Membership.simple γ.raft.cfg) γ.raft.dec
    else Draft.isStaticCluster γ.raft.cl srvClusterN γ.raft.vs (fun _ _ => False)) ∗
    Draft.leaderTransferOff γ.raft.cl srvClusterN)

instance srvClusterOk_persistent (γ : ServerRaftNames) : Persistent (srvClusterOk (GF := GF) γ) := by
  unfold srvClusterOk; split <;> infer_instance

/-- **Raft's committed log, at the server** (persistent; the contract's ghost interface): the
server's log invariant, the cluster's kind, the start log committed and the start index its
length. (2026-10-27: until then raft's commit invariant and the conf-change policy.) -/
def srvRaftLogInv (γ : ServerRaftNames) : IProp GF :=
  iprop(srvLogInv γ ∗ srvClusterOk γ ∗ srvRLogLb γ [] ∗ ⌜uint.Z γ.ai0 = γ.pre.length⌝)

instance srvRaftLogInv_persistent (γ : ServerRaftNames) :
    Persistent (srvRaftLogInv (GF := GF) γ) := by
  unfold srvRaftLogInv; infer_instance

theorem srvRaftLogInv_facts (γ : ServerRaftNames) :
    srvRaftLogInv (GF := GF) γ ⊢ ⌜uint.Z γ.ai0 = γ.pre.length⌝ := by
  unfold srvRaftLogInv
  iintro ⟨-, -, -, %H⟩
  ipureintro; exact H

end regs

/-! ## Pure facts of the two logs -/

section purefacts
variable [GooseExts]

theorem srvLE_ops_nofill (γ : ServerRaftNames) (L : List EntryModel)
    (h : ∀ m ∈ L, ¬ m.toLE.isFiller) :
    Draft.opsOf (srvLE γ L) = Draft.opsOf (srvLE γ []) ++ L.map EntryModel.toLE := by
  have : srvLE γ L = srvLE γ [] ++ L.map EntryModel.toLE := by
    rw [← srvLE_append]; rfl
  rw [this, opsOf_append, opsOf_nofill (L.map EntryModel.toLE)]
  intro e he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
  exact h m hm

theorem srvLE_ops (γ : ServerRaftNames) (A : List EntryModel) :
    Draft.opsOf (srvLE γ A) = Draft.opsOf (srvLE γ []) ++ Draft.opsOf (A.map EntryModel.toLE) := by
  have : srvLE γ A = srvLE γ [] ++ A.map EntryModel.toLE := by
    rw [← srvLE_append]; rfl
  rw [this, opsOf_append]

/-- A committed log's requested entries, as a prefix of the server's log's. -/
theorem srv_ops_prefix (γ : ServerRaftNames) (A Lf : List EntryModel)
    (hnf : ∀ m ∈ Lf, ¬ m.toLE.isFiller)
    (h : Draft.opsOf (srvLE γ A) <+: Draft.opsOf (srvLE γ Lf)) :
    Draft.opsOf (A.map EntryModel.toLE) <+: Lf.map EntryModel.toLE := by
  rw [srvLE_ops, srvLE_ops_nofill γ Lf hnf] at h
  exact (List.prefix_append_right_inj _).1 h

/-- The server's log after one more requested entry has a next index that fits: the committed
log `l` holding its requested entries extends the start log. -/
theorem srv_next_bound (γ : ServerRaftNames) (Lf : List EntryModel) (l : List Draft.LogEntry)
    (x : Draft.LogEntry) (hnf : ∀ m ∈ Lf, ¬ m.toLE.isFiller)
    (hops : Draft.opsOf l = Draft.opsOf (srvLE γ Lf) ++ [x])
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

/-! ## The server's updates as the node API's -/

section bridges
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

theorem srv_mask_inner : (⊤ \ ↑srvRaftN : CoPset) ⊆ (⊤ \ ↑srvClusterN) \ ↑srvLogN :=
  mask_diff_ndot2 srvRaftN "cluster" "log"

/-- **The server's half bounds every prefix of the committed log**, by their requested entries:
a committed log's requested entries are those of a prefix of the server's log (2026-10-27: until
then the committed log itself was a prefix of the server's, which held raft's fillers too). -/
theorem srvRLog_lb (γ : ServerRaftNames) (E : CoPset) (hE : ↑srvLogN ⊆ E)
    (L A : List EntryModel) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvRLog γ L -∗ srvRLogLb γ A ={E}=∗
      srvRLog γ L ∗ ⌜srvIdxOkW γ.ai0 L ∧ (∀ m ∈ L, ¬ m.toLE.isFiller) ∧
        Draft.opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE⌝ := by
  letI := srvAnyStor (GF := GF)
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
  ihave %Hp := Draft.ownCommittedOps_lb_prefix γ.raft.cl _ _ $$ [Hown HA]
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

end bridges

end EtcdGrove
end Perennial
