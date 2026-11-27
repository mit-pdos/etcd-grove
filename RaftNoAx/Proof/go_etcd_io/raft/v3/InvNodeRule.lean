-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/InvNodeRule.lean` (etc/copy-part.py; rerun it, do not edit).
/-
# Raft's node API: a cluster with snapshots and reconfiguration, its conf entries decided by the client

(2026-10-28, stage U4a; the conf-change decision switch, `notes/spec-first-study/raft-decisions-spec.md`,
§1, §3, §4.) A cluster in raft's dynamic mode **and** outside its no-snapshot mode, whose committed conf
entries the client decides: a client-owned authority over the decisions (`ownConfDecisions`, from the
allocation, empty), one decision per position (`confDecide`), every node's configuration the fold of the
decisions over the committed log. Raft's API mentions no rule: a client deciding by a rule uses the
library `ConfPolicy.lean` over the authority. (Until the switch, stage U4a's interim: a rule fixed at
allocation, `cluster_alloc_rule`, with raft's persistent `confPolicy`.)

Every predicate is **sealed** over its definition in `InvApiDec.lean` (laws and allocation proved
there, `InvApiDecAlloc.lean`); nothing here is `sorry`. The node's other predicates are `InvNode`'s
(`isNode`, `nodeDriver`, `nodeConfig`, `deliveredLogLb`, `snapshotCert`, ...), the specs over this cluster
`RestartNode.spec`, `node.ApplyConfChange.spec`, `node.Advance.spec`.

- **The cluster** (`isCluster`, persistent): its nodes' configuration the membership after their
  applied conf entries, from the voters' membership, each decided once for all nodes; snapshots taken
  and installed.
- **Decisions**: `ownConfDecisions γ D` (exclusive, timeless), the decisions recorded so far by
  position; `confDecided γ k d` (persistent), that the conf entry at position `k` was decided `d`
  (`_lookup`, `_witness`, `confDecided_agree`); `confDecide` records a decision on an undecided
  committed conf entry, at the configuration before it, with a result.
- **The configuration** (`confAt γ k m`, persistent): the membership after the first `k` committed
  entries is `m`. A client tracks `confAt` beside its node's view (`nodeConfig`): past entries that are
  no conf change (`confAt_noConf`), past a decided one (`confAt_decided`). `skippedIn γ l a b`: every
  conf entry of `l` in `[a, b)` decided `.skip`, what `ApplyConfChange`/`Advance` take for the entries
  their view passes.
- **Snapshots** (TaDa style): the client's registry of the snapshots it made (`ownSnapsMade`, from the
  allocation, empty), `snapshotCert_make` (a committed prefix at its configuration), `snapshotCert_made`
  (a certificate's prefix, configuration and record), `snapMade_elem`.
- **Joining** (2026-10-29, stage U4): the ids started or reserved (`joinAuth γ U`, from the allocation
  at the founders), and a newcomer's token (`nodeJoin γ N id`, `joinAuth_join`), for its `RestartNode`
  at the initial membership with an empty log, as a founder's.
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.ConfRule
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApiDec
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApiDecAlloc
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApiJoin
import RaftNoAx.Proof.go_etcd_io.raft.v3.InvApiBoot
import all RaftNoAx.Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-! ## The cluster -/

/-- **A cluster with snapshots and reconfiguration** (persistent): raft's dynamic mode of the client's
decisions, outside the no-snapshot mode, with the registry of the snapshots made. -/
@[no_expose] def isCluster (γ : Cluster) (N : Namespace) : IProp GF := ApiImpl.isClusterU γ N

instance isCluster_persistent (γ : Cluster) (N : Namespace) :
    Persistent (isCluster (GF := GF) γ N) := by
  unfold isCluster; exact ApiImpl.isClusterU_persistent γ N

/-- **The membership after the first `k` committed entries is `m`** (persistent): every conf entry
among them decided. -/
@[no_expose] def confAt (γ : Cluster) (k : Nat) (m : Membership) : IProp GF :=
  ApiImpl.confAtU γ k m

instance confAt_persistent (γ : Cluster) (k : Nat) (m : Membership) :
    Persistent (confAt (GF := GF) γ k m) := by
  unfold confAt; exact ApiImpl.confAtU_persistent γ k m

/-- (2026-10-28, the decision switch) No later credit to open an invariant holding it
(`ConfPolicy.lean`). -/
instance confAt_timeless (γ : Cluster) (k : Nat) (m : Membership) :
    Timeless (confAt (GF := GF) γ k m) := by
  unfold confAt; exact ApiImpl.confAtU_timeless γ k m

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- (open) **A node's configuration view** (exclusive, one per node): what `node.ApplyConfChange`
moves and `node.Advance` checks. Separate from the `Ready` loop's token (`nodeDriver`): an application
may apply the conf changes on another goroutine than its `Ready` loop (etcd's server applies them on
its apply goroutine, and hands the view back before `Advance`). (2026-10-30, stage R3: moved here
from `InvNode.lean`, with the configuration it names, `confAt`, `nodeConfig_confAt`.) -/
@[no_expose] def nodeConfig (n : NodeH) (γ : Cluster) (N : Namespace) (v : ConfigView) : IProp GF :=
  iprop(ApiImpl.nodeConfig n γ N v ∗ ApiImpl.confAtU γ v.applied v.membership)

/-- (2026-10-30, stage R3) **A node's view is the cluster's configuration** at its applied index. -/
theorem nodeConfig_confAt (n : NodeH) (γ : Cluster) (N : Namespace) (v : ConfigView) :
    nodeConfig (GF := GF) n γ N v ⊢ nodeConfig n γ N v ∗ confAt γ v.applied v.membership := by
  haveI := ApiImpl.confAtU_persistent (GF := GF) γ v.applied v.membership
  unfold nodeConfig confAt
  iintro ⟨H, #Hc⟩
  iframe H Hc

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
/-- **The conf entry at position `k` (index `k + 1`) of the committed log was decided `d`**
(persistent). -/
@[no_expose] def confDecided (γ : Cluster) (k : Nat) (d : ConfDecision) : IProp GF :=
  ApiImpl.confDecidedU γ k d

instance confDecided_persistent (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Persistent (confDecided (GF := GF) γ k d) := by
  unfold confDecided; exact ApiImpl.confDecidedU_persistent γ k d

instance confDecided_timeless (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Timeless (confDecided (GF := GF) γ k d) := by
  unfold confDecided; exact ApiImpl.confDecidedU_timeless γ k d

/-- **The decisions recorded so far, by log position** (exclusive; the client's, typically in an
invariant). -/
@[no_expose] def ownConfDecisions (γ : Cluster) (D : GMap Nat ConfDecision) : IProp GF :=
  ApiImpl.ownConfDecisionsU γ D

instance ownConfDecisions_timeless (γ : Cluster) (D : GMap Nat ConfDecision) :
    Timeless (ownConfDecisions (GF := GF) γ D) := by
  unfold ownConfDecisions; exact ApiImpl.ownConfDecisionsU_timeless γ D

/-- **The snapshots the client made** (exclusive): the records `S`, in the cluster's registry. -/
@[no_expose] def ownSnapsMade (γ : Cluster) (S : List SnapRec) : IProp GF := ApiImpl.ownSnapsMadeU γ S

/-- No later credit to open an invariant holding it. -/
instance ownSnapsMade_timeless (γ : Cluster) (S : List SnapRec) :
    Timeless (ownSnapsMade (GF := GF) γ S) := by
  unfold ownSnapsMade; exact ApiImpl.ownSnapsMadeU_timeless γ S

/-- **The snapshot `s` was made** (persistent). -/
@[no_expose] def snapMade (γ : Cluster) (s : SnapRec) : IProp GF := ApiImpl.snapMadeU γ s

instance snapMade_persistent (γ : Cluster) (s : SnapRec) :
    Persistent (snapMade (GF := GF) γ s) := by
  unfold snapMade; exact ApiImpl.snapMadeU_persistent γ s

/-- (R2d, Q14, 2026-11-06) No later credit to open an invariant holding it (a WAL record's
certificate in the server's durability invariant, `walSnapCert`). -/
instance snapMade_timeless (γ : Cluster) (s : SnapRec) :
    Timeless (snapMade (GF := GF) γ s) := by
  unfold snapMade; exact ApiImpl.snapMadeU_timeless γ s

-- (2026-11-01, durability stage I-7) `nodeFounder` and `nodeJoin` deleted: allocation and
-- `joinAuth_join` give the id's durable state at `RaftState.init` and its vacant slot
-- (`raftState`, `nodeVacant`, `InvNode.lean`) in their place.

/-- **The ids started or reserved** (exclusive): every node id in `U` has had its durable state and
slot taken (a founder's or a joiner's); the others' are here. -/
@[no_expose] def joinAuth (γ : Cluster) (U : GSet w64) : IProp GF := ApiImpl.joinAuthU γ U

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- **A founder of a cluster with a bootstrap log** (persistent; 2026-10-30, stage R5; until
2026-11-01, durability stage I-7, an exclusive start token, whose ghost state moved to `raftState`
and `nodeVacant`): node `id`, one of the voters `vs`, of a cluster whose committed log starts with
the voters' `AddNode`s with the contexts `ctxs` (`BootLog`), for its `StartNode` on an empty storage
(`StartNode.spec`). Persistent, so a first start that crashed may be retried. -/
@[no_expose] def nodeBoot (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) : IProp GF :=
  ApiImpl.nodeBootU γ N vs ctxs id

instance nodeBoot_persistent (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) : Persistent (nodeBoot (GF := GF) γ N vs ctxs id) := by
  unfold nodeBoot; exact ApiImpl.nodeBootU_persistent γ N vs ctxs id

/-- (2026-11-05, the lease-expiry plan's E2 revision 5) **The node `n` of the cluster `γ` was made
by `StartNode`** (persistent): `n` is the node of `id` in `γ` (`isNode`), `γ` was bootstrapped with
the voters `vs` (`nodeBoot`), and `StartNode` made `n` (its start tag `true`, `nodeStartTag`): `StartNode.spec`'s
precondition is an empty storage, so its log began as the bootstrap log. `RestartNode` tags its node
`false`, so gives no such fact, even on an empty storage (etcd's join without a WAL). -/
@[no_expose] def nodeStartedFresh (n : NodeH) (γ : Cluster) (N : Namespace) (vs : List w64)
    (ctxs : List (List w8)) (id : w64) : IProp GF :=
  iprop(isNode n γ N id ∗ nodeBoot γ N vs ctxs id ∗ ⌜id ∈ vs⌝ ∗
    ApiImpl.nodeStartTag n γ true)

instance nodeStartedFresh_persistent (n : NodeH) (γ : Cluster) (N : Namespace) (vs : List w64)
    (ctxs : List (List w8)) (id : w64) :
    Persistent (nodeStartedFresh (GF := GF) n γ N vs ctxs id) := by
  unfold nodeStartedFresh
  haveI := ApiImpl.nodeStartTag_persistent (GF := GF) n γ true
  haveI := nodeBoot_persistent (GF := GF) γ N vs ctxs id
  haveI := isNode_persistent (GF := GF) n γ N id
  infer_instance

open Classical in
/-- **A new cluster of the voters `vs`** (§3 of the decision switch; until U9, 2026-10-29,
`cluster_alloc_dec`, the name `cluster_alloc` being the static cluster's; until the switch
`cluster_alloc_rule`, of a rule), in the caller's namespace `N`, its committed log starting with the
bootstrap log `boot` (2026-10-30, stage R5): either none (`boot = []`), or one `AddNode` per voter with
the contexts `ctxs`, as raft's `Bootstrap` writes them (`BootLog`), whose bytes are `Marshal`'s
(`bootMarshal`). The committed operations the bootstrap log's, the read contexts with none used, the
cluster (with snapshots), the authority over its decisions, none recorded (a boot conf entry is decided
as any other, `confDecide`: an `AddNode` of a voter keeps the voters' membership,
`Membership.applyChange_addVoter`), the membership of no entry the voters', the registry of the
snapshots made (empty), the bootstrap log's length (`Cluster.bootLen`, for `readyFits_intro`), and
(2026-11-01, J8a) the nodes' snapshot directories the caller's `sl` (`Cluster.snapLoc`,
`nodeSnapLocal`). Per voter (2026-11-01, durability stage I-7; until then a founder's or a start token): its durable
state at `RaftState.init` and its vacant slot (`raftState`, `nodeVacant`), for `RestartNode` without
a bootstrap log, or with one (and the bootstrap log committed) for `StartNode` with its persistent
`nodeBoot`. Without a bootstrap log, the join authority at the voters (2026-10-29, stage U4); with one
none (raft keeps the bootstrap log in every node's log, which a newcomer's empty storage does not
hold). The term budget, backed by time receipts (`receiptBound`), is the cluster's; so (U9) are the
read requests' credits, and leader transfer is on in every cluster. (auth-lease S4, 2026-11-16, L-r6)
And the cluster's no-snapshot mode (`clusterNoSnap`) the caller's choice `ns`, only with a bootstrap
log. -/
theorem cluster_alloc_ns (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (dup : Bool) (sl : w64 → Option GName)
    -- (raft-entsize §2, 2026-11-09) the bound on proposed data (`Cluster.maxData`): at most `2^31`,
    -- and met by the bootstrap log's entries (both vacuous at `none`)
    (md : Option Nat) (E : CoPset)
    -- (auth-lease S4, 2026-11-16, L-r6) the no-snapshot mode, only with a bootstrap log
    (ns : Bool) (Hns : ns = true → boot ≠ []) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    (boot ≠ [] → BootLog vs ctxs boot) →
    (∀ b, md = some b → b ≤ 2 ^ 31) →
    (∀ b, md = some b → ∀ e ∈ boot, e.data.length ≤ b) →
    ⊢ (if boot = [] then emp else bootMarshal (GF := GF) vs ctxs (LogEntry.toEntries boot 0)) ={E}=∗
      ∃ γ, ⌜γ.dup = dup ∧ γ.snapLoc = sl ∧ γ.bootLen = boot.length ∧ γ.maxData = md ∧
          (clusterNoSnap γ ↔ ns = true)⌝ ∗
        -- (2026-11-09, Q8 stage 0, `notes/trace-validation-q6.md` item 9) an untraced cluster
        ⌜Cluster.trace γ = none⌝ ∗ ownCommittedOps (GF := GF) γ boot ∗
        ownReadCtxs γ ∅ ∗ isCluster γ N ∗ ownConfDecisions γ ∅ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMade γ [] ∗
        ([∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id) ∗
        if boot = [] then joinAuth γ (GMap.listToSet vs)
        else isCommittedLogLb γ boot ∗ [∗list] id ∈ vs, nodeBoot γ N vs ctxs id := by
  intro Hrb Hne Hnd Hnz Hlen HB Hmd HmdB
  unfold ownCommittedOps ownReadCtxs isCluster ownConfDecisions confAt ownSnapsMade
    joinAuth nodeBoot Cluster.dup Cluster.snapLoc Cluster.bootLen Cluster.trace Cluster.maxData
    isCommittedLogLb raftState nodeVacant clusterNoSnap
  by_cases hb : boot = []
  · subst hb
    rw [if_pos rfl]
    iintro -
    imod ApiImpl.cluster_alloc_dec_impl (GF := GF) N vs dup sl E md Hmd Hrb Hne Hnd Hnz Hlen
      with ⟨%γ, %Hd, Hops, Hctx, #Hcl, Hdec, #Hca, Hsm, Hja, Hfs⟩
    imodintro
    iexists γ
    rw [if_pos rfl]
    iframe Hops Hctx Hcl Hdec Hca Hsm Hja Hfs
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hd
    isplitr
    · ipureintro
      refine ⟨h1, h2, h3, h5, ?_⟩
      rw [h6]; cases ns
      · exact Iff.rfl
      · exact absurd rfl (Hns rfl)
    ipureintro; exact h4
  · simp only [hb, ↓reduceIte]
    iintro Hm
    imod ApiImpl.cluster_alloc_boot_impl (GF := GF) N vs ctxs boot dup sl E md Hmd HmdB ns Hns Hrb Hne
      Hnd Hnz Hlen (HB hb)
      $$ Hm with ⟨%γ, %Hd, Hops, Hctx, #Hcl, Hdec, #Hca, Hsm, #Hlb, Hbs⟩
    icases (BigSepL.bigSepL_sep_eqv (Φ := fun _ id => ApiImpl.nodeBootU (GF := GF) γ N vs ctxs id)
      (Ψ := fun _ id => iprop(ApiImpl.raftStateU (GF := GF) γ id RaftState.init ∗
        ApiImpl.nodeVacantU γ id))).1 $$ Hbs with ⟨#Hbs, Hrs⟩
    imodintro
    iexists γ
    iframe Hops Hctx Hcl Hdec Hca Hsm Hlb Hbs Hrs
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hd
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h5, by rw [h6]⟩
    ipureintro; exact h4

/-- **A new cluster of the voters `vs`, outside the no-snapshot mode** (`cluster_alloc_ns` at
`false`; the statement before auth-lease S4). -/
theorem cluster_alloc (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (dup : Bool) (sl : w64 → Option GName)
    (md : Option Nat) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    (boot ≠ [] → BootLog vs ctxs boot) →
    (∀ b, md = some b → b ≤ 2 ^ 31) →
    (∀ b, md = some b → ∀ e ∈ boot, e.data.length ≤ b) →
    ⊢ (if boot = [] then emp else bootMarshal (GF := GF) vs ctxs (LogEntry.toEntries boot 0)) ={E}=∗
      ∃ γ, ⌜γ.dup = dup ∧ γ.snapLoc = sl ∧ γ.bootLen = boot.length ∧ γ.maxData = md⌝ ∗
        -- (auth-lease S4, 2026-11-16) outside the no-snapshot mode
        ⌜¬ clusterNoSnap γ⌝ ∗
        -- (2026-11-09, Q8 stage 0, `notes/trace-validation-q6.md` item 9) an untraced cluster
        ⌜Cluster.trace γ = none⌝ ∗ ownCommittedOps (GF := GF) γ boot ∗
        ownReadCtxs γ ∅ ∗ isCluster γ N ∗ ownConfDecisions γ ∅ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMade γ [] ∗
        ([∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id) ∗
        if boot = [] then joinAuth γ (GMap.listToSet vs)
        else isCommittedLogLb γ boot ∗ [∗list] id ∈ vs, nodeBoot γ N vs ctxs id := by
  intro Hrb Hne Hnd Hnz Hlen HB Hmd HmdB
  iintro Hm
  imod cluster_alloc_ns N vs ctxs boot dup sl md E false (fun h => by cases h) Hrb Hne Hnd Hnz Hlen
    HB Hmd HmdB $$ Hm with ⟨%γ, %Hd, %Htr, H⟩
  imodintro
  iexists γ
  iframe H
  isplitr
  · ipureintro; exact ⟨Hd.1, Hd.2.1, Hd.2.2.1, Hd.2.2.2.1⟩
  isplitr
  · ipureintro; intro h; exact absurd (Hd.2.2.2.2.1 h) (by decide)
  ipureintro; exact Htr

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- (etcd-dist D7, 2026-11-23) **A founder's `nodeBoot` but `proto.Marshal`'s contract** (persistent),
at the bootstrap log `bl`: what a deployment's start, which has no heap, allocates for each voter
(`cluster_alloc_bootG`); the voter's own `bootMarshal` at its heap makes it `nodeBoot` (`nodeBoot_of_G`). -/
@[no_expose] def nodeBootG (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (bl : List EntryM) : IProp GF :=
  iprop(ApiImpl.nodeBootUG γ N vs ctxs id ∗ ⌜γ.raft.reBoot = bl⌝)

instance nodeBootG_persistent (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (bl : List EntryM) : Persistent (nodeBootG (GF := GF) γ N vs ctxs id bl) := by
  unfold nodeBootG; haveI := ApiImpl.nodeBootUG_persistent (GF := GF) γ N vs ctxs id; infer_instance

/-- (etcd-dist D7, 2026-11-23) **`cluster_alloc_ns` with a bootstrap log, over the global ghost state**:
the same cluster, without `bootMarshal` (a WP at the holder's heap), each voter's `nodeBootG` at the
bootstrap log's entries in place of its `nodeBoot`. -/
theorem cluster_alloc_bootG (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (dup : Bool) (sl : w64 → Option GName) (md : Option Nat) (E : CoPset)
    (ns : Bool) (Hns : ns = true → boot ≠ []) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    BootLog vs ctxs boot →
    (∀ b, md = some b → b ≤ 2 ^ 31) →
    (∀ b, md = some b → ∀ e ∈ boot, e.data.length ≤ b) →
    ⊢ |={E}=> ∃ γ, ⌜γ.dup = dup ∧ γ.snapLoc = sl ∧ γ.bootLen = boot.length ∧ γ.maxData = md ∧
          (clusterNoSnap γ ↔ ns = true)⌝ ∗
        ⌜Cluster.trace γ = none⌝ ∗ ownCommittedOps (GF := GF) γ boot ∗
        ownReadCtxs γ ∅ ∗ isCluster γ N ∗ ownConfDecisions γ ∅ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMade γ [] ∗
        ([∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id) ∗
        isCommittedLogLb γ boot ∗
        [∗list] id ∈ vs, nodeBootG γ N vs ctxs id (LogEntry.toEntries boot 0) := by
  intro Hrb Hne Hnd Hnz Hlen HB Hmd HmdB
  unfold ownCommittedOps ownReadCtxs isCluster ownConfDecisions confAt ownSnapsMade
    nodeBootG Cluster.dup Cluster.snapLoc Cluster.bootLen Cluster.trace Cluster.maxData
    isCommittedLogLb raftState nodeVacant clusterNoSnap
  imod ApiImpl.cluster_alloc_boot_implG_tr (GF := GF) N vs ctxs boot dup sl none E md Hmd HmdB ns Hns
    Hrb Hne Hnd Hnz Hlen HB with ⟨%γ, %Hd, Hops, Hctx, #Hcl, Hdec, #Hca, Hsm, #Hlb, Hbs⟩
  icases (BigSepL.bigSepL_sep_eqv (Φ := fun _ id => ApiImpl.nodeBootUG (GF := GF) γ N vs ctxs id)
    (Ψ := fun _ id => iprop(ApiImpl.raftStateU (GF := GF) γ id RaftState.init ∗
      ApiImpl.nodeVacantU γ id))).1 $$ Hbs with ⟨#Hbs, Hrs⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hd
  imodintro
  iexists γ
  iframe Hops Hctx Hcl Hdec Hca Hsm Hlb Hrs
  isplitr
  · ipureintro; exact ⟨h1, h2, h3, h5, by rw [h6]⟩
  isplitr
  · ipureintro; exact h4
  iapply BigSepL.bigSepL_mono ?_ $$ Hbs
  intro k id _
  iintro #H
  iframe H
  ipureintro; exact h7

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (etcd-dist D7, 2026-11-23) **A voter's `nodeBoot` from its `nodeBootG` and `proto.Marshal`'s contract at
its own heap**, at the bootstrap log `bl`. -/
theorem nodeBoot_of_G (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8)) (id : w64)
    (bl : List EntryM) :
    nodeBootG (GF := GF) γ N vs ctxs id bl ∗ bootMarshal vs ctxs bl ⊢ nodeBoot γ N vs ctxs id := by
  unfold nodeBootG nodeBoot
  iintro ⟨⟨Hg, %Hb⟩, Hm⟩
  subst Hb
  iapply (ApiImpl.nodeBootU_of_G γ N vs ctxs id).1
  isplitl [Hg]
  · iexact Hg
  iexact Hm

/-- **A new traced cluster** (2026-11-11, trace-check S7 part 2: Q6 item 8, revision 2 of
`notes/trace-validation-q6.md`; `notes/decisions.md`, "S7 (part 2)"): `cluster_alloc` with a
bootstrap log `boot` (a traced cluster needs one: `StartNode` is its only constructor, `RestartNode`
taking an untraced cluster), whose trace mode is the caller's directory `γd` (`Cluster.trace γ = some
γd`, the gate of every traced-only premise of the node API; the directory names the simulation's
ghost state, `traceDir`, which the caller allocates before). Everything else as `cluster_alloc`'s
post at `boot ≠ []`. (`lean` merge, stage 2) With `cluster_alloc`'s bound on proposed data `md`
(raft-entsize §2). -/
theorem cluster_alloc_traced (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (dup : Bool) (sl : w64 → Option GName) (γd : GName)
    (md : Option Nat) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    BootLog vs ctxs boot →
    (∀ b, md = some b → b ≤ 2 ^ 31) →
    (∀ b, md = some b → ∀ e ∈ boot, e.data.length ≤ b) →
    ⊢ bootMarshal (GF := GF) vs ctxs (LogEntry.toEntries boot 0) ={E}=∗
      ∃ γ, ⌜γ.dup = dup ∧ γ.snapLoc = sl ∧ γ.bootLen = boot.length ∧ γ.maxData = md⌝ ∗
        ⌜Cluster.trace γ = some γd⌝ ∗ ownCommittedOps (GF := GF) γ boot ∗
        ownReadCtxs γ ∅ ∗ isCluster γ N ∗ ownConfDecisions γ ∅ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMade γ [] ∗
        ([∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id) ∗
        isCommittedLogLb γ boot ∗ [∗list] id ∈ vs, nodeBoot γ N vs ctxs id := by
  intro Hrb Hne Hnd Hnz Hlen HB Hmd HmdB
  unfold ownCommittedOps ownReadCtxs isCluster ownConfDecisions confAt ownSnapsMade
    nodeBoot Cluster.dup Cluster.snapLoc Cluster.bootLen Cluster.trace Cluster.maxData
    isCommittedLogLb raftState nodeVacant
  iintro Hm
  imod ApiImpl.cluster_alloc_boot_impl_tr (GF := GF) N vs ctxs boot dup sl (some γd) E md Hmd HmdB
    false (fun h => by cases h) Hrb Hne Hnd Hnz Hlen HB $$ Hm with ⟨%γ, %Hd, Hops, Hctx, #Hcl, Hdec, #Hca, Hsm, #Hlb, Hbs⟩
  icases (BigSepL.bigSepL_sep_eqv (Φ := fun _ id => ApiImpl.nodeBootU (GF := GF) γ N vs ctxs id)
    (Ψ := fun _ id => iprop(ApiImpl.raftStateU (GF := GF) γ id RaftState.init ∗
      ApiImpl.nodeVacantU γ id))).1 $$ Hbs with ⟨#Hbs, Hrs⟩
  imodintro
  iexists γ
  iframe Hops Hctx Hcl Hdec Hca Hsm Hlb Hbs Hrs
  isplitr
  · ipureintro; exact ⟨Hd.1, Hd.2.1, Hd.2.2.1, Hd.2.2.2.2.1⟩
  ipureintro; exact Hd.2.2.2.1

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
/-! ## Joining -/

/-- **Reserving a new id**: its durable state at `RaftState.init` and its vacant slot, out of the
authority (2026-11-01, durability stage I-7; until then a newcomer's token, `nodeJoin`). -/
theorem joinAuth_join (γ : Cluster) (N : Namespace) (U : GSet w64) (id : w64) :
    id ∉ U → id ≠ W64 0 →
    isCluster (GF := GF) γ N ∗ joinAuth γ U ==∗
      joinAuth γ ({[id]} ∪ U) ∗ raftState γ id RaftState.init ∗ nodeVacant γ id := by
  intro hU hz
  unfold isCluster joinAuth raftState nodeVacant
  exact ApiImpl.joinAuth_join_impl γ N U id hU hz

/-- (2026-11-22, kvraft decision B) **A new cluster of the voters `vs` without a bootstrap log, at a
global ghost state**: `cluster_alloc`'s post at `boot = []`, stated over `[AllG] [ReceiptGS] [InvGS]`
only (no heap, no Go semantics: `cluster_alloc`'s premise `bootMarshal` is a WP, so its statement
needs them), for an allocation before any machine runs (kvraft's adequacy `Hstart`). -/
theorem cluster_alloc_nb (N : Namespace) (vs : List w64) (dup : Bool) (sl : w64 → Option GName)
    (md : Option Nat) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    (∀ b, md = some b → b ≤ 2 ^ 31) →
    ⊢ |={E}=> ∃ γ, ⌜γ.dup = dup ∧ γ.snapLoc = sl ∧ γ.bootLen = 0 ∧ γ.maxData = md⌝ ∗
        ⌜¬ clusterNoSnap γ⌝ ∗ ⌜Cluster.trace γ = none⌝ ∗ ownCommittedOps (GF := GF) γ [] ∗
        ownReadCtxs γ ∅ ∗ isCluster γ N ∗ ownConfDecisions γ ∅ ∗
        confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMade γ [] ∗
        ([∗list] id ∈ vs, raftState γ id RaftState.init ∗ nodeVacant γ id) ∗
        joinAuth γ (GMap.listToSet vs) := by
  intro Hrb Hne Hnd Hnz Hlen Hmd
  unfold ownCommittedOps ownReadCtxs isCluster ownConfDecisions confAt ownSnapsMade
    joinAuth Cluster.dup Cluster.snapLoc Cluster.bootLen Cluster.trace Cluster.maxData
    raftState nodeVacant clusterNoSnap
  imod ApiImpl.cluster_alloc_dec_impl (GF := GF) N vs dup sl E md Hmd Hrb Hne Hnd Hnz Hlen
    with ⟨%γ, %Hd, Hops, Hctx, #Hcl, Hdec, #Hca, Hsm, Hja, Hfs⟩
  imodintro
  iexists γ
  iframe Hops Hctx Hcl Hdec Hca Hsm Hja Hfs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hd
  isplitr
  · ipureintro; exact ⟨h1, h2, h3, h5⟩
  isplitr
  · ipureintro; rw [h6]; decide
  ipureintro; exact h4

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-! ## Stopped nodes (2026-10-29, stage U9a) -/

/-- **A running node has not stopped**: a holder of a share of `nodeRunning` refutes the stopped
answers (`node.Advance`'s and `node.ApplyConfChange`'s stopped cases). -/
theorem nodeRunning_stopped (n : NodeH) (γ : Cluster) (N : Namespace) (q : Qp) :
    nodeRunning (GF := GF) n γ N q ∗ nodeStopped n γ N ⊢ False := by
  unfold nodeRunning nodeStopped
  iintro H
  iapply ApiImpl.nodeRunning_stopped_impl n γ N q $$ H

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
/-! ## Decisions -/

theorem ownConfDecisions_excl (γ : Cluster) (D1 D2 : GMap Nat ConfDecision) :
    ownConfDecisions (GF := GF) γ D1 ∗ ownConfDecisions γ D2 ⊢ False := by
  unfold ownConfDecisions; exact ApiImpl.ownConfDecisions_excl_impl γ D1 D2

theorem ownConfDecisions_lookup (γ : Cluster) (D : GMap Nat ConfDecision) (k : Nat)
    (d : ConfDecision) :
    ownConfDecisions (GF := GF) γ D ∗ confDecided γ k d ⊢ ⌜D !! k = some d⌝ := by
  unfold ownConfDecisions confDecided; exact ApiImpl.ownConfDecisions_lookup_impl γ D k d

/-- A recorded decision's witness (the authority given back). -/
theorem ownConfDecisions_witness (γ : Cluster) (D : GMap Nat ConfDecision) (k : Nat)
    (d : ConfDecision) :
    D !! k = some d →
    ownConfDecisions (GF := GF) γ D ⊢ ownConfDecisions γ D ∗ confDecided γ k d := by
  intro h
  unfold ownConfDecisions confDecided; exact ApiImpl.ownConfDecisions_witness_impl γ D k d h

/-- Two decisions of one position agree (without the authority). -/
theorem confDecided_agree (γ : Cluster) (k : Nat) (d1 d2 : ConfDecision) :
    confDecided (GF := GF) γ k d1 ∗ confDecided γ k d2 ⊢ ⌜d1 = d2⌝ := by
  unfold confDecided; exact ApiImpl.confDecided_agree_impl γ k d1 d2

/-- **Deciding an undecided committed conf entry**, at the configuration before it, with an allowed
decision: one shot per position (the map grows only where it is undefined). -/
theorem confDecide (γ : Cluster) (N : Namespace) (D : GMap Nat ConfDecision) (l : List LogEntry)
    (k : Nat) (e : LogEntry) (m m' : Membership) (d : ConfDecision) :
    D !! k = none → l[k]? = some e → e.isConfChange → d.step m = some m' →
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ∗ confAt γ k m ∗ ownConfDecisions γ D ==∗
      ownConfDecisions γ (D.insert k d) ∗ confDecided γ k d ∗ confAt γ (k + 1) m' := by
  intro hD he hc hs
  unfold isCluster isCommittedLogLb confAt ownConfDecisions confDecided
  exact ApiImpl.confDecide_impl γ N D l k e m m' d hD he hc hs

/-! ## The configuration -/

theorem confAt_agree (γ : Cluster) (k : Nat) (m1 m2 : Membership) :
    confAt (GF := GF) γ k m1 ∗ confAt γ k m2 ⊢ ⌜m1 = m2⌝ := by
  unfold confAt; exact ApiImpl.confAt_agree_impl γ k m1 m2

theorem confAt_valid (γ : Cluster) (k : Nat) (m : Membership) :
    confAt (GF := GF) γ k m ⊢ ⌜m.Valid⌝ := by
  unfold confAt; exact ApiImpl.confAt_valid_impl γ k m

/-- **A configuration is recorded only over the committed log** (T10 step 3 (B), B8): the
membership at `k` is at most the committed log's length. -/
theorem confAt_committed (γ : Cluster) (k : Nat) (m : Membership) :
    confAt (GF := GF) γ k m ⊢ ∃ l, isCommittedLogLb γ l ∗ ⌜k ≤ l.length⌝ := by
  unfold confAt isCommittedLogLb; exact ApiImpl.confAt_committed_impl γ k m

/-- **Every committed conf entry decodes** (2026-10-29, stage U5): the leader decodes every conf
entry it appends (`raft.go:1320`, raft's own automatic leave by `ccDecodeV2_nil`), so an application
that decodes a committed one never fails. -/
theorem committed_confDecodes (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ⊢
      ⌜∀ e ∈ l, e.isConfChange → ConfEntryDecodes e⌝ := by
  unfold isCluster isCommittedLogLb; exact ApiImpl.committed_confDecodes_impl γ N l

/-- **A committed empty `ConfChangeV2` is at a joint configuration** (2026-10-29, stage U5): raft's
automatic leave, or a client's explicit empty change, is appended only at a joint configuration with
every conf entry before it applied (`stepLeader`'s `alreadyJoint && !wantsLeaveJoint` refusal), so
applying it (leaving the joint configuration) is defined. -/
theorem committed_emptyV2_joint (γ : Cluster) (N : Namespace) (l : List LogEntry) (k : Nat)
    (e : LogEntry) (m : Membership) :
    l[k]? = some e → e.isEmptyV2 →
    isCluster (GF := GF) γ N ∗ isCommittedLogLb γ l ∗ confAt γ k m ⊢ ⌜m.isJoint⌝ := by
  intro hk he
  unfold isCluster isCommittedLogLb confAt
  exact ApiImpl.committed_emptyV2_joint_impl γ N l k e m hk he

/-- **Past entries that are no conf change** (candidate 13's `confAt_normal`, over a range). -/
theorem confAt_noConf (γ : Cluster) (l : List LogEntry) (a b : Nat) (m : Membership) :
    NoConfChangeIn l a b → a ≤ b → b ≤ l.length →
    isCommittedLogLb (GF := GF) γ l ∗ confAt γ a m ⊢ confAt γ b m := by
  intro hn hab hb
  unfold isCommittedLogLb confAt; exact ApiImpl.confAt_noConf_impl γ l a b m hn hab hb

/-- **Past a decided conf entry**: the decision's result. -/
theorem confAt_decided (γ : Cluster) (k : Nat) (m : Membership) (d : ConfDecision) :
    confAt (GF := GF) γ k m ∗ confDecided γ k d ⊢
      ∃ m', ⌜d.step m = some m'⌝ ∗ confAt γ (k + 1) m' := by
  unfold confAt confDecided; exact ApiImpl.confAt_decided_impl γ k m d

/-- **Every conf entry of `l` in `[a, b)` is decided `.skip`** (persistent; §4 of the decision
switch): what `node.ApplyConfChange` and `node.Advance` take for the conf entries their view passes
(until then none at all, `NoConfChangeIn`). -/
def skippedIn (γ : Cluster) (l : List LogEntry) (a b : Nat) : IProp GF :=
  [∗list] j ∈ List.range' a (b - a),
    iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ → confDecided γ j .skip)

instance skippedIn_persistent (γ : Cluster) (l : List LogEntry) (a b : Nat) :
    Persistent (skippedIn (GF := GF) γ l a b) := by
  unfold skippedIn; infer_instance

/-- With no conf entry in the range, nothing to decide. -/
theorem skippedIn_noConf (γ : Cluster) (l : List LogEntry) (a b : Nat) :
    NoConfChangeIn l a b → ⊢ skippedIn (GF := GF) γ l a b := by
  intro hn
  unfold skippedIn
  have H : ∀ xs : List Nat, (∀ j ∈ xs, a ≤ j ∧ j < b) →
      ⊢ [∗list] j ∈ xs, iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ →
        confDecided (GF := GF) γ j .skip) := by
    intro xs
    induction xs with
    | nil => intro _; iapply BigSepL.bigSepL_nil.2; iempintro
    | cons j xs ih =>
      intro hx
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iintro %e %he
        exfalso
        exact absurd he.2 (hn j e (hx j (List.mem_cons_self ..)).1 (hx j (List.mem_cons_self ..)).2 he.1)
      iapply ih (fun x h => hx x (List.mem_cons_of_mem _ h))
  exact H _ (fun j hj => by have := List.mem_range'_1.1 hj; omega)

/-- (2026-10-30, stage R3) **Past skipped conf entries**: the membership stays. -/
theorem confAt_skipped (γ : Cluster) (l : List LogEntry) (a b : Nat) (m : Membership) :
    a ≤ b → b ≤ l.length →
    isCommittedLogLb (GF := GF) γ l ∗ confAt γ a m ∗ skippedIn γ l a b ⊢ confAt γ b m := by
  intro hab hb
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  clear hab
  induction n generalizing a with
  | zero => iintro ⟨-, Hc, -⟩; iExactEq Hc; rfl
  | succ n ih =>
    unfold skippedIn
    rw [show a + (n + 1) - a = n + 1 by omega, List.range'_succ]
    iintro ⟨#Hl, #Hc, #Hs⟩
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨#Hs0, #Hs⟩
    ihave #Hc1 : confAt (GF := GF) γ (a + 1) m $$ []
    · cases he : l[a]? with
      | none =>
        exfalso
        have := List.getElem?_eq_none_iff.1 he
        omega
      | some e =>
        by_cases hcc : e.isConfChange
        · ihave #Hd := Hs0 $$ %e %(And.intro rfl hcc)
          icases confAt_decided γ a m .skip $$ [Hc Hd] with ⟨%m', %Hm', #Hc'⟩
          · iframe Hc Hd
          simp only [ConfDecision.step] at Hm'
          cases Hm'
          iexact Hc'
        · iapply confAt_noConf γ l a (a + 1) m
            (fun k e' h1 h2 h3 => by
              have : k = a := by omega
              subst this; rw [he] at h3; cases h3; exact hcc)
            (by omega) (by omega)
          iframe Hl Hc
    rw [show a + (n + 1) = (a + 1) + n by omega]
    iapply ih (a + 1) (by omega)
    iframe Hl Hc1
    unfold skippedIn
    rw [show a + 1 + n - (a + 1) = n by omega]
    iexact Hs

/-! ## Snapshots -/

/-- **A snapshot made is one of the client's.** -/
theorem snapMade_elem (γ : Cluster) (S : List SnapRec) (s : SnapRec) :
    ownSnapsMade (GF := GF) γ S ∗ snapMade γ s ⊢ ⌜s ∈ S⌝ := by
  unfold ownSnapsMade snapMade; exact ApiImpl.snapMade_elem_impl γ S s

/-- **Certifying a snapshot of a committed prefix** `l` (its length `i`, last term `t`) at the
membership `m` after it (`confAt`), its `ConfState` `cs` reporting `m`, its data `d` anything: the
snapshot is recorded as made. A fancy update inside `N` (it opens raft's commit invariant); the
lists' well-formedness raft's `restore` needs (`SnapListsOk`: ids nonzero, at most `2^62` entries in
all, the index below `2^61`) a premise (`notes/decisions.md`, "Stages U2, U3"). -/
theorem snapshotCert_make (γ : Cluster) (N : Namespace) (E : CoPset) (l : List LogEntry) (i t : w64)
    (d : List w8) (m : Membership) (cs : ConfStateM) (S : List SnapRec) :
    ↑N ⊆ E → l.length = uint.nat i → Option.map LogEntry.term l.getLast? = some t →
    SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ → confStateIs cs m →
    ⊢ isCluster (GF := GF) γ N -∗ isCommittedLogLb γ l -∗ confAt γ l.length m -∗
      ownSnapsMade γ S ={E}=∗
      ownSnapsMade γ (S ++ [⟨l.length, m, d⟩]) ∗
      snapshotCert γ N ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ := by
  intro HE Hlen Hlast Hok Hcs
  unfold isCluster isCommittedLogLb confAt ownSnapsMade snapshotCert
  exact ApiImpl.snapshotCert_make_impl γ N E HE l i t d m cs S Hlen Hlast Hok Hcs

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- (restart S7.3, 2026-11-14; `notes/restart-s7-p2a.md`) **A `MsgSnap`'s destination, in the
cluster's configurations**: a message with `snapTo` (a `Ready`'s, `readyRest_snapTo`; a sent one's,
`sentMsg_snapTo`), if a `MsgSnap`, is not to its sender `id` and is to an id of a membership after a
committed prefix (`confAt`), with a lower bound of the committed log covering it. The premise
`confAt γ k0 m0` (any one; a cluster's boot membership `confAt γ 0 _` serves) witnesses that the
cluster is in the client's decision mode (raft's dynamic mode), where `snapTo` carries the
destination's configuration. So in a cluster whose committed memberships are all `simple {id}` (etcd's
one-member cluster) no `MsgSnap` is ever sent (`srvRestartRows_single`). -/
theorem snapTo_confAt (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (id : w64)
    (st : MsgSt) (k0 : Nat) (m0 : Membership) (Hty : st.msg.Type' = MsgSnap) :
    ⊢ isCluster (GF := GF) γ N -∗ confAt γ k0 m0 -∗ snapTo γ id st ={E}=∗
      ⌜st.msg.To' ≠ id⌝ ∗ ∃ (k : Nat) (m : Membership) (l : List LogEntry), confAt γ k m ∗
        isCommittedLogLb γ l ∗ ⌜k ≤ l.length ∧ st.msg.To' ∈ m.ids⌝ := by
  unfold isCluster confAt snapTo ApiImpl.isClusterU isCommittedLogLb
  haveI := ApiImpl.clusterInv_persistent (GF := GF) γ N
  haveI := ApiImpl.confAtU_persistent (GF := GF) γ k0 m0
  iintro ⟨-, #Hci, -⟩ #Hc0 #Hs
  iapply ApiImpl.snapTo_confAt_impl γ N E HE id st k0 m0 Hty $$ Hci Hc0 Hs

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
variable [CrashGS GF] in
/-- (2026-11-21, the crash invariant: `notes/raft-crash-law-design.md` (i)) **Arming a vacancy**:
an arm of `id`'s crash invariant, the vacancy for the node to start from (`nodeVacantA`) and the
arm's crash token for the crash (`nodeCrashTok`). -/
theorem nodeVacant_arm (γ : Cluster) (id : w64) (E : CoPset) :
    ⊢ nodeVacant (GF := GF) γ id ={E}=∗ ∃ x, nodeVacantA γ id x ∗ nodeCrashTok γ id x := by
  unfold nodeVacant nodeVacantA nodeCrashTok
  exact ApiImpl.nodeVacant_arm_impl γ id E

variable [CrashGS GF] in
/-- (2026-11-21) **Arming a vacancy, the crash token dropped**: for a client whose crash is
`node.Stop`'s (kvdurable, kvreconf, the server), which never needs the vacancy back after a real
crash. -/
theorem nodeVacant_armD (γ : Cluster) (id : w64) (E : CoPset) :
    ⊢ nodeVacant (GF := GF) γ id ={E}=∗ ∃ x, nodeVacantA γ id x := by
  iintro Hv
  imod nodeVacant_arm γ id E $$ Hv with ⟨%x, Hv, -⟩
  imodintro
  iexists x
  iexact Hv

variable [CrashGS GF] in
/-- (2026-11-21) **A crash gives the vacancy back**: whether a node of `id` ran from the arm or
not (and whatever it held), the arm's crash token and the crash's `crashed` give `nodeVacant`. -/
theorem nodeCrash (γ : Cluster) (N : Namespace) (id : w64) (x : CrashNames) (E : CoPset)
    (HE : ↑N ⊆ E) :
    ⊢ isCluster (GF := GF) γ N -∗ crashed -∗ nodeCrashTok γ id x ={E}=∗ nodeVacant γ id := by
  unfold isCluster nodeCrashTok nodeVacant ApiImpl.isClusterU
  haveI := ApiImpl.clusterInv_persistent (GF := GF) γ N
  iintro ⟨-, #Hci, -⟩ Hc Htok
  unfold ApiImpl.clusterInv
  icases Hci with ⟨%HNs, -⟩
  iapply ApiImpl.nodeCrash_impl γ N id x E HE HNs $$ Hc Htok

end api


section validLists
variable [GooseExts]

/-- (raft-final, 2026-10-29, for kvreconf) **A valid membership's `ConfState` has well-formed lists**
(`SnapListsOk`, `snapshotCert_make`'s premise), given what `Restore` needs beyond validity (no id `0`,
no staged learner that is an incoming voter: `Membership.Restorable`'s two clauses, here spelled out:
`ConfchangeApi.lean`'s `Membership.Valid.snapListsOk'` takes `Restorable`), fewer than `2^61` ids and
the index below `2^61`. -/
theorem Membership.Valid.snapListsOk {m : Membership} {cs : ConfStateM} {t i : w64} {d : List w8} :
    m.Valid → confStateIs cs m → W64 0 ∉ m.ids → (∀ k, k ∈ m.learnersNext → k ∉ m.voters) →
    GMap.size m.ids < 2 ^ 61 → uint.Z i < 2 ^ 61 →
    SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ := by
  intro hv hcs h0 hln hsz hi
  obtain ⟨⟨⟨_, hInv2, hInv3, hInv4⟩, hne, _⟩, _⟩ := hv
  obtain ⟨pv, po, pl, pln, _⟩ := hcs
  simp only [ApiImpl.stOf, cfgStateC, ApiImpl.cfgOf] at hInv2 hInv3 hInv4 hne
  have mem : ∀ {L : List w64} {X : GSet w64} (x : w64), L.Perm (elements X) → (x ∈ L ↔ x ∈ X) :=
    fun x hp => by rw [hp.mem_iff, GMap.elem_of_elements]
  have hids : ∀ x, x ∈ m.ids ↔ x ∈ m.voters ∨ x ∈ m.votersOutgoing ∨ x ∈ m.learners ∨
      x ∈ m.learnersNext := by
    intro x; simp only [Membership.ids, GMap.elem_of_union, or_assoc]
  -- the sizes: voters, learners, staged learners are disjoint, all inside the ids
  have hdisj : (elements m.voters ++ elements m.learners ++ elements m.learnersNext).Nodup := by
    simp only [List.nodup_append, GMap.NoDup_elements, true_and, List.mem_append,
      GMap.elem_of_elements]
    refine ⟨fun a ha b hb e => ?_, fun a ha b hb e => ?_⟩
    · subst e; exact (hInv3 a hb).2.1 ha
    · subst e
      rcases ha with ha | ha
      · exact hln a hb ha
      · have h1 := (hInv2 a hb).2; have h2 := (hInv3 a ha).2.2; rw [h1] at h2; cases h2
  have hsub : GMap.listToSet (elements m.voters ++ elements m.learners ++ elements m.learnersNext) ⊆
      m.ids := by
    rw [GMap.elem_of_subseteq]; intro x hx
    rw [GMap.elem_of_list_to_set] at hx
    simp only [List.mem_append, GMap.elem_of_elements] at hx
    rw [hids]
    rcases hx with (h | h) | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  have h3 := GMap.subseteq_size hsub
  rw [GMap.size_list_to_set _ hdisj] at h3
  simp only [List.length_append, GMap.length_elements] at h3
  have hosub : m.votersOutgoing ⊆ m.ids := by
    rw [GMap.elem_of_subseteq]; intro x hx; rw [hids]; exact .inr (.inl hx)
  have ho := GMap.subseteq_size hosub
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hi⟩
  · intro he
    apply hne
    apply GMap.set_eq; intro x
    refine ⟨fun hx => ?_, fun hx => absurd hx (GMap.not_elem_of_empty x)⟩
    have := (mem x pv).2 hx; change cs.Voters' = [] at he; rw [he] at this; simp at this
  · intro x hx he; subst he
    simp only [ConfStateM.lists] at hx
    apply h0; rw [hids]
    rcases hx with h | h | h | h
    · exact .inr (.inl ((mem _ po).1 h))
    · exact .inl ((mem _ pv).1 h)
    · exact .inr (.inr (.inl ((mem _ pl).1 h)))
    · exact .inr (.inr (.inr ((mem _ pln).1 h)))
  · intro x hx
    simp only [ConfStateM.lists] at hx ⊢
    rw [mem x pl] at hx; rw [mem x pv, mem x po]
    exact ⟨(hInv3 x hx).2.1, (hInv3 x hx).1⟩
  · intro x hx
    simp only [ConfStateM.lists] at hx ⊢
    rw [mem x pln] at hx; rw [mem x po, mem x pv, mem x pl]
    refine ⟨(hInv2 x hx).1, hln x hx, fun hl => ?_⟩
    have h1 := (hInv2 x hx).2; have h2 := (hInv3 x hl).2.2; rw [h1] at h2; cases h2
  · intro hvo
    simp only [ConfStateM.lists] at hvo ⊢
    have : m.votersOutgoing = ∅ := by
      apply GMap.set_eq; intro x
      refine ⟨fun hx => ?_, fun hx => absurd hx (GMap.not_elem_of_empty x)⟩
      have := (mem x po).2 hx; simp [hvo] at this
    have := (hInv4 this).1
    rw [this] at pln
    have he : elements (∅ : GSet w64) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [he] at pln; exact pln.eq_nil
  · exact pv.nodup_iff.2 (GMap.NoDup_elements _)
  · exact pl.nodup_iff.2 (GMap.NoDup_elements _)
  · exact po.nodup_iff.2 (GMap.NoDup_elements _)
  · exact pln.nodup_iff.2 (GMap.NoDup_elements _)
  · simp only [ConfStateM.lists, pv.length_eq, pl.length_eq, po.length_eq, pln.length_eq,
      GMap.length_elements]
    omega
  · intro hvo
    simp only [ConfStateM.lists] at hvo
    have : m.votersOutgoing = ∅ := by
      apply GMap.set_eq; intro x
      refine ⟨fun hx => ?_, fun hx => absurd hx (GMap.not_elem_of_empty x)⟩
      have := (mem x po).2 hx; simp [hvo] at this
    exact (hInv4 this).2

end validLists

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **What a certificate says**: the snapshot is of a committed prefix of its length and last term,
at the membership after it (which its lists and auto-leave flag report), and was made. -/
theorem snapshotCert_made (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    isCluster (GF := GF) γ N ∗ snapshotCert γ N k ⊢
      ∃ (l : List LogEntry) (m : Membership), isCommittedLogLb γ l ∗ confAt γ l.length m ∗
        snapMade γ ⟨l.length, m, k.dat⟩ ∗
        ⌜l.length = uint.nat k.sid.index' ∧ Option.map LogEntry.term l.getLast? = some k.sid.term' ∧
          k.cl.Is m ∧ k.al = m.autoLeave⌝ := by
  unfold isCluster isCommittedLogLb confAt snapMade snapshotCert
  exact ApiImpl.snapshotCert_made_impl γ N k

/-- **The snapshot `sv` is valid** for the cluster (persistent; U8 v2, candidate 17 rev 3 §2,
`notes/spec-first-study/raft-storage-spec.md`): it is of a non-empty committed prefix `l` of its
index and last term, its `ConfState` reports the membership `m` after `l` (`confAt`), and it was made
(`snapMade`, with its data). Exposed: what a client's `Storage.Snapshot` promises of a non-empty
snapshot (`isStorageD`), replacing the certificate registry (`snapshotCert` with `storCert`). -/
def snapshotValid (γ : Cluster) (sv : SnapshotM) : IProp GF :=
  iprop(∃ (l : List LogEntry) (m : Membership), isCommittedLogLb γ l ∗ confAt γ l.length m ∗
    snapMade γ ⟨l.length, m, sv.Data'⟩ ∗
    ⌜l.length = uint.nat sv.Metadata'.Index' ∧ 0 < l.length ∧
      Option.map LogEntry.term l.getLast? = some sv.Metadata'.Term' ∧
      confStateIs sv.Metadata'.ConfState' m ∧
      -- (U8 v2, 2026-10-29) the bounds raft's certificate needs (`SnapListsOk`), which nothing
      -- above gives (a joint configuration may list `2^62 + 2` ids)
      l.length < 2 ^ 61 ∧
      (sv.Metadata'.ConfState'.Voters'.length + sv.Metadata'.ConfState'.Learners'.length +
        sv.Metadata'.ConfState'.VotersOutgoing'.length +
        sv.Metadata'.ConfState'.LearnersNext'.length : Int) ≤ 2 ^ 62⌝)

instance snapshotValid_persistent (γ : Cluster) (sv : SnapshotM) :
    Persistent (snapshotValid (GF := GF) γ sv) := by
  unfold snapshotValid; infer_instance

/-- (R2d, Q17 F6, 2026-11-06) No later credit to open an invariant holding it (the server's WAL
durability invariant holds a record's certificate, `walSnapCert`). -/
instance snapshotValid_timeless (γ : Cluster) (sv : SnapshotM) :
    Timeless (snapshotValid (GF := GF) γ sv) := by
  unfold snapshotValid; infer_instance

/-- (R2d, Q17 F6) **A valid snapshot's data is one the client made** (its registry `S`). -/
theorem ownSnapsMade_snapshotValid_data (γ : Cluster) (S : List SnapRec) (sv : SnapshotM) :
    ownSnapsMade (GF := GF) γ S ∗ snapshotValid γ sv ⊢ ⌜∃ r ∈ S, r.data = sv.Data'⌝ := by
  iintro ⟨Hown, #Hsv⟩
  unfold snapshotValid
  icases Hsv with ⟨%l, %m, -, -, #Hmade, -⟩
  ihave %Hin := snapMade_elem γ S _ $$ [$Hown $Hmade]
  ipureintro
  exact ⟨_, Hin, rfl⟩

/-! ## The storage contract at the node API (U8 v2, 2026-10-29; candidate 17 rev 3 §2) -/

/-- The compaction's justification (`isStorageP`'s `Bnd`): compacting at or past `c` is safe
(`nodeAppliedLb`, which since 2026-11-01 holds the snapshot hand-out). (2026-11-01, durability stage
I-4: keyed by the storage's key `K`.) (2026-11-12, trace-check's small items: Q39 (a), the design's
B2, `notes/trace-validation-q6.md` §7) **Gated on the trace**: at a traced cluster no compaction is
justified (`c = 0`), so that the specification never has to follow a snapshot (what `rnTrace`'s
`TrNoSnap` is built from at `setupNode`, A4); untraced, as before, and (auth-lease S4, 2026-11-16,
L-r2) in the cluster's no-snapshot mode never past index `1` (the client's promise; raft's leaders
then never fall back to a snapshot). Sealed: clients use `storBnd_zero`, `storBnd_intro_untraced`
and `storBnd_cap`. -/
@[no_expose] def storBnd (γ : Cluster) (K : GName) (c : Nat) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(∃ k : Nat, ⌜c ≤ k⌝ ∗ nodeAppliedLb γ K k ∗ ⌜clusterNoSnap γ → k ≤ 1⌝)
  | some _ => iprop(⌜c = 0⌝)

/-- (2026-11-12, trace-check implementation step 1: the design's B2) **No compaction is always
justified** (any cluster; what a storage that never compacts, the trace-check harness's, uses). -/
theorem storBnd_zero (γ : Cluster) (K : GName) : ⊢ storBnd (GF := GF) γ K 0 := by
  unfold storBnd
  split
  · iexists 0
    isplitr; · ipureintro; exact Nat.le_refl 0
    isplitr
    · iapply nodeAppliedLb_zero γ K
    ipureintro; intro _; exact Nat.zero_le 1
  · ipureintro; rfl

/-- (2026-11-12, trace-check implementation step 1: the design's B2) **At an untraced cluster,
compacting at or below the applied index is justified** (what the key-value stores' and etcd's
server's storages use in place of unfolding `storBnd`), (auth-lease S4, L-r2) in the no-snapshot
mode at an applied index at most `1` (`hns`). -/
theorem storBnd_intro_untraced (γ : Cluster) (K : GName) (k c : Nat) (h : Cluster.trace γ = none)
    (hns : clusterNoSnap γ → k ≤ 1) :
    ⊢ nodeAppliedLb (GF := GF) γ K k -∗ ⌜c ≤ k⌝ -∗ storBnd γ K c := by
  iintro #Hl %Hc
  unfold storBnd
  rw [h]
  iexists k; iframe Hl
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact hns

/-- (auth-lease S4, L-r2) **In the no-snapshot mode, the storage is compacted at most to `1`.** -/
theorem storBnd_cap (γ : Cluster) (K : GName) (c : Nat) :
    storBnd (GF := GF) γ K c ⊢ ⌜clusterNoSnap γ → c ≤ 1⌝ := by
  unfold storBnd
  split
  · iintro ⟨%k, %hk, -, %h⟩
    ipureintro; intro hm; have := h hm; omega
  · iintro %h
    ipureintro; intro _; omega

-- (2026-11-01, durability stage I-4) `storDL γ id i` (an open definition: "the committed log
-- delivered to some node `id`") is now the sealed `nodeCommitLb γ K i` (`InvNode.lean`): it is
-- given at the attach, before anything is delivered.

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- **The storage contract of the storage `st` of key `K`** (persistent; the frozen design's §2,
`isStorageP` at the cluster's pieces). (2026-11-01, durability stage I-4: keyed by `K`.)
(out_size C2) **Sized when the cluster bounds proposed data** (`γ.maxData ≠ none`): `Entries`
returns objects at contents of bounded size, cut at `maxSize` when `maxSize ≤ 2^20` (`isStorageP`'s
flag); what raft's `MsgApp` size bound and the handed-out entries' (`Cluster.outEnt_size`) rest on.
A cluster without the bound (`maxData = none`, kv's) asks nothing more of its storage. -/
def isStorage (γ : Cluster) (K : GName) (st : Storage)
    (SV : SnapshotM → IProp GF := snapshotValid γ) : IProp GF :=
  isStorageP γ.maxData.isSome SV (storBnd γ K) (nodeCommitLb γ K) st

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
/-- The node pinned this certificate for snapshots returned by its storage at attach. -/
@[no_expose] def nodeTagPin (γ : Cluster) (n : NodeH) (SV : SnapshotM → IProp GF) : IProp GF :=
  iprop(∃ γn : NodeNames, ApiImpl.nodeTabOk γ n γn ∗ savedPredOwn γn.sn.gsv DFrac.discard SV)

instance nodeTagPin_persistent (γ : Cluster) (n : NodeH) (SV : SnapshotM → IProp GF) :
    Persistent (nodeTagPin γ n SV) := by
  unfold nodeTagPin
  haveI (γn : NodeNames) := ApiImpl.nodeTabOk_persistent (GF := GF) γ n γn
  infer_instance

/-- The certificate carried by the received-snapshot path of this node. -/
@[no_expose] def nodeRestoreCert (γ : Cluster) (n : NodeH) (sv : SnapshotM) : IProp GF :=
  iprop(∃ γn : NodeNames, ApiImpl.nodeTabOk γ n γn ∗
    ksnCert γn.sn (snapTrip sv sv.Metadata'.ConfState'.lists))

instance nodeRestoreCert_persistent (γ : Cluster) (n : NodeH) (sv : SnapshotM) :
    Persistent (nodeRestoreCert (GF := GF) γ n sv) := by
  unfold nodeRestoreCert
  haveI (γn : NodeNames) := ApiImpl.nodeTabOk_persistent (GF := GF) γ n γn
  infer_instance

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
/-- For an outgoing MsgSnap, the storage supplied its pinned certificate or raft
carried the certificate for a received snapshot. The later comes from saved
predicate agreement and applies only to the client-selected certificate. -/
theorem readySnapSources_msgSnap (γ : Cluster) (n : NodeH) (id : w64) {term : w64} {bound : Nat} {installed : Option w64} (ms : List QMsg)
    (q : QMsg) (SV : SnapshotM → IProp GF) (hq : q ∈ ms) (ht : q.st.msg.Type' = MsgSnap) :
    ⊢ readySnapSources (GF := GF) γ n id term ms bound installed -∗ nodeTagPin γ n SV -∗
      ∃ sv : SnapshotM, ⌜q.st.snap = some sv⌝ ∗ (▷ SV sv ∨ nodeRestoreCert γ n sv ∗ nodeRestoreSource γ id (snapId sv)) := by
  haveI (γn : NodeNames) := ApiImpl.nodeTabOk_persistent (GF := GF) γ n γn
  unfold readySnapSources ApiImpl.snapSources nodeTagPin
  iintro ⟨%γn, #Htab, #Hs, -⟩ ⟨%γp, #Htabp, #Hpin⟩
  iunfold readyMsgOrigins at Hs
  icases Hs with ⟨%ks, #Hhist, #Hs⟩
  iunfold qSrcs at Hs
  ihave ⟨#Hq, -⟩ := BigSepL.bigSepL_mem_acc hq $$ Hs
  iunfold qSrc at Hq
  iunfold tsSrc at Hq
  icases Hq with (%Hne | ⟨%sv, %Hsv, Hc⟩)
  · exact False.elim (Hne ht)
  iexists sv
  isplitr
  · ipureintro; exact Hsv
  icases Hc with (Hc | ⟨Hc, %Hmem⟩)
  · ileft
    ihave %He := ApiImpl.nodeTabOk_agree γ n γn γp $$ Htab Htabp
    have Hkey : γn.sn.gsv = γp.sn.gsv := congrArg (fun k : ApiImpl.CfgNames => k.2.2.2.2.2.2.2.1) He
    iunfold svCert at Hc
    icases Hc with ⟨%P, #Hp, #HP⟩
    ihave #Hp' : savedPredOwn γp.sn.gsv DFrac.discard P $$ []
    · rw [← Hkey]; iexact Hp
    ihave #Heq := saved_pred_agree γp.sn.gsv DFrac.discard DFrac.discard P SV sv $$ Hp' Hpin
    inext
    ihave ⟨Hiff, -⟩ := internalEq_iff _ _ $$ Heq
    iapply Hiff $$ HP
  · iright
    isplitr
    rotate_left
    · unfold nodeRestoreSource
      iunfold restoredSnapHistory at Hhist
      ihave #Horigin := Hhist $$ %_ %Hmem
      rw [show snapId sv = (snapTrip sv sv.Metadata'.ConfState'.lists).sid from rfl]
      iexact Horigin
    unfold nodeRestoreCert
    iexists γn
    iframe Htab Hc


/-- Storage snapshots carry their client's tag. A restored snapshot is bounded by
the log delivered in any Ready from this incarnation at the original send term,
including when a later Ready finally drains the message. -/
theorem readySnapSources_le (γ : Cluster) (n : NodeH) (id term handoutTerm : w64)
    (ms observed : List QMsg) (bound observedBound : Nat) (q : QMsg) (SV : SnapshotM → IProp GF)
    (hq : q ∈ ms) (ht : q.st.msg.Type' = MsgSnap) (he : term = handoutTerm ∨ term = q.st.msg.Term')
    (sourceInstall observedInstall : Option w64 := none) :
    ⊢ readySnapSources (GF := GF) γ n id handoutTerm ms bound sourceInstall -∗
      readySnapSources γ n id term observed observedBound observedInstall -∗ snapshotLeader γ id term -∗
      nodeTagPin γ n SV -∗ ∃ sv : SnapshotM, ⌜q.st.snap = some sv⌝ ∗
        (▷ SV sv ∨ ⌜uint.nat sv.Metadata'.Index' ≤ observedBound⌝) := by
  haveI (γn : NodeNames) := ApiImpl.nodeTabOk_persistent (GF := GF) γ n γn
  unfold readySnapSources ApiImpl.snapSources nodeTagPin snapshotLeader
  iintro ⟨%γn, #Htab, -, #Hs⟩ ⟨%γo, #Htabo, -, #Ho⟩ #Hlead ⟨%γp, #Htabp, #Hpin⟩
  iunfold handoutOrigins at Hs
  icases Hs with ⟨%ks, -, -, #Hknown, #Hqueued, #Hqs, -⟩
  iunfold qSrcs at Hqs
  ihave ⟨#Hq, -⟩ := BigSepL.bigSepL_mem_acc hq $$ Hqs
  iunfold qSrc at Hq
  iunfold tsSrc at Hq
  icases Hq with (%Hne | ⟨%sv, %Hsv, Hc⟩)
  · exact False.elim (Hne ht)
  iexists sv
  isplitr
  · ipureintro; exact Hsv
  icases Hc with (Hc | ⟨-, %Hmem⟩)
  · ileft
    ihave %He := ApiImpl.nodeTabOk_agree γ n γn γp $$ Htab Htabp
    have Hkey : γn.sn.gsv = γp.sn.gsv := congrArg (fun k : ApiImpl.CfgNames => k.2.2.2.2.2.2.2.1) He
    iunfold svCert at Hc
    icases Hc with ⟨%P, #Hp, #HP⟩
    ihave #Hp' : savedPredOwn γp.sn.gsv DFrac.discard P $$ []
    · rw [← Hkey]; iexact Hp
    ihave #Heq := saved_pred_agree γp.sn.gsv DFrac.discard DFrac.discard P SV sv $$ Hp' Hpin
    inext
    ihave ⟨Hiff, -⟩ := internalEq_iff _ _ $$ Heq
    iapply Hiff $$ HP
  · iright
    ihave #Hsend : restoreAtSend γ.raft id γn.sn (snapTrip sv sv.Metadata'.ConfState'.lists) term $$ []
    · rcases he with rfl | rfl
      · iapply Hknown $$ %_ %Hmem
      · iapply Hqueued $$ %q %hq %sv %(And.intro ht Hsv) %_ %(And.intro Hmem rfl)
    iunfold handoutOrigins at Ho
    icases Ho with ⟨%obs, %hbound, #Hmark, -, -⟩
    ihave %He := ApiImpl.nodeTabOk_agree γ n γn γo $$ Htab Htabo
    have hkey : γn.sn.history = γo.sn.history :=
      congrArg (fun k : ApiImpl.CfgNames => k.2.2.2.2.2.2.2.2.2.2.2.2.2.1) He
    ihave #HmarkN : snapHistoryMark γn.sn (uint.nat term) (maxRestored obs) $$ []
    · rw [show snapHistoryMark (GF := GF) γn.sn (uint.nat term) (maxRestored obs) =
          snapHistoryMark γo.sn (uint.nat term) (maxRestored obs) by unfold snapHistoryMark; rw [hkey]]
      iexact Hmark
    ihave %hindex := restoredSend_index_le γ.raft id term γn.sn _ (maxRestored obs) $$ Hsend Hlead HmarkN
    ipureintro; exact Nat.le_trans hindex hbound


theorem readySnapSources_sameTerm_le (γ : Cluster) (n : NodeH) (id term : w64)
    (ms observed : List QMsg) (bound observedBound : Nat) (q : QMsg) (SV : SnapshotM → IProp GF)
    (hq : q ∈ ms) (ht : q.st.msg.Type' = MsgSnap) :
    ⊢ readySnapSources (GF := GF) γ n id term ms bound -∗
      readySnapSources γ n id term observed observedBound -∗ snapshotLeader γ id term -∗
      nodeTagPin γ n SV -∗ ∃ sv : SnapshotM, ⌜q.st.snap = some sv⌝ ∗
        (▷ SV sv ∨ ⌜uint.nat sv.Metadata'.Index' ≤ observedBound⌝) :=
  readySnapSources_le γ n id term term ms observed bound observedBound q SV hq ht (.inl rfl)

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
/-- A snapshot actually handed out for installation on this node incarnation. -/
@[no_expose] def nodeInstalledIndex (γ : Cluster) (n : NodeH) (i : w64) : IProp GF :=
  iprop(∃ γn : NodeNames, ApiImpl.nodeTabOk γ n γn ∗ installSeen γn.sn.installs (uint.nat i))

instance (γ : Cluster) (n : NodeH) (i : w64) : Persistent (nodeInstalledIndex (GF := GF) γ n i) := by
  unfold nodeInstalledIndex
  haveI (γn : NodeNames) := ApiImpl.nodeTabOk_persistent (GF := GF) γ n γn
  infer_instance

end api

section apiHeap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem readySnapSources_installed (γ : Cluster) (n : NodeH) (id term i : w64) (ms : List QMsg)
    (bound : Nat) : readySnapSources (GF := GF) γ n id term ms bound (some i) ⊢ nodeInstalledIndex γ n i := by
  unfold readySnapSources ApiImpl.snapSources nodeInstalledIndex
  iintro ⟨%gn, Htab, -, Hobs⟩
  iunfold handoutOrigins at Hobs
  icases Hobs with ⟨%ks, -, -, -, -, -, Hseen, -⟩
  iexists gn; iframe Htab
  iapply Hseen $$ %i %rfl

/-- (2026-11-24, the lifetime law: `notes/etcd-dist-d6.md`, T4 round 5) **A `Ready`'s `MsgSnap`s are
past the node's start term** (`nodeStartTerm`, `RestartNode`'s): each was sent in this run of the
node, by it as the leader of a term it won after the restart (raft's `LifeOk`: the term never goes
below the stored one, a campaign moves past it, only a leader queues a `MsgSnap`, at its term). So a
client tells this run's `MsgSnap`s from an earlier run's, whose `sentMsg` facts persist. -/
theorem readySnapSources_startTerm (γ : Cluster) (n : NodeH) (id term : w64) (ms : List QMsg)
    (bound : Nat) (installed : Option w64) (T0 : w64) :
    readySnapSources (GF := GF) γ n id term ms bound installed ∗ nodeStartTerm n T0 ⊢
      ⌜∀ q ∈ ms, q.st.msg.Type' = MsgSnap → uint.Z T0 < uint.Z q.st.msg.Term'⌝ := by
  unfold readySnapSources ApiImpl.snapSources ApiImpl.nodeTabOk nodeStartTerm
  iintro ⟨⟨%gn, %Htab, -, Hobs⟩, %Ht0⟩
  iunfold handoutOrigins at Hobs
  icases Hobs with ⟨%ks, -, -, -, -, -, -, -, %Hlife⟩
  ipureintro
  intro q hq ht
  subst Htab
  rw [← Ht0]
  exact Hlife q hq ht

/-- A snapshot read back from storage can use the restore certificate issued
when the driver installed it. The outbox's original send term suffices even
when storage and apply are processing different Ready batches. -/
theorem readySnapSources_installed_le (γ : Cluster) (n : NodeH) (id handoutTerm : w64)
    (ms observed : List QMsg) (bound observedBound : Nat) (sourceInstall observedInstall : Option w64)
    (q : QMsg) (sv : SnapshotM) (hq : q ∈ ms) (ht : q.st.msg.Type' = MsgSnap) (hsv : q.st.snap = some sv) :
    ⊢ readySnapSources (GF := GF) γ n id handoutTerm ms bound sourceInstall -∗
      readySnapSources γ n id q.st.msg.Term' observed observedBound observedInstall -∗
      snapshotLeader γ id q.st.msg.Term' -∗ nodeInstalledIndex γ n sv.Metadata'.Index' -∗
      ⌜uint.nat sv.Metadata'.Index' ≤ observedBound⌝ := by
  haveI (gn : NodeNames) := ApiImpl.nodeTabOk_persistent (GF := GF) γ n gn
  unfold readySnapSources ApiImpl.snapSources snapshotLeader nodeInstalledIndex
  iintro ⟨%gn, #Htab, -, #Hs⟩ ⟨%go_, #Htabo, -, #Ho⟩ #Hlead ⟨%gi, #Htabi, #Hi⟩
  iunfold handoutOrigins at Hs Ho
  icases Hs with ⟨%ks, -, -, -, #Hqueued, -, -, #Hknown, -⟩
  icases Ho with ⟨%obs, %hbound, #Hmark, -⟩
  ihave %Hei := ApiImpl.nodeTabOk_agree γ n gn gi $$ Htab Htabi
  have iki : gn.sn.installs = gi.sn.installs :=
    congrArg (fun k : ApiImpl.CfgNames => k.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) Hei
  ihave #Hi' : installSeen gn.sn.installs (uint.nat sv.Metadata'.Index') $$ []
  · rw [iki]; iexact Hi
  icases Hknown $$ %q %hq %sv %(And.intro ht hsv) Hi' with ⟨%k, %hk⟩
  ihave #Hsend := Hqueued $$ %q %hq %sv %(And.intro ht hsv) %k %hk
  ihave %He := ApiImpl.nodeTabOk_agree γ n gn go_ $$ Htab Htabo
  have hkey : gn.sn.history = go_.sn.history :=
    congrArg (fun k : ApiImpl.CfgNames => k.2.2.2.2.2.2.2.2.2.2.2.2.2.1) He
  ihave #Hmark' : snapHistoryMark gn.sn (uint.nat q.st.msg.Term') (maxRestored obs) $$ []
  · rw [show snapHistoryMark (GF := GF) gn.sn (uint.nat q.st.msg.Term') (maxRestored obs) =
        snapHistoryMark go_.sn (uint.nat q.st.msg.Term') (maxRestored obs) by unfold snapHistoryMark; rw [hkey]]
    iexact Hmark
  ihave %hi := restoredSend_index_le γ.raft id q.st.msg.Term' gn.sn k (maxRestored obs) $$ Hsend Hlead Hmark'
  ipureintro; rw [← hk.2]; exact Nat.le_trans hi hbound

/-- A storage whose nonempty snapshots also carry the client's source tag. -/
def isStorageT (γ : Cluster) (K : GName) (Tg : SnapshotM → IProp GF) (st : Storage) : IProp GF :=
  isStorageP γ.maxData.isSome (fun sv => iprop(snapshotValid γ sv ∗ Tg sv))
    (storBnd γ K) (nodeCommitLb γ K) st

theorem isStorageT_forget (γ : Cluster) (K : GName) (Tg : SnapshotM → IProp GF) (st : Storage) :
    isStorageT γ K Tg st ⊢ isStorage γ K st := by
  apply isStorageP_mono_SV
  intro sv
  iintro ⟨H, -⟩
  iexact H

theorem isStorage_tagTrue (γ : Cluster) (K : GName) (st : Storage) :
    isStorage (GF := GF) γ K st ⊢ isStorageT γ K (fun _ => iprop(True)) st := by
  apply isStorageP_mono_SV
  intro sv
  iintro H
  iframe H

/-- (2026-11-01, durability stage I-4) **The storage `st` holds the contents `σ`**, as the storage
contract states its log: compacted at the base, the base's entry (of the base's term) frozen, the
entries above it owned, the end after them. What a restarted node's view of its storage starts
from (until then `bootStorage`'s at the empty log). -/
def storHolds (st : Storage) (σ : StorContents) (f : Nat) : IProp GF :=
  iprop(∃ e0 : EntryM, ⌜e0.Term' = σ.base.term'⌝ ∗ storCompacted st σ.b ∗
    storLog st σ.b DFrac.discard [e0] ∗
    -- (2026-11-01, durability stage II (k), the freeze point) the entries up to `f` frozen
    storLog st (σ.b + 1) DFrac.discard (σ.ents.take (f - σ.b)) ∗
    storLog st (f + 1) (DFrac.own 1) (σ.ents.drop (f - σ.b)) ∗
    storEnd st (σ.last + 1))

/-- (2026-11-01, durability stage I-4; candidate 12 §4, generalizing `bootStorage`) **A storage `st`
to start a node from, holding `σ`**: a frame `R` of the client's, with `FirstIndex` answering
`σ.b + 1` and `LastIndex` `σ.last` over it, and `InitialState` answering `σ`'s hard state and the
conf state `csm`, after which -- given the fresh key `K` raft names the storage by, and raft's
bounds at the attach (compacting up to the applied index it starts at, `max σ.b A`, is safe; it
committed up to the stored commit) -- the client makes the storage contract (`isStorage γ K st`)
and gives the storage's log (`storHolds`; (2026-11-01, durability stage II (k)) the entries up to a
freeze point `f` of the client's choice, `σ.b ≤ f ≤ σ.commit`, frozen, the rest owned), keeping its
frame `F K`, which `RestartNode`'s post returns
at the driver's key. (2026-11-01, stage-I fix G1-frame: the frame depends on the key, so that a
client allocating its storage's invariant at `K` in the continuation has it at the driver's key.)
`newRaft` reads `FirstIndex` and `LastIndex` (`newLogWithSize`) *before* `InitialState`, and a
`MemoryStorage`'s `InitialState` reads its snapshot without the lock
(`issues/raft-memorystorage-initialstate-unlocked.md`), so its invariant (`memStorInv`) can only be
made once `InitialState` returned: the contract comes in `InitialState`'s post. Each attach has its
key, so a key's bounds are one node's. -/
def restartStorage (γ : Cluster) (st : Storage) (σ : StorContents) (csm : ConfStateM) (A : Nat)
    (F : GName → IProp GF) (SV : SnapshotM → IProp GF := snapshotValid γ) : IProp GF :=
  iprop(∃ (i : GoInterfaceOk) (R : IProp GF) (f : Nat), ⌜st = interface.ok i⌝ ∗
    -- (2026-11-01, durability stage II (k)) the freeze point: the stored entries up to `f`, committed,
    -- frozen (`storHolds`), so that the client may have made a snapshot among them before the attach
    ⌜σ.b ≤ f ∧ f ≤ σ.commit⌝ ∗ R ∗
    ({{ R }} (App (Val #(methods i.ty go!"FirstIndex" i.v)) (Val #()))
       {{ RET (PairV #(W64 (σ.b + 1)) #interface.nil); R }}) ∗
    ({{ R }} (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #()))
       {{ RET (PairV #(W64 σ.last) #interface.nil); R }}) ∗
    ({{ R }} (App (Val #(methods i.ty go!"InitialState" i.v)) (Val #()))
       {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
          hsOpt hp σ.hs ∗ csPts cs DFrac.discard csm al ∗
          ∀ K : GName, nodeAppliedLb γ K (max σ.b A) -∗ nodeCommitLb γ K σ.commit -∗
            |={⊤}=> isStorage γ K st SV ∗ storHolds st σ f ∗ F K }}))

end apiHeap

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
/-- (raft-final, 2026-10-29, U8: the WIP's `snapshotCert_valid`) **A certified snapshot is valid**:
a `Ready`'s snapshot (`readySnap`'s certificate, its index past `0` and below `2^61`) is what
`MemoryStorage.ApplySnapshot` and the storage contract take (`snapshotValid`). -/
theorem snapshotCert_valid (γ : Cluster) (N : Namespace) (sv : SnapshotM) :
    0 < uint.Z sv.Metadata'.Index' → uint.Z sv.Metadata'.Index' < 2 ^ 61 →
    isCluster (GF := GF) γ N ∗ snapshotCert γ N (snapTrip sv sv.Metadata'.ConfState'.lists) ⊢
      snapshotValid γ sv := by
  intro Hpos H61
  iintro ⟨#Hc, #Hk⟩
  ihave ⟨%l, %m, #Hlb, #Ha, #Hm, %Hf⟩ := snapshotCert_made γ N _ $$ [Hc Hk]
  · iframe Hc Hk
  -- the lists' bound, from the certificate's `snapAtOk` (the registry on: `UniNames`)
  ihave %Hsl : ⌜SnapListsOk (snapTrip sv sv.Metadata'.ConfState'.lists)⌝ $$ []
  · iunfold isCluster at Hc
    iunfold ApiImpl.isClusterU at Hc
    icases Hc with ⟨%HU, -, -⟩
    obtain ⟨⟨c0, g, ⟨⟨_, _, _, _, Hreg, _⟩, _⟩⟩, _⟩ := HU
    iunfold snapshotCert at Hk
    iunfold ApiImpl.snapshotCert at Hk
    icases Hk with ⟨#Hrc, -⟩
    iunfold raftSnapCert at Hrc
    icases Hrc with ⟨-, -, -, #Hat⟩
    iunfold snapAtOk at Hat
    icases Hat with (%Hn | ⟨%L, %M, -, -, %Hp⟩)
    · exact absurd Hn Hreg
    ipureintro; exact Hp.2.2.1
  obtain ⟨Hlen, Hlast, ⟨h1, h2, h3, h4⟩, hal⟩ := Hf
  unfold snapshotValid
  iexists l, m
  isplitr; · iexact Hlb
  isplitr; · iexact Ha
  isplitr
  · iExactEq Hm; rfl
  ipureintro
  have u := uint_nat_eq sv.Metadata'.Index'
  have Hlen' : l.length = uint.nat sv.Metadata'.Index' := Hlen
  refine ⟨Hlen', by omega, Hlast, ⟨h1, h2, h3, h4, hal⟩, by omega, ?_⟩
  exact Hsl.2.2.2.2.2.1

end api

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- (2026-11-22, ledger `RestartNode`) **A plain restart update is one with the crash token**:
`RestartNode`'s update is given the generation's `notCrashed` and gives it back; a client that
does not need it passes it through. -/
theorem restartAu_nc (γ : Cluster) (N : Namespace) (id : w64) (σ : StorContents)
    (Q : RaftState → IProp GF) :
    iprop(AU <{ ∃∃ (S : RaftState), ▷ raftState γ id S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ \ ↑N, ∅
      <{ raftState γ id S, COMM Q S }>) ⊢
    iprop(notCrashed -∗
      AU <{ ∃∃ (S : RaftState), ▷ raftState γ id S ∗ ⌜StorageHolds S σ⌝ }> @ ⊤ \ ↑N, ∅
        <{ raftState γ id S, COMM notCrashed ∗ Q S }>) := by
  iintro HAU Hnc
  iapply aupd_wand_post
  iframe HAU
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iintro %_ HQ
  iframe

end api


end EtcdGrove
end Perennial
