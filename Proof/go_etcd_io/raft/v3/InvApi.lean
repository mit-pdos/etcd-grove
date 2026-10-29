/-
# Raft's node API over an abstract log: the implementation (2026-10-27)

The definitions behind the node API (`InvNode.lean`; until 2026-10-28 `NodeApiImpl.lean`, behind `NodeApiDraft.lean`) and the proofs of
its laws and specs (`*_impl`), from raft's internals. Once done, the draft's `sorry` bodies are
replaced by these (`notes/decisions.md`, "Raft's node API over an abstract log").

**The ghost state** (`Cluster`): raft's names (`raft`, the commit invariant's namespace
`N .@ "raft"`) and the adapter's own:
- `full`, a monotone list of `LogEntry`: the full committed log (fillers included), its authority
  in the adapter's invariant (`apiInv`), its lower bounds the client's (`isCommittedLogLb`);
- `ops`, a monotone list of `LogEntry`: the committed requested entries (`opsOf`), its authority
  halved between `apiInv` and the client (`ownCommittedOps`);
- `ctxs`, a ghost map `c ↦ (γq, l0)` (persistent elements) of the read contexts the client
  committed, `γq` naming the context's predicate, `l0` a log committed before (2026-10-27:
  `readCtxAfter`); the client holds the authority (`ownReadCtxs`).

The adapter's invariant `apiInv γ N` (at `N .@ "api"`, disjoint from raft's `N .@ "raft"`) holds the
client half of raft's committed log (`rLog`), the authority of `full` at it (as `LogEntry`s) and
half of `ops` at its requested entries, and the client side of raft's registries.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context
public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Perennial.Ghost.MonoList
public import Proof.go_etcd_io.raft.v3.NodeApiVocab
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.ApiVocab
import all Proof.go_etcd_io.raft.v3.InvNodeChan

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The abstract state (as in the draft) -/

section pure
variable [GooseExts]

instance LogEntry_countable : Pos.Countable LogEntry :=
  countableOfLeftInverse (fun e : LogEntry => (e.term, e.type, e.data))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

theorem opsOf_append (a b : List LogEntry) : opsOf (a ++ b) = opsOf a ++ opsOf b := by
  unfold opsOf; exact List.filter_append _ _

theorem opsOf_prefix {a b : List LogEntry} (h : a <+: b) : opsOf a <+: opsOf b := by
  obtain ⟨r, rfl⟩ := h
  rw [opsOf_append]
  exact List.prefix_append _ _

theorem opsOf_snoc_filler (l : List LogEntry) (e : LogEntry) (h : e.isFiller ∨ e.isEmptyV2) :
    opsOf (l ++ [e]) = opsOf l := by
  rw [opsOf_append]
  rcases h with h | h <;> simp [opsOf, h]

theorem opsOf_snoc_op (l : List LogEntry) (e : LogEntry) (h : ¬ (e.isFiller ∨ e.isEmptyV2)) :
    opsOf (l ++ [e]) = opsOf l ++ [e] := by
  rw [opsOf_append]
  simp only [not_or] at h
  simp [opsOf, h.1, h.2]

theorem strip_append (a b : List EntryM) : strip (a ++ b) = strip a ++ strip b := by
  unfold strip; exact List.map_append

theorem strip_prefix {a b : List EntryM} (h : a <+: b) : strip a <+: strip b := by
  obtain ⟨r, rfl⟩ := h
  rw [strip_append]
  exact List.prefix_append _ _

theorem strip_length (a : List EntryM) : (strip a).length = a.length := by
  unfold strip; exact List.length_map _

/-- A filler as raft sees it (`Filler`) is one or an empty `ConfChangeV2` as the client does. -/
theorem isFiller_ofEntryM (e : EntryM) :
    ((LogEntry.ofEntryM e).isFiller ∨ (LogEntry.ofEntryM e).isEmptyV2) ↔ Filler e.Type' e.Data' := by
  unfold LogEntry.isFiller LogEntry.isEmptyV2 Filler LogEntry.ofEntryM
  simp only
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, .inl h2⟩
    · exact ⟨h1, .inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨h1, h2⟩

end pure

/-! ## The cluster's ghost names -/

/-- A cluster's ghost names (see the file header). -/
structure Cluster where
  raft : RaftNames
  full : GName
  ops : GName
  ctxs : GName
  /-- the cluster's term budget (raft's `BudgetNames`) -/
  bud : BudgetNames
  /-- the trivial result predicate the adapter registers its proposals with -/
  trueQ : GName
  /-- (2026-10-27) the nodes' mode (static, or dynamic with its decoder and initial configuration),
  at every `GooseExts` instance (`RNMode.all`), as `RaftNames.reDyn` -/
  mode : (e : GooseExts) → @RNMode e
  /-- (2026-10-27) a dynamic cluster's table of its nodes' configuration names: node `id`'s ghost
  map, whose one persistent entry names its `NodeNames`' `dlm`, `cap`, `ccq` and `cam`
  (`nodeTabOk`), so that the node's predicates (`nodeDriver`, `nodeConfig`, `deliveredLogLb`)
  agree on them -/
  nodeTab : GMap w64 GName

/-- A mode at every `GooseExts` instance: `m` at the current one (as `DynCfg.all`). -/
def _root_.Perennial.EtcdGrove.RNMode.all [ext : GooseExts] (m : RNMode) : (e : GooseExts) → @RNMode e := by
  classical
  exact fun e => if h : e = ext then h ▸ m else @RNMode.static e

theorem _root_.Perennial.EtcdGrove.RNMode.all_self [ext : GooseExts] (m : RNMode) : m.all ext = m := by
  unfold RNMode.all; simp

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The client's views of the committed log, and their laws -/

/-- (2026-10-29, stage U5) **What raft told the client of the committed entries `L`**
(persistent): each entry's bytes decode as its type says (`CCDecodes`, from its `entDataIs`), and
each empty `ConfChangeV2` sits at a joint configuration of its prefix (`ev2At`, `noopAu`'s). -/
def cmtFacts (γ : Cluster) (L : List EntryM) : IProp GF :=
  iprop(⌜∀ e ∈ L, CCDecodes e.Type' e.Data'⌝ ∗
    □ ∀ (k : Nat) (e : EntryM), ⌜L[k]? = some e⌝ -∗ ev2At γ.raft (L.take k) e)

instance cmtFacts_persistent (γ : Cluster) (L : List EntryM) :
    Persistent (cmtFacts (GF := GF) γ L) := by
  unfold cmtFacts; infer_instance

instance cmtFacts_timeless (γ : Cluster) (L : List EntryM) :
    Timeless (cmtFacts (GF := GF) γ L) := by
  unfold cmtFacts; infer_instance

/-- ... of a client's view `l` of them. -/
def cmtFactsS (γ : Cluster) (l : List LogEntry) : IProp GF :=
  iprop(∃ L, ⌜strip L = l⌝ ∗ cmtFacts γ L)

instance cmtFactsS_persistent (γ : Cluster) (l : List LogEntry) :
    Persistent (cmtFactsS (GF := GF) γ l) := by
  unfold cmtFactsS; infer_instance

instance cmtFactsS_timeless (γ : Cluster) (l : List LogEntry) :
    Timeless (cmtFactsS (GF := GF) γ l) := by
  unfold cmtFactsS; infer_instance

omit [StorageModel GF] sem package_sem in
theorem cmtFacts_nil (γ : Cluster) : ⊢ cmtFacts (GF := GF) γ [] := by
  unfold cmtFacts
  isplitr; · ipureintro; intro e he; simp at he
  imodintro; iintro %k %e %h; simp at h

omit [StorageModel GF] sem package_sem in
theorem cmtFacts_take (γ : Cluster) (L : List EntryM) (n : Nat) :
    cmtFacts (GF := GF) γ L ⊢ cmtFacts γ (L.take n) := by
  unfold cmtFacts
  iintro ⟨%H1, #H2⟩
  isplitr; · ipureintro; intro e he; exact H1 e (List.mem_of_mem_take he)
  imodintro
  iintro %k %e %h
  rw [List.getElem?_take] at h
  split at h
  · rename_i hk
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    iapply H2 $$ %k %e %h
  · cases h

omit [StorageModel GF] sem package_sem in
theorem cmtFacts_snoc (γ : Cluster) (L : List EntryM) (e : EntryM) :
    CCDecodes e.Type' e.Data' →
    ⊢ cmtFacts (GF := GF) γ L -∗ ev2At γ.raft L e -∗ cmtFacts γ (L ++ [e]) := by
  intro Hd
  unfold cmtFacts
  iintro ⟨%H1, #H2⟩ #He
  isplitr
  · ipureintro; intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact H1 x hx
    · simp at hx; subst hx; exact Hd
  imodintro
  iintro %k %x %h
  by_cases hk : k < L.length
  · rw [List.getElem?_append_left hk] at h
    rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
    iapply H2 $$ %k %x %h
  · rw [List.getElem?_append_right (by omega)] at h
    have hk' : k = L.length := by
      have := (List.getElem?_eq_some_iff.mp h).1; simp at this; omega
    subst hk'
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.take_left]
    iexact He

omit [StorageModel GF] sem package_sem in
theorem cmtFactsS_prefix (γ : Cluster) (L : List EntryM) (l : List LogEntry) (H : l <+: strip L) :
    cmtFacts (GF := GF) γ L ⊢ cmtFactsS γ l := by
  iintro #H
  unfold cmtFactsS
  iexists L.take l.length
  isplitr
  · ipureintro
    obtain ⟨t, ht⟩ := H
    show (L.take l.length).map LogEntry.ofEntryM = l
    rw [List.map_take]
    show (strip L).take l.length = l
    rw [← ht, List.take_left]
  iapply cmtFacts_take γ L l.length $$ H

omit [StorageModel GF] sem package_sem in
/-- (2026-10-29, stage U5) A bootstrap log's facts: `ConfChange`s that decode. -/
theorem cmtFacts_bootOk (γ : Cluster) {ps : List w64} {L : List EntryM} (H : BootLogOk ps L) :
    ⊢ cmtFacts (GF := GF) γ L := by
  unfold cmtFacts
  isplitr
  · ipureintro; intro e he
    obtain ⟨k, hk⟩ := List.getElem?_of_mem he
    obtain ⟨-, -, ht, m, hm, -⟩ := H.2.2 k e hk
    exact ⟨fun _ => ⟨_, hm⟩, fun h2 => by rw [ht] at h2; revert h2; word⟩
  imodintro
  iintro %k %e %hk
  unfold ev2At
  iintro %Hc
  exfalso
  obtain ⟨-, -, ht, -⟩ := H.2.2 k e hk
  have := Hc.2.2.2; rw [ht] at this; revert this; word

/-- **A lower bound of the committed log**, fillers included (persistent): `l` is empty, or a
prefix of the full log (`full`) whose requested entries are a prefix of the requested entries
(`ops`), shorter than the receipts' bound past the bootstrap log (2026-10-27: every committed
entry's index is covered by a time receipt, `isEntryR_receipt`), with what raft told of its
entries (2026-10-29, stage U5: `cmtFactsS`). -/
def isCommittedLogLb (γ : Cluster) (l : List LogEntry) : IProp GF :=
  iprop(⌜l = []⌝ ∨ (monoListLbOwn γ.full l ∗ monoListLbOwn γ.ops (opsOf l) ∗
    ⌜(l.length : Int) < (receiptBound GF : Int) + γ.raft.reBoot.length⌝ ∗ cmtFactsS γ l))

/-- **The committed requested entries, the client's** (exclusive): half of `ops`' authority, and
a committed log whose requested entries they are. -/
def ownCommittedOps (γ : Cluster) (ops : List LogEntry) : IProp GF :=
  iprop(monoListAuthOwn γ.ops (1 : Qp).half ops ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf l = ops⌝)

instance isCommittedLogLb_persistent (γ : Cluster) (l : List LogEntry) :
    Persistent (isCommittedLogLb (GF := GF) γ l) := by
  unfold isCommittedLogLb; infer_instance

instance isCommittedLogLb_timeless (γ : Cluster) (l : List LogEntry) :
    Timeless (isCommittedLogLb (GF := GF) γ l) := by
  unfold isCommittedLogLb; infer_instance

instance ownCommittedOps_timeless (γ : Cluster) (ops : List LogEntry) :
    Timeless (ownCommittedOps (GF := GF) γ ops) := by
  unfold ownCommittedOps; infer_instance

omit [StorageModel GF] sem package_sem in
theorem ownCommittedOps_get_lb_impl (γ : Cluster) (ops : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ⊢
      ownCommittedOps γ ops ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf l = ops⌝ := by
  unfold ownCommittedOps
  iintro ⟨Ha, %l, #Hl, %Hops⟩
  iframe Ha
  isplitl []
  · iexists l; iframe Hl; ipureintro; exact Hops
  · iexists l; iframe Hl; ipureintro; exact Hops

omit [StorageModel GF] sem package_sem in
theorem ownCommittedOps_lb_prefix_impl (γ : Cluster) (ops l : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ∗ isCommittedLogLb γ l ⊢ ⌜opsOf l <+: ops⌝ := by
  unfold ownCommittedOps isCommittedLogLb
  iintro ⟨⟨Ha, -⟩, (%Hnil | ⟨-, #Hlb, -⟩)⟩
  · ipureintro; subst Hnil; exact List.nil_prefix
  icases mono_list_auth_lb_valid $$ Ha Hlb with %H
  ipureintro; exact H.2

omit [StorageModel GF] sem package_sem in
theorem isCommittedLogLb_nil_impl (γ : Cluster) : ⊢ isCommittedLogLb (GF := GF) γ [] := by
  unfold isCommittedLogLb
  ileft; ipureintro; rfl

omit [StorageModel GF] sem package_sem in
theorem isCommittedLogLb_mono_impl (γ : Cluster) (l1 l2 : List LogEntry) :
    l1 <+: l2 → isCommittedLogLb (GF := GF) γ l2 ⊢ isCommittedLogLb γ l1 := by
  intro Hp
  unfold isCommittedLogLb
  iintro (%Hnil | ⟨#H1, #H2, %Hb, #Hcf⟩)
  · ileft; ipureintro; subst Hnil; exact List.prefix_nil.mp Hp
  iright
  isplitl []
  · iapply monoListLbOwn_le _ Hp $$ H1
  isplitl []
  · iapply monoListLbOwn_le _ (opsOf_prefix Hp) $$ H2
  isplitl []
  · ipureintro; have := Hp.length_le; omega
  iunfold cmtFactsS at Hcf
  icases Hcf with ⟨%L, %HL, #Hc⟩
  iapply cmtFactsS_prefix γ L l1 (by rw [HL]; exact Hp) $$ Hc

omit [StorageModel GF] sem package_sem in
theorem isCommittedLogLb_agree_impl (γ : Cluster) (l1 l2 : List LogEntry) :
    isCommittedLogLb (GF := GF) γ l1 ∗ isCommittedLogLb γ l2 ⊢ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold isCommittedLogLb
  iintro ⟨(%H1 | ⟨#H1, -⟩), (%H2 | ⟨#H2, -⟩)⟩
  · ipureintro; subst H1; exact .inl List.nil_prefix
  · ipureintro; subst H1; exact .inl List.nil_prefix
  · ipureintro; subst H2; exact .inr List.nil_prefix
  iapply mono_list_lb_valid $$ H1 H2

end api

/-! ## The adapter's invariant -/

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The adapter's invariant's namespace, beside raft's (`N .@ "raft"`). -/
def apiN (N : Namespace) : Namespace := N .@ "api"

theorem apiN_sub_raft (N : Namespace) : (↑(apiN N) : CoPset) ⊆ ⊤ \ ↑(N .@ "raft") :=
  mask_ndot_ne' N "api" "raft" (by decide)

theorem mask_api_raft (N : Namespace) :
    (⊤ \ ↑N : CoPset) ⊆ (⊤ \ ↑(N .@ "raft")) \ ↑(apiN N) :=
  mask_diff_ndot2 N "raft" "api"

theorem apiN_sub (N : Namespace) {E : CoPset} (HE : ↑N ⊆ E) : (↑(apiN N) : CoPset) ⊆ E :=
  fun p hp => HE p (nclose_subseteq N "api" p hp)

theorem raftN_sub (N : Namespace) {E : CoPset} (HE : ↑N ⊆ E) :
    (↑(N .@ "raft") : CoPset) ⊆ E :=
  fun p hp => HE p (nclose_subseteq N "raft" p hp)

/-- A read context's result predicate, as raft's read records it: the context's predicate `Q` of
the requested entries of the log. -/
def qrOf (Q : List LogEntry → IProp GF) (L : List EntryM) : IProp GF := Q (opsOf (strip L))

/-- **A read context deposited in raft** (the part under a later): committed (`γ.ctxs`) to the
predicate `Q` (named `γq`), its read deposited with the result predicate `qrOf Q`. -/
def readDep (γ : Cluster) (c : List w8) : IProp GF :=
  iprop(∃ (γq : GName) (l0 : List LogEntry) (Q : List LogEntry → IProp GF),
    c ↪[γ.ctxs]□ ((γq, l0) : GName × List LogEntry) ∗
    savedPredOwn γq DFrac.discard Q ∗ isRead γ.raft c (qrOf Q))

instance readDep_persistent (γ : Cluster) (c : List w8) : Persistent (readDep (GF := GF) γ c) := by
  unfold readDep; infer_instance

/-- **A read context deposited in raft** (timeless): its entry in `γ.ctxs` and raft's record,
deposited at a committed log at least as long as the one the context was committed after. -/
def readKey (γ : Cluster) (c : List w8) : IProp GF :=
  iprop(∃ (γq : GName) (l0 : List LogEntry) (Lc : List EntryM),
    c ↪[γ.ctxs]□ ((γq, l0) : GName × List LogEntry) ∗ readReq γ.raft c Lc ∗
    ⌜l0.length ≤ Lc.length⌝)

instance readKey_persistent (γ : Cluster) (c : List w8) : Persistent (readKey (GF := GF) γ c) := by
  unfold readKey; infer_instance

instance readKey_timeless (γ : Cluster) (c : List w8) : Timeless (readKey (GF := GF) γ c) := by
  unfold readKey readReq; infer_instance

/-- The entries of a committed log are at their positions. -/
def IdxOk (L : List EntryM) : Prop :=
  ∀ (k : Nat) (e : EntryM), L[k]? = some e → uint.Z e.Index' = (k : Int) + 1

theorem IdxOk_snoc {L : List EntryM} {e : EntryM} (H : IdxOk L)
    (He : uint.Z e.Index' = (L.length : Int) + 1) : IdxOk (L ++ [e]) := by
  intro k e' Hk
  by_cases hk : k < L.length
  · rw [List.getElem?_append_left hk] at Hk; exact H k e' Hk
  · have hk' : k = L.length := by
      have := (List.getElem?_eq_some_iff.mp Hk).1; simp at this; omega
    subst hk'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at Hk
    simp at Hk; subst Hk; exact He

/-- The keys the adapter registered (and the boot entries'), each with the trivial predicate. -/
def freshOk (γ : Cluster) (F : GMap (List w8) Unit) : IProp GF :=
  iprop(□ ∀ k : List w8, ⌜F !! k = some ()⌝ -∗ propIsAt γ.raft k γ.trueQ)

instance freshOk_persistent (γ : Cluster) (F : GMap (List w8) Unit) :
    Persistent (freshOk (GF := GF) γ F) := by
  unfold freshOk; infer_instance

instance freshOk_timeless (γ : Cluster) (F : GMap (List w8) Unit) :
    Timeless (freshOk (GF := GF) γ F) := by
  unfold freshOk; infer_instance

/-- The read contexts the adapter deposited in raft. -/
def rdFreshOk (γ : Cluster) (RF : GMap (List w8) Unit) : IProp GF :=
  iprop(□ ∀ c : List w8, ⌜RF !! c = some ()⌝ -∗ readDep γ c)

/-- ... their timeless part. -/
def rdKeys (γ : Cluster) (RF : GMap (List w8) Unit) : IProp GF :=
  iprop(□ ∀ c : List w8, ⌜RF !! c = some ()⌝ -∗ readKey γ c)

instance rdKeys_persistent (γ : Cluster) (RF : GMap (List w8) Unit) :
    Persistent (rdKeys (GF := GF) γ RF) := by
  unfold rdKeys; infer_instance

instance rdKeys_timeless (γ : Cluster) (RF : GMap (List w8) Unit) :
    Timeless (rdKeys (GF := GF) γ RF) := by
  unfold rdKeys; infer_instance

instance rdFreshOk_persistent (γ : Cluster) (RF : GMap (List w8) Unit) :
    Persistent (rdFreshOk (GF := GF) γ RF) := by
  unfold rdFreshOk; infer_instance

/-- **The adapter's invariant** (see the file header). -/
def apiInvBody (γ : Cluster) : IProp GF :=
  iprop(∃ (L : List EntryM) (F RF : GMap (List w8) Unit),
    rLog γ.raft L ∗ ⌜IdxOk L ∧ (L.length : Int) < (receiptBound GF : Int) + γ.raft.reBoot.length⌝ ∗
    monoListAuthOwn γ.full 1 (strip L) ∗ monoListAuthOwn γ.ops (1 : Qp).half (opsOf (strip L)) ∗
    ghostMapAuth γ.raft.reFresh 1 F ∗ freshOk γ F ∗ cmtFacts γ L ∗
    ghostMapAuth γ.raft.reRdFresh 1 RF ∗ rdKeys γ RF ∗ rdFreshOk γ RF)

def apiInv (γ : Cluster) (N : Namespace) : IProp GF := inv (apiN N) (apiInvBody γ)

instance apiInv_persistent (γ : Cluster) (N : Namespace) : Persistent (apiInv (GF := GF) γ N) := by
  unfold apiInv; infer_instance

/-- **The cluster's invariants**: raft's, in `N .@ "raft"`, and the adapter's. -/
def clusterInv (γ : Cluster) (N : Namespace) : IProp GF :=
  iprop(⌜γ.raft.reNs = N .@ "raft"⌝ ∗ raftCommitInv γ.raft ∗ apiInv γ N ∗
    savedPredOwn γ.trueQ DFrac.discard (fun _ : List EntryM => iprop(True : IProp GF)))

instance clusterInv_persistent (γ : Cluster) (N : Namespace) :
    Persistent (clusterInv (GF := GF) γ N) := by
  unfold clusterInv; infer_instance

/-! ### Raft's standing update, from the adapter's invariant -/

/-- **The standing update for the fillers**: the full log grows by the filler, the requested
entries do not. -/
theorem api_noopAu (γ : Cluster) (N : Namespace) (HN : γ.raft.reNs = N .@ "raft") :
    ⊢ apiInv (GF := GF) γ N -∗ noopAu γ.raft := by
  iintro #Hinv
  unfold noopAu
  imodintro
  iauintro
  unfold atomic_acc apiInv apiInvBody
  have Hsub : (↑(apiN N) : CoPset) ⊆ ⊤ \ ↑(raftN γ.raft) := by
    unfold raftN; rw [HN]; exact apiN_sub_raft N
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑(raftN γ.raft)) \ ↑(apiN N) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists L
  iframe HrL
  isplit
  · iintro HrL
    imod Hclose2 with -
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iempintro
  · iintro %e ⟨HrL, #He, #Hev, %HeIdx⟩
    imod Hclose2 with -
    iunfold entDataIs at He
    iunfold propDataIs at He
    icases He with %Hfill
    ihave #Hcf' := cmtFacts_snoc γ L e Hfill.2 $$ Hcf Hev
    have Hf : (LogEntry.ofEntryM e).isFiller ∨ (LogEntry.ofEntryM e).isEmptyV2 :=
      (isFiller_ofEntryM e).2 Hfill.1
    imod monoListAuthOwn_update_app [LogEntry.ofEntryM e] $$ Hfull with ⟨Hfull, -⟩
    have Hstrip : strip (L ++ [e]) = strip L ++ [LogEntry.ofEntryM e] := by
      rw [strip_append]; rfl
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L ++ [e], F, RF
      rw [Hstrip, opsOf_snoc_filler _ _ Hf]
      iframe HrL Hfull Hops HF HFok Hcf' HRF HRk HRFok
      ipureintro
      refine ⟨IdxOk_snoc Hidx.1 HeIdx.1, ?_⟩
      have := HeIdx.2; simp only [List.length_append, List.length_singleton]; push_cast; omega
    imodintro
    itrivial

end inv

/-! ## Read contexts -/

section ctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The read contexts, the client's**: the authority of `ctxs`, whose domain is `U`. -/
def ownReadCtxs (γ : Cluster) (U : GSet (List w8)) : IProp GF :=
  iprop(∃ M : GMap (List w8) (GName × List LogEntry), ghostMapAuth γ.ctxs 1 M ∗
    ⌜∀ c, c ∈ U ↔ c ∈ M⌝)

instance ownReadCtxs_timeless (γ : Cluster) (U : GSet (List w8)) :
    Timeless (ownReadCtxs (GF := GF) γ U) := by
  unfold ownReadCtxs; infer_instance

/-- The update a read context is committed with. -/
def ctxAu (γ : Cluster) (N : Namespace) (Q : List LogEntry → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
           <{ ownCommittedOps γ ops, COMM □ Q ops }>)

instance ctxAu_persistent (γ : Cluster) (N : Namespace) (Q : List LogEntry → IProp GF) :
    Persistent (ctxAu (GF := GF) γ N Q) := by
  unfold ctxAu; infer_instance

/-- **The read context `c` is committed to `Q`**: its entry in `ctxs`, naming `Q` and a log `l0`
committed before, and the update. -/
def isReadCtx (γ : Cluster) (N : Namespace) (c : List w8) (Q : List LogEntry → IProp GF) :
    IProp GF :=
  iprop(∃ (γq : GName) (l0 : List LogEntry), c ↪[γ.ctxs]□ ((γq, l0) : GName × List LogEntry) ∗
    savedPredOwn γq DFrac.discard Q ∗ ctxAu γ N Q ∗ isCommittedLogLb γ l0)

/-- **The context `c` was committed after the log `l0` was** (the draft's `readCtxAfter`). -/
def readCtxAfter (γ : Cluster) (_N : Namespace) (c : List w8) (l0 : List LogEntry) : IProp GF :=
  iprop(∃ γq : GName, c ↪[γ.ctxs]□ ((γq, l0) : GName × List LogEntry))

instance readCtxAfter_persistent (γ : Cluster) (N : Namespace) (c : List w8) (l0 : List LogEntry) :
    Persistent (readCtxAfter (GF := GF) γ N c l0) := by
  unfold readCtxAfter; infer_instance

instance isReadCtx_persistent (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) : Persistent (isReadCtx (GF := GF) γ N c Q) := by
  unfold isReadCtx; infer_instance

omit [StorageModel GF] sem package_sem in
theorem readCtx_commit_after_impl (γ : Cluster) (N : Namespace) (U : GSet (List w8))
    (c : List w8) (Q : List LogEntry → IProp GF) (l0 : List LogEntry) :
    c ∉ U →
    ownReadCtxs (GF := GF) γ U ∗ isCommittedLogLb γ l0 ∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
           <{ ownCommittedOps γ ops, COMM □ Q ops }> ⊢
    |==> (ownReadCtxs γ (insert c U) ∗ isReadCtx γ N c Q ∗ readCtxAfter γ N c l0) := by
  intro Hc
  unfold ownReadCtxs isReadCtx ctxAu readCtxAfter
  iintro ⟨⟨%M, HM, %HU⟩, #Hl0, #Hau⟩
  have HMc : M !! c = none := by
    have h : ¬ c ∈ M := fun h => Hc ((HU c).mpr h)
    cases hM : M !! c with
    | none => rfl
    | some v => exact absurd (show c ∈ M from by show (M.lookup c).isSome = true; rw [hM]; rfl) h
  imod saved_pred_alloc Q DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod ghost_map_insert_persist c ((γq, l0) : GName × List LogEntry) HMc $$ HM with ⟨HM, #Hel⟩
  imodintro
  isplitl [HM]
  · iexists _
    iframe HM
    ipureintro
    intro c'
    rw [GMap.elem_of_insert_set]
    have := GMap.lookup_insert_is_Some M c c' ((γq, l0) : GName × List LogEntry)
    change _ ↔ ((<[c := ((γq, l0) : GName × List LogEntry)]> M) !! c').isSome = true
    constructor
    · rintro (h | h)
      · subst h; exact this.2 (.inl rfl)
      · by_cases e : c = c'
        · exact this.2 (.inl e)
        · exact this.2 (.inr ⟨e, (HU c').mp h⟩)
    · intro h
      rcases this.1 h with e | ⟨-, h⟩
      · exact .inl e.symm
      · exact .inr ((HU c').mpr h)
  isplitl []
  · iexists γq, l0
    iframe Hel Hsp Hau Hl0
  · iexists γq
    iframe Hel

omit [StorageModel GF] sem package_sem in
theorem readCtx_commit_impl (γ : Cluster) (N : Namespace) (U : GSet (List w8)) (c : List w8)
    (Q : List LogEntry → IProp GF) :
    c ∉ U →
    ownReadCtxs (GF := GF) γ U ∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
           <{ ownCommittedOps γ ops, COMM □ Q ops }> ⊢
    |==> (ownReadCtxs γ (insert c U) ∗ isReadCtx γ N c Q) := by
  intro Hc
  iintro ⟨HU, #Hau⟩
  imod readCtx_commit_after_impl γ N U c Q [] Hc $$ [HU] with ⟨HU, #Hr, -⟩
  · iframe HU Hau
    iapply isCommittedLogLb_nil_impl
  imodintro
  iframe HU Hr

end ctx

/-! ## A new cluster -/

section boot
variable [GooseExts]

theorem ofEntryM_toEntryM (idx : w64) (e : LogEntry) : LogEntry.ofEntryM (e.toEntryM idx) = e := by
  cases e; rfl

theorem toEntries_length (l : List LogEntry) (base : Nat) :
    (LogEntry.toEntries l base).length = l.length := by
  unfold LogEntry.toEntries; exact List.length_mapIdx

theorem toEntries_getElem? (l : List LogEntry) (base k : Nat) :
    (LogEntry.toEntries l base)[k]? = (l[k]?).map (LogEntry.toEntryM (W64 (base + k + 1))) := by
  unfold LogEntry.toEntries; rw [List.getElem?_mapIdx]

theorem strip_toEntries (l : List LogEntry) (base : Nat) :
    strip (LogEntry.toEntries l base) = l := by
  apply List.ext_getElem?
  intro k
  unfold strip
  rw [List.getElem?_map, toEntries_getElem?]
  cases l[k]? <;> simp [ofEntryM_toEntryM]

/-- A raft log whose entries are at the indices after `base` is the Go entries of what the client
sees of it. -/
theorem toEntries_strip (L : List EntryM) (base : Nat)
    (H : ∀ (k : Nat) (e : EntryM), L[k]? = some e → uint.Z e.Index' = ((base + k + 1 : Nat) : Int)) :
    LogEntry.toEntries (strip L) base = L := by
  apply List.ext_getElem?
  intro k
  rw [toEntries_getElem?]
  unfold strip
  rw [List.getElem?_map]
  cases hk : L[k]? with
  | none => rfl
  | some e =>
    have hi := H k e hk
    simp only [Option.map_some]
    congr 1
    cases e with
    | mk t i ty d =>
      simp only [LogEntry.toEntryM, LogEntry.ofEntryM, EntryM.mk.injEq, and_true, true_and]
      simp only at hi
      apply word.unsigned_inj
      rw [hi]
      have := word.unsigned_range i
      word

theorem opsOf_eq_self (l : List LogEntry) (H : ∀ e ∈ l, ¬ e.isFiller ∧ ¬ e.isEmptyV2) :
    opsOf l = l := by
  unfold opsOf
  rw [List.filter_eq_self]
  intro e he
  simp [(H e he).1, (H e he).2]

theorem BootLog_ok {ps : List w64} {ctxs : List (List w8)} {boot : List LogEntry}
    (H : BootLog ps ctxs boot) : BootLogOk ps (LogEntry.toEntries boot 0) := by
  obtain ⟨Hl, Hb, Hk⟩ := H
  refine ⟨by rw [toEntries_length, Hl], by rw [toEntries_length]; exact Hb, fun k e He => ?_⟩
  rw [toEntries_getElem?] at He
  cases hb : boot[k]? with
  | none => rw [hb] at He; cases He
  | some e0 =>
    rw [hb] at He
    simp only [Option.map_some, Option.some.injEq] at He
    subst He
    obtain ⟨id, ctx, Hid, -, Ht, Hty, Hm⟩ := Hk k e0 hb
    have hk : k < boot.length := (List.getElem?_eq_some_iff.mp hb).1
    refine ⟨Ht, ?_, Hty, ⟨⟨W32 0, id, ctx, W64 0⟩, Hm, rfl, Hid⟩⟩
    show uint.Z (W64 ((0 + k + 1 : Nat) : Int)) = _
    have : ((0 + k + 1 : Nat) : Int) < 2 ^ 64 := by omega
    rw [uint_Z_W64 _ (by omega) this]
    push_cast; omega

theorem BootLog_opsOf {ps : List w64} {ctxs : List (List w8)} {boot : List LogEntry}
    (H : BootLog ps ctxs boot) : opsOf boot = boot := by
  apply opsOf_eq_self
  intro e he
  obtain ⟨k, hk⟩ := List.getElem?_of_mem he
  obtain ⟨-, -, -, -, -, Hty, -⟩ := H.2.2 k e hk
  refine ⟨?_, ?_⟩ <;> rintro ⟨-, h⟩ <;> rw [Hty] at h <;>
    have := congrArg (fun x : w32 => uint.Z x) h <;> revert this <;> decide

theorem BootLog_idx {ps : List w64} {ctxs : List (List w8)} {boot : List LogEntry}
    (H : BootLog ps ctxs boot) : IdxOk (LogEntry.toEntries boot 0) := by
  intro k e He
  have Hok := BootLog_ok H
  exact (Hok.2.2 k e He).2.1

/-- The fresh-data tokens of the keys of `L` (raft's `bootFreshFrom`). -/
theorem bootFreshFrom_lookup (F : GMap (List w8) Unit) (L : List EntryM) (k : List w8) :
    (bootFreshFrom F L) !! k = some () →
    F !! k = some () ∨ ∃ e ∈ L, entKey e.Type' e.Data' = k := by
  induction L generalizing F with
  | nil => intro h; exact .inl h
  | cons e L ih =>
    intro h
    rcases ih (Std.insert F (entKey e.Type' e.Data') ()) h with h1 | ⟨e', he', hk⟩
    · have h1' : (<[entKey e.Type' e.Data' := ()]> F) !! k = some () := h1
      rw [GMap.lookup_insert_Some] at h1'
      rcases h1' with ⟨hk, -⟩ | ⟨-, h⟩
      · exact .inr ⟨e, List.mem_cons_self .., hk⟩
      · exact .inl h
    · exact .inr ⟨e', List.mem_cons_of_mem _ he', hk⟩

end boot

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A set of distinct elements, as a list. -/
theorem bigSepM_listToSet (Φ : w64 → IProp GF) (ps : List w64) (Hnd : ps.Nodup) :
    ([∗map] id ↦ _u ∈ toMap (GMap.listToSet ps), Φ id) ⊢ [∗list] id ∈ ps, Φ id := by
  induction ps with
  | nil =>
    iintro -
    iapply (BigSepL.bigSepL_nil (Φ := fun _ id => Φ id)).2
    iempintro
  | cons p ps ih =>
    rw [List.nodup_cons] at Hnd
    have Hnone : (GMap.listToSet ps) !! p = none := by
      cases h : (GMap.listToSet ps) !! p with
      | none => rfl
      | some u =>
        exfalso; apply Hnd.1
        rw [← GMap.elem_of_list_to_set]
        show ((GMap.listToSet ps).lookup p).isSome = true
        show ((GMap.listToSet ps) !! p).isSome = true
        rw [h]; rfl
    rw [show toMap (GMap.listToSet (p :: ps)) =
      (Std.insert (GMap.listToSet ps : GMap w64 Unit) p () : GMap w64 Unit) from rfl]
    iintro H
    icases (BigSepM.bigSepM_insert (Φ := fun id (_u : Unit) => Φ id) Hnone).1 $$ H with ⟨Hp, H⟩
    iapply (BigSepL.bigSepL_cons (Φ := fun _ id => Φ id)).2
    iframe Hp
    iapply ih Hnd.2 $$ H

/-- **Read credits** (open: raft's `rdCred`). -/
def readCredits (γ : Cluster) (n : Nat) : IProp GF := rdCred γ.raft n

/-- (open) **A read request's credit.** -/
def readCredit (γ : Cluster) : IProp GF := readCredits γ 1

omit [StorageModel GF] sem package_sem in
theorem readCredits_split (γ : Cluster) (a b : Nat) :
    readCredits (GF := GF) γ (a + b) ⊣⊢ readCredits γ a ∗ readCredits γ b := by
  unfold readCredits; exact rdCred_split γ.raft a b

/-- The snapshots' data the cluster admits, as raft's names keep it (`RaftNames.reSnapOkRaw`, of
bootstrap entries): the client's predicate of the entries as it sees them. -/
def sokOf (snapOk : List LogEntry → List w8 → Prop) : List BootEntry → List w8 → Prop :=
  fun B d => snapOk (B.map fun b => (⟨b.term, b.type, b.data⟩ : LogEntry)) d

theorem reSnapOk_sokOf (γr : RaftNames) (so : List LogEntry → List w8 → Prop)
    (h : γr.reSnapOkRaw = sokOf so) (L : List EntryM) (d : List w8) :
    γr.reSnapOk L d ↔ so (strip L) d := by
  unfold RaftNames.reSnapOk; rw [h]; unfold sokOf strip; rw [List.map_map]; rfl

/-- What raft's names say of a static cluster of the voters `vs` in the namespace `N`, taking
snapshots whose data satisfy `snapOk`: the voters, the static mode, snapshots and leader transfer on,
no snapshot directory, the certificates' namespace `N`, the tracked bound (if any) the voters. -/
def StaticNames (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) : Prop :=
  γ.raft.reCfg = GMap.listToSet vs ∧ γ.raft.reDyn = none ∧ γ.raft.reNoSnap = false ∧
  γ.raft.reSnapOkRaw = sokOf snapOk ∧ γ.mode = RNMode.static.all ∧
  γ.raft.reSnapLoc = (fun _ => none) ∧ γ.raft.reCertNs = N ∧ γ.raft.reSnapReg = none ∧
  (γ.raft.reTracked = none ∨ γ.raft.reTracked = some (GMap.listToSet vs)) ∧
  vs ≠ [] ∧ vs.Nodup ∧ W64 0 ∉ vs ∧ (vs.length : Int) ≤ 2 ^ 62

/-- **The cluster is static** (the draft's `isStaticCluster`): raft's names say so, and the
cluster's invariants. -/
def isStaticCluster (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) : IProp GF :=
  iprop(⌜StaticNames γ N vs snapOk⌝ ∗ clusterInv γ N)

instance isStaticCluster_persistent (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) :
    Persistent (isStaticCluster (GF := GF) γ N vs snapOk) := by
  unfold isStaticCluster; infer_instance

/-- **Leader transfer is on** in the cluster (persistent). -/
def leaderTransferOn (γ : Cluster) (_N : Namespace) : IProp GF :=
  iprop(⌜γ.raft.reNoXfer = false⌝)

instance leaderTransferOn_persistent (γ : Cluster) (N : Namespace) :
    Persistent (leaderTransferOn (GF := GF) γ N) := by
  unfold leaderTransferOn; infer_instance

/-- **Leader transfer is off** in the cluster (persistent): raft's no-transfer mode. -/
def leaderTransferOff (γ : Cluster) (_N : Namespace) : IProp GF :=
  iprop(⌜γ.raft.reNoXfer = true⌝)

instance leaderTransferOff_persistent (γ : Cluster) (N : Namespace) :
    Persistent (leaderTransferOff (GF := GF) γ N) := by
  unfold leaderTransferOff; infer_instance

/-- Leader transfer on or off, by `transfer`. -/
theorem leaderTransfer_of (γ : Cluster) (N : Namespace) (transfer : Bool)
    (h : γ.raft.reNoXfer = !transfer) :
    ⊢ if transfer then leaderTransferOn (GF := GF) γ N else leaderTransferOff γ N := by
  cases transfer
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold leaderTransferOff; ipureintro; exact h
  · simp only [↓reduceIte]
    unfold leaderTransferOn; ipureintro; exact h

/-- **A node's boot token** of a new cluster of the peers `ps` with the contexts `ctxs`: the cluster
static (of the peers), its raft ghost state at the bootstrap state, the committed bootstrap log, the
bytes of its entries (`bootMarshal`), and the term budget at the bootstrap term. -/
def nodeBoot (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (id : w64) :
    IProp GF :=
  iprop((∃ so, isStaticCluster γ N ps so) ∗ ⌜BootLogOk ps γ.raft.reBoot⌝ ∗
    ownRaftGhost γ.raft id (bootPState γ.raft.reBoot) ∗
    isCommitted γ.raft γ.raft.reBoot ∗ bootMarshal ps ctxs γ.raft.reBoot ∗
    inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 1))

/-- **A static cluster's boot token** for node `id` (the draft's `nodeRestartBoot`): the cluster
static (of the voters `vs`), its raft ghost state at the initial state, the empty log committed, the
term budget. -/
def nodeRestartBoot (γ : Cluster) (N : Namespace) (vs : List w64) (id : w64) : IProp GF :=
  iprop((∃ so, isStaticCluster γ N vs so) ∗ ownRaftGhost γ.raft id initPState ∗
    isCommitted γ.raft [] ∗ inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 0))

/-- The client's part of a new cluster, built in raft's allocation (`allocClientGen`). -/
def allocOut (N : Namespace) (boot : List LogEntry) (bud : BudgetNames) (md : RNMode)
    (tab : GMap w64 GName) (γr : RaftNames) : IProp GF :=
  iprop(∃ γ : Cluster, ⌜γ.raft = γr ∧ γ.bud = bud ∧ γ.mode = md.all ∧ γ.nodeTab = tab⌝ ∗
    savedPredOwn γ.trueQ DFrac.discard (fun _ : List EntryM => iprop(True : IProp GF)) ∗ apiInv γ N ∗ ownCommittedOps γ boot ∗ ownReadCtxs γ ∅)

/-- The adapter's part of raft's allocation: its ghost state and invariant, raft's standing update
from it. -/
theorem api_alloc_client (N : Namespace) (E : CoPset) (cfg : GSet w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (bud : BudgetNames) (md : RNMode)
    (tab : GMap w64 GName) (dyn : Option ((e : GooseExts) → @DynCfg e))
    (HB : BootLog ps ctxs boot) :
    ⊢ allocClientGen (GF := GF) E cfg dyn (fun _ _ => True) (LogEntry.toEntries boot 0)
        (allocOut N boot bud md tab) (N .@ "raft") := by
  unfold allocClientGen
  iintro %γr %Hγr #Hc HrL Hfa Hrfa ⟨%γT, #HspT, #Hpis⟩
  obtain ⟨-, -, -, HbL, HNs⟩ := Hγr
  have Hblen : (boot.length : Int) < (receiptBound GF : Int) + γr.reBoot.length := by
    have := receiptBound_pos (GF := GF)
    rw [HbL, toEntries_length]; omega
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γf, Hf, #Hflb⟩
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γo, Ho, #Holb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × List LogEntry) with ⟨%γc, Hca⟩
  icases ((monoListAuthOwn_fractional (GF := GF) γo
      boot).fractional (1 : Qp).half (1 : Qp).half).1
    $$ [Ho] with ⟨Ho1, Ho2⟩
  · rw [Qp.half_add_half]; iexact Ho
  let γ : Cluster := ⟨γr, γf, γo, γc, bud, γT, md.all, tab⟩
  imod inv_alloc (apiN N) E (apiInvBody (GF := GF) γ) $$ [HrL Hf Ho1 Hfa Hrfa] with #Hinv
  · inext
    unfold apiInvBody
    iexists LogEntry.toEntries boot 0, bootFresh (LogEntry.toEntries boot 0), ∅
    rw [strip_toEntries, (BootLog_opsOf HB)]
    iframe HrL Hf Ho1 Hfa Hrfa
    isplitr
    · ipureintro; refine ⟨BootLog_idx HB, ?_⟩; rw [toEntries_length]; exact Hblen
    isplitr
    · unfold freshOk
      imodintro
      iintro %k %Hk
      unfold bootFresh at Hk
      rcases bootFreshFrom_lookup ∅ _ k Hk with h | ⟨e, he, hek⟩
      · exact absurd h (by simp [GMap.lookup_empty])
      · obtain ⟨j, hj⟩ := List.getElem?_of_mem he
        subst hek
        iapply (BigSepL.bigSepL_lookup (Φ := fun _ (e : EntryM) =>
          propIsAt (GF := GF) γr (entKey e.Type' e.Data') γT) hj) $$ Hpis
    isplitr
    · iapply cmtFacts_bootOk γ (BootLog_ok HB)
    isplitr
    · unfold rdKeys
      imodintro
      iintro %c %Hc
      exact absurd Hc (by simp [GMap.lookup_empty])
    · unfold rdFreshOk
      imodintro
      iintro %c %Hc
      exact absurd Hc (by simp [GMap.lookup_empty])
  ihave #Hinv' : apiInv (GF := GF) γ N $$ []
  · unfold apiInv; iexact Hinv
  ihave #Hnoop := api_noopAu γ N HNs $$ Hinv'
  imodintro
  iframe Hnoop
  unfold allocOut
  iexists γ
  isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  iframe Hinv' HspT
  isplitl [Ho2]
  · unfold ownCommittedOps
    iframe Ho2
    iexists boot
    unfold isCommittedLogLb
    rw [(BootLog_opsOf HB)]
    isplitl []
    · iright; iframe Hflb Holb
      isplitr; · ipureintro; exact Hblen
      unfold cmtFactsS
      iexists LogEntry.toEntries boot 0
      isplitr; · ipureintro; exact strip_toEntries boot 0
      iapply cmtFacts_bootOk γ (BootLog_ok HB)
    ipureintro; rfl
  · unfold ownReadCtxs
    iexists ∅
    iframe Hca
    ipureintro
    intro c
    constructor <;> intro h <;> exact absurd h (by simp [Membership.mem, GMap.lookup_empty])

theorem listToSet_ne_empty (ps : List w64) (Hne : ps ≠ []) : GMap.listToSet ps ≠ ∅ := by
  intro h
  obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil Hne
  have : p ∈ GMap.listToSet (p :: ps') := (GMap.elem_of_list_to_set p _).2 (List.mem_cons_self ..)
  rw [h] at this
  exact (GMap.not_elem_of_empty p) this

/-- **A new cluster** (the draft's `cluster_alloc`). -/
theorem cluster_alloc_impl (N : Namespace) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (snapOk : List LogEntry → List w8 → Prop) (transfer : Bool)
    (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 →
    BootLog ps ctxs boot → ps.Nodup → ps ≠ [] → W64 0 ∉ ps →
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      |={E}=> ∃ γ, ⌜γ.raft.reBoot.length = boot.length⌝ ∗ ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isStaticCluster γ N ps snapOk ∗
        (if transfer then leaderTransferOn γ N else leaderTransferOff γ N) ∗
        [∗list] id ∈ ps, nodeBoot γ N ps ctxs id := by
  intro Hrb HB Hnd Hne Hnz
  iintro #Hm
  imod budget_alloc_boot (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  have Hok := (BootLog_ok HB)
  have Hwf := Hok.wf Hnd
  have Hbne : LogEntry.toEntries boot 0 ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [toEntries_length, HB.1] at this
    exact Hne (List.eq_nil_of_length_eq_zero this)
  have Hcne := listToSet_ne_empty ps Hne
  have Hnz' : W64 0 ∉ GMap.listToSet ps := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have Hlen : (ps.length : Int) ≤ 2 ^ 62 := by have := HB.2.1; rw [HB.1] at this; omega
  ihave Hcl := api_alloc_client (GF := GF) N E (GMap.listToSet ps) ps ctxs boot bud .static ∅ none HB
  imod ownRaftGhost_alloc_core E (GMap.listToSet ps) (GMap.listToSet ps) none (fun _ _ => True)
    (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot bud .static ∅) (some (GMap.listToSet ps))
    (fun T hT => by cases hT; exact ⟨GMap.subseteq_refl _, rfl⟩) false (fun h => by cases h)
    (!transfer) (fun _ => Hbne) (sokOf snapOk) (fun _ => none) (N .@ "raft") N Hcne
    Hnz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, Hboot, Htrk, Hns, Hnx, Hsok, Hsl, HNs, Hcert, Hreg⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb, Hγm, -⟩ := Hγr
  subst Hγr
  ihave #Hst : isStaticCluster (GF := GF) γ N ps snapOk $$ []
  · unfold isStaticCluster clusterInv
    iframe Hcinv Hinv HspT
    ipureintro
    exact ⟨⟨Hcfg, Hdyn, Hns, Hsok, Hγm, Hsl, Hcert, Hreg, .inr Htrk, Hne, Hnd, Hnz, Hlen⟩, HNs⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; rw [Hboot, toEntries_length]
  iframe Hops Hctx Hst
  isplitl [Hcr]
  · unfold readCredits; iexact Hcr
  isplitr
  · iapply leaderTransfer_of γ N transfer Hnx
  simp only [Option.isSome_none]
  rw [← bootPState_eq]
  iapply bigSepM_listToSet _ ps Hnd
  iapply BigSepM.bigSepM_impl $$ Hnodes
  imodintro
  iintro %id %u %_ Hg
  unfold nodeBoot
  rw [Hboot]
  rw [Hγb]
  iframe Hg Hc0 Hm Hbinv Htlb
  isplitr
  · iexists snapOk; iexact Hst
  ipureintro; exact Hok

/-- **A new static cluster** (the draft's `cluster_alloc_static`). -/
theorem cluster_alloc_static_impl (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) ≤ 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ownCommittedOps (GF := GF) γ [] ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isStaticCluster γ N vs snapOk ∗ leaderTransferOn γ N ∗
        [∗list] id ∈ vs, nodeRestartBoot γ N vs id := by
  intro Hrb Hne Hnd Hnz Hlen
  imod budget_alloc (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  have HB : BootLog ([] : List w64) [] [] := ⟨rfl, by simp, fun k e h => by simp at h⟩
  have Hcne := listToSet_ne_empty vs Hne
  have Hnz' : W64 0 ∉ GMap.listToSet vs := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have H0 : LogEntry.toEntries ([] : List LogEntry) 0 = [] := rfl
  have Hcl0 := api_alloc_client (GF := GF) N E (GMap.listToSet vs) [] [] [] bud .static ∅ none HB
  rw [H0] at Hcl0
  ihave Hcl := Hcl0
  imod ownRaftGhost_alloc_core E (GMap.listToSet vs) (GMap.listToSet vs) none (fun _ _ => True)
    [] (W64 0) (allocOut N [] bud .static ∅) none (fun _ h => by cases h) false (fun h => by cases h)
    false (fun h => by cases h) (sokOf snapOk) (fun _ => none) (N .@ "raft") N Hcne
    Hnz' BootWf_nil (fun h => absurd rfl h)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, -, Htrk, Hns, Hnx, Hsok, Hsl, HNs, Hcert, Hreg⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb, Hγm, -⟩ := Hγr
  subst Hγr
  ihave #Hst : isStaticCluster (GF := GF) γ N vs snapOk $$ []
  · unfold isStaticCluster clusterInv
    iframe Hcinv Hinv HspT
    ipureintro
    exact ⟨⟨Hcfg, Hdyn, Hns, Hsok, Hγm, Hsl, Hcert, Hreg, .inl Htrk, Hne, Hnd, Hnz, Hlen⟩, HNs⟩
  imodintro
  iexists γ
  iframe Hops Hctx Hst
  isplitl [Hcr]
  · unfold readCredits; iexact Hcr
  isplitr
  · unfold leaderTransferOn; ipureintro; exact Hnx
  simp only [Option.isSome_none]
  iapply bigSepM_listToSet _ vs Hnd
  iapply BigSepM.bigSepM_impl $$ Hnodes
  imodintro
  iintro %id %u %_ Hg
  unfold nodeRestartBoot
  rw [initPState_eq, Hγb]
  iframe Hg Hc0 Hbinv Htlb
  iexists snapOk; iexact Hst

end alloc

/-! ## What raft's commit facts and read states give the client -/

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftN_api (N : Namespace) {E : CoPset} (HE : ↑N ⊆ E) (x : String) :
    (↑((N .@ "raft") .@ x) : CoPset) ⊆ E \ ↑(apiN N) := by
  intro p hp
  have h1 : p ∈ (↑(N .@ "raft") : CoPset) := nclose_subseteq (N .@ "raft") x p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨HE p (nclose_subseteq N "raft" p h1),
    fun h => ndot_ne_disjoint N (show "raft" ≠ "api" by decide) p ⟨h1, h⟩⟩

/-- **A raft commit fact, as the client sees it**: a lower bound of the full log (and so of the
requested entries), whose entries are at their positions. -/
theorem api_committed_lb (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (D : List EntryM) :
    ⊢ clusterInv (GF := GF) γ N -∗ isCommitted γ.raft D ={E}=∗
      isCommittedLogLb γ (strip D) ∗ ⌜IdxOk D⌝ := by
  iintro #Hci #HD
  unfold clusterInv
  icases Hci with ⟨%HNs, #Hcinv, #Hinv, -⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩ Hclose
  ihave #Hli := raftCommitInv_log γ.raft $$ Hcinv
  have Hl : (↑(raftLogN γ.raft) : CoPset) ⊆ E \ ↑(apiN N) := by
    unfold raftLogN raftN; rw [HNs]; exact raftN_api N HE "log"
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  iunfold rLog at HrL
  ihave %HLeq := ghostVar_agree γ.raft.reRLog P rlq L (1 : Qp).half $$ Hq1 HrL
  subst HLeq
  ihave %HDP := isCommitted_prefix γ.raft D P $$ HD HP
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  ihave #Hflb := monoListLbOwn_get γ.full 1 (strip P) $$ Hfull
  ihave #Holb := monoListLbOwn_get γ.ops (1 : Qp).half (opsOf (strip P)) $$ Hops
  imod Hclose $$ [HrL Hfull Hops HF HRF] with -
  · inext
    iexists P, F, RF
    unfold rLog
    iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
    ipureintro; exact Hidx
  imodintro
  isplitl []
  · unfold isCommittedLogLb
    iright
    isplitl []
    · iapply monoListLbOwn_le _ (strip_prefix HDP) $$ Hflb
    isplitl []
    · iapply monoListLbOwn_le _ (opsOf_prefix (strip_prefix HDP)) $$ Holb
    isplitl []
    · ipureintro
      have := HDP.length_le; have := Hidx.2; rw [strip_length]; omega
    iapply cmtFactsS_prefix γ P (strip D) (strip_prefix HDP) $$ Hcf
  ipureintro
  intro k e Hk
  obtain ⟨r, rfl⟩ := HDP
  exact Hidx.1 k e (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hk).1]; exact Hk)

/-- A log whose term at `c` is known is at least `c` long. -/
theorem termAt_len (F : List EntryM) (c : w64) (h : plogTermAt base0 F c ≠ none) :
    uint.nat c ≤ F.length := by
  have := (not_congr (plogTermAt_none_range base0 F c)).1 h
  unfold plogLastIndexZ at this
  rw [base0_index] at this
  have := rUnat_eq c
  omega

theorem termAt_some_of_le (F : List EntryM) (c : w64) (hc : uint.nat c ≤ F.length) :
    plogTermAt base0 F c ≠ none := by
  intro h
  rcases (plogTermAt_none_range base0 F c).1 h with h | h
  · rw [base0_index] at h; have := word.unsigned_range c; omega
  · unfold plogLastIndexZ at h; rw [base0_index] at h; have := rUnat_eq c; omega

/-- **A commit witness names a committed log as long as its index.** Its full log has a term at
the index (`commitJ`: the bootstrap log's, or a commit fact's, `cqAt`), so is that long. -/
theorem commitWit_len (γr : RaftNames) (t c : w64) :
    ⊢ commitWit (GF := GF) γr t c -∗ ∃ L, isCommitted γr L ∗ ⌜L.length = uint.nat c⌝ := by
  iintro #Hw
  iunfold commitWit at Hw
  icases Hw with ⟨%F, -, -, #Hin, #Hc⟩
  ihave #Hj := commitIn_j γr F c t $$ Hin
  iunfold commitJ at Hj
  have Hcn : (uint.Z c).toNat = uint.nat c := by have := rUnat_eq c; omega
  ihave %HF : ⌜uint.nat c ≤ F.length⌝ $$ []
  · icases Hj with (%Hb | ⟨%t', %n, %G, #Hq⟩)
    · ipureintro
      by_cases h0 : uint.nat c = 0
      · omega
      apply termAt_len
      rw [← Hb.2]
      apply termAt_some_of_le
      have := Hb.1; have := rUnat_eq c; omega
    · icases Hq with ⟨#Hq, %Hcn2⟩
      icases cq_cqAt γr t' n G $$ Hq with ⟨%a, %cf, %q, Hq'⟩
      iunfold cqAt at Hq'
      icases Hq' with ⟨%Hn, -⟩
      ipureintro
      have HnG := (plogTermAt_some_range _ _ _ _ Hn).2
      unfold plogLastIndexZ at HnG; rw [base0_index] at HnG
      apply termAt_len
      rw [← Hcn2.2.2]
      apply termAt_some_of_le
      have := Hcn2.1; have := rUnat_eq c; have := rUnat_eq n; omega
  iexists F.take (uint.Z c).toNat
  iframe Hc
  ipureintro
  rw [List.length_take, Hcn]; omega

/-- (2026-10-27) **The log through index `c` was committed at term `t`** (the draft's
`committedAtTerm`): raft's commit witness, and a committed log as long as its index, as the client
knows it. -/
def committedAtTerm (γ : Cluster) (_N : Namespace) (t c : w64) : IProp GF :=
  iprop(commitWit γ.raft t c ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜l.length = uint.nat c⌝)

instance committedAtTerm_persistent (γ : Cluster) (N : Namespace) (t c : w64) :
    Persistent (committedAtTerm (GF := GF) γ N t c) := by
  unfold committedAtTerm; infer_instance

theorem committedAtTerm_of_raft (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (t c : w64) :
    ⊢ clusterInv (GF := GF) γ N -∗ commitWit γ.raft t c ={E}=∗ committedAtTerm γ N t c := by
  iintro #Hci #Hw
  icases commitWit_len γ.raft t c $$ Hw with ⟨%L, #HL, %Hlen⟩
  imod api_committed_lb γ N E HE L $$ Hci HL with ⟨#Hlb, -⟩
  imodintro
  unfold committedAtTerm
  iframe Hw
  iexists strip L
  iframe Hlb
  ipureintro; rw [strip_length]; exact Hlen

/-- (2026-10-27) What a hard state says, the committed log delivered with it of length `n` (raft's
`hsWit`, as the client sees it). (2026-10-28, stage U3d) Or nothing outside raft's no-snapshot mode:
after a snapshot `Ready` the witness bounds the log before the snapshot, not the one delivered up to
it (a dynamic cluster in the no-snapshot mode keeps `nodeDriver_hardStateCommitted`). -/
def hsCommitted (γ : Cluster) (N : Namespace) (h : HardStateM) (n : Nat) : IProp GF :=
  iprop(⌜h = hsZero⌝ ∨ committedAtTerm γ N h.Term' h.Commit' ∗ ⌜(n : Int) ≤ uint.Z h.Commit'⌝ ∨
    ⌜γ.raft.reNoSnap = false⌝)

instance hsCommitted_persistent (γ : Cluster) (N : Namespace) (h : HardStateM) (n : Nat) :
    Persistent (hsCommitted (GF := GF) γ N h n) := by
  unfold hsCommitted; infer_instance

theorem hsCommitted_of_raft (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (h : HardStateM) (n : Nat) :
    ⊢ clusterInv (GF := GF) γ N -∗ hsWit γ.raft h n ={E}=∗ hsCommitted γ N h n := by
  iintro #Hci #Hw
  iunfold hsWit at Hw
  unfold hsCommitted
  icases Hw with (%H | ⟨#Hw, %Hn⟩)
  · imodintro; ileft; ipureintro; exact H
  imod committedAtTerm_of_raft γ N E HE _ _ $$ Hci Hw with #Hc
  imodintro
  iright; ileft
  iframe Hc
  ipureintro; exact Hn

/-- **A read state** (persistent): raft's (`readOk`), its context committed (`γ.ctxs`) after a log
no longer than its index. -/
def readStateOk (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) : IProp GF :=
  iprop(clusterInv γ N ∗ readOk γ.raft c idx ∗ ∃ (γq : GName) (l0 : List LogEntry),
    c ↪[γ.ctxs]□ ((γq, l0) : GName × List LogEntry) ∗ ⌜l0.length ≤ uint.nat idx⌝)

instance readStateOk_persistent (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) :
    Persistent (readStateOk (GF := GF) γ N c idx) := by
  unfold readStateOk; infer_instance

/-- A context with a raft read was deposited by the adapter: its fresh token is in raft's
registry, so the adapter minted it. -/
theorem api_readReq_dep (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (c : List w8) (Lc : List EntryM) :
    ⊢ clusterInv (GF := GF) γ N -∗ readReq γ.raft c Lc ={E}=∗ readKey γ c ∗ ▷ readDep γ c := by
  iintro #Hci #Hrq
  unfold clusterInv
  icases Hci with ⟨%HNs, #Hcinv, #Hinv, -⟩
  unfold readReq
  icases Hrq with ⟨%γq, #Hel, -⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩ Hclose
  ihave #Hri := raftCommitInv_reg γ.raft $$ Hcinv
  have Hr : (↑(raftRegN γ.raft) : CoPset) ⊆ E \ ↑(apiN N) := by
    unfold raftRegN raftN; rw [HNs]; exact raftN_api N HE "reg"
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold readsReg at Hreads
  icases Hreads with ⟨>Hra, Hs⟩
  icases ghost_map_lookup $$ Hra Hel with %HRc
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun c r =>
      iprop(▷ (readSlot (GF := GF) γ.raft r l ∗ rdFresh γ.raft c))) HRc).1 $$ Hs
    with ⟨⟨Hsl, >Hfr⟩, Hsback⟩
  iunfold rdFresh at Hfr
  icases ghost_map_lookup $$ HRF Hfr with %HRFc
  ihave Hs := Hsback $$ [Hsl Hfr]
  · inext; iframe Hsl; unfold rdFresh; iexact Hfr
  imod Hclose2 $$ [Hq2 Hprops Hra Hs] with -
  · iexists l
    iframe Hq2
    unfold regsAt readsReg
    inext
    iexists R, RR
    iframe Hprops Hnoop Hra
    iexact Hs
  imod Hclose $$ [HrL Hfull Hops HF HRF] with -
  · inext
    iexists L, F, RF
    iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
    ipureintro; exact Hidx
  imodintro
  iunfold rdKeys at HRk
  isplitl []
  · iapply HRk $$ %c %HRFc
  · inext
    iunfold rdFreshOk at HRFok
    iapply HRFok $$ %c %HRFc

/-- **A raft read state, as the client sees it.** -/
theorem api_readState (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (st : ReadStateM) :
    ⊢ clusterInv (GF := GF) γ N -∗ EtcdGrove.readStateRaw γ.raft st ={E}=∗
      readStateOk γ N st.RequestCtx' st.Index' := by
  iintro #Hci #Hst
  iunfold EtcdGrove.readStateRaw at Hst
  icases Hst with ⟨%c, %Hc, #Hok⟩
  rw [Hc]
  ihave #Hok' := Hok
  iunfold readOk at Hok'
  icases Hok' with ⟨%Lc, #Hrq, %HLcb⟩
  imod api_readReq_dep γ N E HE c Lc $$ Hci Hrq with ⟨#Hdep, -⟩
  iunfold readKey at Hdep
  icases Hdep with ⟨%γq, %l0, %Lc', #Hel, #Hrq', %Hl0⟩
  iunfold readReq at Hrq Hrq'
  icases Hrq with ⟨%γr, #Hr, -⟩
  icases Hrq' with ⟨%γr', #Hr', -⟩
  ihave %Hag := ghostMapElem_agree $$ Hr Hr'
  have HLc : Lc' = Lc := by simp only [Prod.mk.injEq] at Hag; exact Hag.2.symm
  subst HLc
  imodintro
  unfold readStateOk
  iframe Hci Hok
  iexists γq, l0
  iframe Hel
  ipureintro
  have := uint_nat_eq st.Index'
  omega

theorem api_readStates (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (sts : List ReadStateM) :
    ⊢ clusterInv (GF := GF) γ N -∗ ([∗list] st ∈ sts, EtcdGrove.readStateRaw γ.raft st) ={E}=∗
      [∗list] st ∈ sts, readStateOk γ N st.RequestCtx' st.Index' := by
  induction sts with
  | nil =>
    iintro #_ -
    imodintro
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (st : ReadStateM) =>
      readStateOk (GF := GF) γ N st.RequestCtx' st.Index')).2
    iempintro
  | cons st sts ih =>
    iintro #Hci H
    icases (BigSepL.bigSepL_cons (Φ := fun _ (st : ReadStateM) =>
      EtcdGrove.readStateRaw (GF := GF) γ.raft st)).1 $$ H with ⟨H1, H⟩
    imod api_readState γ N E HE st $$ Hci H1 with #H1
    imod ih $$ Hci H with H
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (st : ReadStateM) =>
      readStateOk (GF := GF) γ N st.RequestCtx' st.Index')).2
    iframe H1 H

omit [StorageModel GF] sem package_sem in
theorem readStateOk_used_impl (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64)
    (U : GSet (List w8)) :
    readStateOk (GF := GF) γ N c idx ∗ ownReadCtxs γ U ⊢ ⌜c ∈ U⌝ := by
  unfold readStateOk ownReadCtxs
  iintro ⟨⟨-, -, %γq, %l0, #Hel, -⟩, %M, HM, %HU⟩
  icases ghost_map_lookup $$ HM Hel with %HMc
  ipureintro
  apply (HU c).mpr
  show (M.lookup c).isSome = true
  show (M !! c).isSome = true
  rw [HMc]; rfl

/-- A client's lower bound is a raft commit fact. -/
theorem api_lb_committed (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (l : List LogEntry) :
    ⊢ clusterInv (GF := GF) γ N -∗ isCommittedLogLb γ l ={E}=∗
      ∃ D : List EntryM, ⌜strip D = l⌝ ∗ isCommitted γ.raft D := by
  iintro #Hci #Hl
  unfold clusterInv
  icases Hci with ⟨%HNs, #Hcinv, #Hinv, -⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩ Hclose
  have Hl : (↑(raftLogN γ.raft) : CoPset) ⊆ E \ ↑(apiN N) := by
    unfold raftLogN raftN; rw [HNs]; exact raftN_api N HE "log"
  imod rLog_committed γ.raft L (E \ ↑(apiN N)) Hl $$ Hcinv HrL with ⟨HrL, #HLc⟩
  iunfold isCommittedLogLb at Hl
  icases Hl with (%Hnil | ⟨#Hfl, -⟩)
  · imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iexists []
    isplitr
    · ipureintro; rw [Hnil]; rfl
    · iapply isCommitted_mono γ.raft _ _ List.nil_prefix $$ HLc
  icases mono_list_auth_lb_valid $$ Hfull Hfl with %Hpre
  imod Hclose $$ [HrL Hfull Hops HF HRF] with -
  · inext
    iexists L, F, RF
    iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
    ipureintro; exact Hidx
  imodintro
  iexists L.take l.length
  isplitr
  · ipureintro
    obtain ⟨r, hr⟩ := Hpre.2
    unfold strip
    rw [List.map_take]
    show List.take l.length (strip L) = l
    rw [← hr]; exact List.take_left
  · iapply isCommitted_mono γ.raft _ _ (List.take_prefix _ _) $$ HLc

/-- Collecting a read's result at a committed log `L` at least as long as the deposit's: the
result predicate the read was deposited with (named `γq`) holds of `L`, under the invariant's
later. (`read_collect` without the comparison with a predicate of the client's.) -/
theorem read_collect_raw (γr : RaftNames) (E : CoPset) (c : List w8) (γq : GName)
    (Lc L : List EntryM) :
    ↑(raftN γr) ⊆ E → Lc.length ≤ L.length →
    ⊢ raftCommitInv (GF := GF) γr -∗ c ↪[γr.reReads]□ ((γq, Lc) : GName × List EntryM) -∗
      isCommitted γr L ={E}=∗
      ▷ ∃ Qr : List EntryM → IProp GF, savedPredOwn γq DFrac.discard Qr ∗ □ Qr L := by
  intro HE Hlen
  iintro #Hinv #Hel #HL
  ihave #Hri := raftCommitInv_reg γr $$ Hinv
  ihave #Hli := raftCommitInv_log γr $$ Hinv
  have HE1 := raftRegN_of HE
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  have HE2 := raftLogN_of_diff HE
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  ihave %Heq := ghostVar_agree γr.reRLog P rlq l rlq $$ Hq1 Hq2
  subst Heq
  ihave %HLP := isCommitted_prefix γr L P $$ HL HP
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold readsReg at Hreads
  icases Hreads with ⟨>Hra, Hs⟩
  icases ghost_map_lookup $$ Hra Hel with %HRc
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  ihave #Hslot : ▷ readSlot γr (γq, Lc) P $$ [Hs]
  · ihave ⟨⟨#Hsl, -⟩, -⟩ := (BigSepM.bigSepM_delete (Φ := fun c r =>
      iprop(▷ (readSlot (GF := GF) γr r P ∗ rdFresh γr c))) HRc).1 $$ Hs
    iexact Hsl
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imod Hclose2 $$ [Hq2 Hprops Hra Hs] with -
  · iexists P
    iframe Hq2
    unfold regsAt readsReg
    inext
    iexists R, RR
    iframe Hprops Hnoop Hra
    iexact Hs
  imodintro
  inext
  iunfold readSlot at Hslot
  icases Hslot with ⟨%Qr', #Hsp', #-, %Hpre, #Hres⟩
  have HlenP : L.length ≤ P.length := HLP.length_le
  have Hn : Lc.length ≤ L.length ∧ L.length ≤ P.length := ⟨Hlen, HlenP⟩
  ihave #HQ' := Hres $$ %L.length %Hn
  have HtL : P.take L.length = L := by
    obtain ⟨r, rfl⟩ := HLP; exact List.take_left
  rw [HtL]
  iexists Qr'
  iframe Hsp' HQ'

/-- **What a read state tells the client** of a context it committed: the read took effect when
the committed log was `l`, of length `idx`, and gave `Q` of its requested entries. (Changed from
the draft: a ghost update within `N`, given a committed log at least `idx` long, the result
under two laters; see the report.) -/
theorem readStateOk_ctx_impl (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64)
    (Q : List LogEntry → IProp GF) (l' : List LogEntry) (E : CoPset) (HE : ↑N ⊆ E) :
    uint.nat idx ≤ l'.length →
    ⊢ readStateOk γ N c idx -∗ isReadCtx γ N c Q -∗ isCommittedLogLb γ l' ={E}=∗
      ∃ l, ⌜l.length = uint.nat idx⌝ ∗ isCommittedLogLb γ l ∗ ▷ ▷ □ Q (opsOf l) := by
  intro Hle
  iintro #Hst #Hctx #Hl'
  unfold readStateOk
  icases Hst with ⟨#Hci, #Hok, %γq0, %l00, #Hel0, -⟩
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -⟩
  iunfold readOk at Hok
  icases Hok with ⟨%Lc, #Hrq, %HLc⟩
  imod api_readReq_dep γ N E HE c Lc $$ Hci Hrq with ⟨-, #Hdep⟩
  imod api_lb_committed γ N E HE l' $$ Hci Hl' with ⟨%D, %HD, #HDc⟩
  have HDlen : D.length = l'.length := by rw [← HD, strip_length]
  have Hn : uint.nat idx ≤ D.length := by rw [HDlen]; exact Hle
  ihave #HL := isCommitted_mono γ.raft (D.take (uint.nat idx)) D (List.take_prefix _ _) $$ HDc
  have HLlen : (D.take (uint.nat idx)).length = uint.nat idx := by
    rw [List.length_take]; omega
  unfold readReq
  icases Hrq with ⟨%γr, #Hrel, -⟩
  have HrN : ↑(raftN γ.raft) ⊆ E := by unfold raftN; rw [HNs]; exact raftN_sub N HE
  have HLc' : Lc.length ≤ (D.take (uint.nat idx)).length := by
    rw [HLlen]; have := uint_nat_eq idx; omega
  imod read_collect_raw γ.raft E c γr Lc (D.take (uint.nat idx)) HrN HLc' $$ Hcinv Hrel HL
    with HX
  have Hsl : strip (D.take (uint.nat idx)) = l'.take (uint.nat idx) := by
    unfold strip; rw [List.map_take]; show List.take _ (strip D) = _; rw [HD]
  imodintro
  iexists l'.take (uint.nat idx)
  isplitr
  · ipureintro; rw [List.length_take]; omega
  isplitr
  · iapply isCommittedLogLb_mono_impl γ _ _ (List.take_prefix _ _) $$ Hl'
  inext
  icases HX with ⟨%Qr, #Hsp, #HQr⟩
  iunfold readDep at Hdep
  icases Hdep with ⟨%γq, %l0, %Q0, #Hel, #HspQ, #Hrd⟩
  iunfold isRead at Hrd
  icases Hrd with ⟨%γr', %Lc', #Hrel', #Hspr⟩
  ihave %Hagr := ghostMapElem_agree $$ Hrel Hrel'
  cases Hagr
  unfold isReadCtx
  icases Hctx with ⟨%γq1, %l1, #Hel1, #Hsp1, -⟩
  ihave %Hag1 := ghostMapElem_agree $$ Hel Hel1
  cases Hag1
  ihave #Heq1 := saved_pred_agree γr DFrac.discard DFrac.discard Qr (qrOf Q0)
    (D.take (uint.nat idx)) $$ Hsp Hspr
  ihave #Heq2 := saved_pred_agree γq DFrac.discard DFrac.discard Q0 Q
    (opsOf (l'.take (uint.nat idx))) $$ HspQ Hsp1
  inext
  ihave Hiff1 := internalEq_iff _ _ $$ Heq1
  icases Hiff1 with ⟨Hiff1, -⟩
  ihave Hiff2 := internalEq_iff _ _ $$ Heq2
  icases Hiff2 with ⟨Hiff2, -⟩
  imodintro
  iapply Hiff2
  ihave HQ0 := Hiff1 $$ HQr
  unfold qrOf
  rw [Hsl]
  iexact HQ0

end facts

/-! ## Snapshots' certificates

A snapshot's certificate as the client sees it (`snapshotCert`): raft's configuration certificate
and its data's, the latter over a committed log the client knows (`isCommittedLogLb`), so that its
laws need no invariant. Raft's (`raftSnapCertD`) and the client's convert into each other within
`N` (`snapshotCert_of_raft`, `raft_of_snapshotCert`). The storage's registry is tied to the
client's certificates (`storageCertLink`), hence to raft's (`storCertOk`) at the cluster's
certificate namespace `N` (`RaftNames.reCertNs`: the conversion opens the adapter's invariant, inside
`N`). A `MemoryStorage`'s registry invariant (`storageCertInv`) is at `N .@ "cert"`. -/

section cert
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-10-28, stage U2) What raft's `snapAtOk` says of the committed prefix `L` of the
snapshot `k`'s length, in a cluster that keeps a registry of the snapshots made: its last term is
`k`'s, `k`'s lists are well formed and denote the mode's configuration of `L` -- (2026-10-28, the
decision switch) its fold over the decisions `M`. -/
def SnapAtPure (γr : RaftNames) (k : SnapTrip) (L : List EntryM) (M : DecMap) : Prop :=
  γr.reSnapReg ≠ none → L.getLast?.map EntryM.Term' = some k.sid.term' ∧ SnapListsOk k ∧
    ∀ D, γr.dyn = some D → D.fold M L = some k.cfgM

/-- **The snapshot `k` is certified** for the cluster: raft's configuration certificate, and its
data what the cluster admits of a committed log as long as its index, which the client knows.
(2026-10-27) Only outside raft's no-snapshot mode (a dynamic cluster's: `readySnap_dynamic`).
(2026-10-28, stage U2) In a cluster that keeps a registry of the snapshots made
(`RaftNames.reSnapReg`), what raft's `snapAtOk` says, of the client's committed log, and the
registry's record of the snapshot (`snapRegOk`). -/
def snapshotCert (γ : Cluster) (_N : Namespace) (k : SnapTrip) : IProp GF :=
  iprop(⌜γ.raft.reNoSnap = false⌝ ∗ raftSnapCert γ.raft k ∗ ∃ (L : List EntryM) (M : DecMap),
    isCommittedLogLb γ (strip L) ∗ decLb γ.raft M ∗
    ⌜IdxOk L ∧ L.length = uint.nat k.sid.index' ∧ γ.raft.reSnapOk L k.dat ∧ SnapAtPure γ.raft k L M⌝ ∗
    snapRegOk γ.raft k.sid.index' k.dat)

instance snapshotCert_persistent (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    Persistent (snapshotCert (GF := GF) γ N k) := by
  unfold snapshotCert; infer_instance

instance snapshotCert_timeless (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    Timeless (snapshotCert (GF := GF) γ N k) := by
  unfold snapshotCert; infer_instance

theorem IdxOk_base {L : List EntryM} (H : IdxOk L) :
    ∀ (k : Nat) (e : EntryM), L[k]? = some e → uint.Z e.Index' = ((0 + k + 1 : Nat) : Int) := by
  intro k e Hk; rw [H k e Hk]; push_cast; omega

theorem snapshotCert_of_raft (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (Hns : γ.raft.reNoSnap = false) (k : SnapTrip) :
    ⊢ clusterInv (GF := GF) γ N -∗ raftSnapCertD γ.raft k ={E}=∗ snapshotCert γ N k := by
  iintro #Hci #Hk
  iunfold raftSnapCertD at Hk
  icases Hk with ⟨#Hc, #Hd⟩
  iunfold snapDataOk at Hd
  icases Hd with ⟨%L, #HL, %HLp, #Hreg⟩
  ihave #Hat : snapAtOk γ.raft k $$ []
  · iunfold raftSnapCert at Hc; icases Hc with ⟨-, -, -, #H⟩; iexact H
  ihave ⟨%M, #HM, %Hap⟩ : iprop(∃ M : DecMap, decLb γ.raft M ∗ ⌜SnapAtPure γ.raft k L M⌝) $$ []
  · iunfold snapAtOk at Hat
    icases Hat with (%Hn | ⟨%L', %M', #HL', #HM', %HL'p⟩)
    · iexists ∅
      isplitr; · iapply decLb_empty
      ipureintro; intro h; exact absurd Hn h
    · icases isCommitted_agree γ.raft L L' $$ HL HL' with %Hpre
      have HLL : L = L' := by
        rcases Hpre with h | h
        · exact h.eq_of_length (by rw [HLp.1, HL'p.1])
        · exact (h.eq_of_length (by rw [HLp.1, HL'p.1])).symm
      subst HLL
      iexists M'
      iframe HM'
      ipureintro; intro _; exact HL'p.2
  imod api_committed_lb γ N E HE L $$ Hci HL with ⟨#Hlb, %Hidx⟩
  imodintro
  unfold snapshotCert
  iframe Hc
  isplitr; · ipureintro; exact Hns
  iexists L, M
  iframe Hlb Hreg HM
  ipureintro; exact ⟨Hidx, HLp.1, HLp.2, Hap⟩

theorem raft_of_snapshotCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (k : SnapTrip) :
    ⊢ clusterInv (GF := GF) γ N -∗ snapshotCert γ N k ={E}=∗ raftSnapCertD γ.raft k := by
  iintro #Hci #Hk
  iunfold snapshotCert at Hk
  icases Hk with ⟨-, #Hc, %L, %M, #Hlb, -, %HL, #Hreg⟩
  imod api_lb_committed γ N E HE (strip L) $$ Hci Hlb with ⟨%D, %HD, #HDc⟩
  imod api_committed_lb γ N E HE D $$ Hci HDc with ⟨-, %HDi⟩
  have HDL : D = L := by
    rw [← toEntries_strip D 0 (IdxOk_base HDi), ← toEntries_strip L 0 (IdxOk_base HL.1), HD]
  subst HDL
  imodintro
  unfold raftSnapCertD snapDataOk
  iframe Hc
  iexists D
  iframe HDc Hreg
  ipureintro; exact ⟨HL.2.1, HL.2.2.1⟩

/-- **The storage's certificates are the cluster's** (the draft's `storageCertLink`). -/
def storageCertLink (γ : Cluster) (N : Namespace) (st : Storage) : IProp GF :=
  iprop(□ (∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ storCert st k ={E}=∗ snapshotCert γ N k) ∗
    □ (∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ snapshotCert γ N k ={E}=∗ storCert st k))

instance storageCertLink_persistent (γ : Cluster) (N : Namespace) (st : Storage) :
    Persistent (storageCertLink (GF := GF) γ N st) := by
  unfold storageCertLink; infer_instance

/-- Raft's certificate link (`storCertOk`), at the cluster's certificate namespace `N`. -/
theorem storCertOk_of_link (γ : Cluster) (N : Namespace) (st : Storage)
    (HN : γ.raft.reCertNs = N) (Hns : γ.raft.reNoSnap = false) :
    ⊢ clusterInv (GF := GF) γ N -∗ storageCertLink γ N st -∗ storCertOk γ.raft st := by
  iintro #Hci #Hl
  iunfold storageCertLink at Hl
  icases Hl with ⟨#H1, #H2⟩
  unfold storCertOk raftCertN
  rw [HN]
  isplitl []
  · imodintro
    iintro %k %E %HE #Hs
    imod H1 $$ %k %E %HE Hs with #Hc
    iapply raft_of_snapshotCert γ N E HE k $$ Hci Hc
  · imodintro
    iintro %k %E %HE #Hr
    imod snapshotCert_of_raft γ N E HE Hns k $$ Hci Hr with #Hc
    iapply H2 $$ %k %E %HE Hc

/-- What a registry entry of a `MemoryStorage` carries: the client's certificates of its snapshot,
at every term for an any-term entry. -/
def certElemApi (γ : Cluster) (N : Namespace) (e : CertKey) : IProp GF :=
  if e.2 then iprop(∀ t : w64, snapshotCert γ N ⟨⟨t, e.1.sid.index'⟩, e.1.cl, e.1.al, e.1.dat⟩)
  else snapshotCert γ N e.1

instance certElemApi_persistent (γ : Cluster) (N : Namespace) (e : CertKey) :
    Persistent (certElemApi (GF := GF) γ N e) := by
  unfold certElemApi; split <;> infer_instance

instance certElemApi_timeless (γ : Cluster) (N : Namespace) (e : CertKey) :
    Timeless (certElemApi (GF := GF) γ N e) := by
  unfold certElemApi; split <;> infer_instance

theorem certElemApi_covers (γ : Cluster) (N : Namespace) (e : CertKey) (k : SnapTrip)
    (h : certCovers e k) : certElemApi (GF := GF) γ N e ⊢ snapshotCert γ N k := by
  unfold certElemApi
  unfold certCovers at h
  split
  · rename_i he
    rw [if_pos he] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    iintro H
    ihave H := H $$ %k.sid.term'
    have : (⟨⟨k.sid.term', e.1.sid.index'⟩, e.1.cl, e.1.al, e.1.dat⟩ : SnapTrip) = k := by
      cases k with | mk sid cl al dat => cases sid; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl
    rw [this]; iexact H
  · rename_i he
    rw [if_neg he] at h
    subst h
    exact .rfl

/-- The registry invariant's namespace. -/
def certN (N : Namespace) : Namespace := N .@ "cert"

theorem certN_sub (N : Namespace) {E : CoPset} (HE : ↑N ⊆ E) : (↑(certN N) : CoPset) ⊆ E :=
  fun p hp => HE p (nclose_subseteq N "cert" p hp)

/-- **A `MemoryStorage`'s certificate registry tied to the cluster** (the draft's
`storageCertInv`). -/
def storageCertInv (γ : Cluster) (N : Namespace) (γs : MemStorNames) : IProp GF :=
  inv (certN N) iprop(∃ L : List CertKey, monoListAuthOwn γs.cert 1 L ∗
    [∗list] e ∈ L, certElemApi γ N e)

instance storageCertInv_persistent (γ : Cluster) (N : Namespace) (γs : MemStorNames) :
    Persistent (storageCertInv (GF := GF) γ N γs) := by
  unfold storageCertInv; infer_instance

theorem storageCertInv_alloc_impl (γ : Cluster) (N : Namespace) (γs : MemStorNames) (E : CoPset) :
    ⊢ memCertAuth (GF := GF) γs ={E}=∗ storageCertInv γ N γs := by
  iintro Ha
  unfold storageCertInv
  iapply inv_alloc
  inext
  iexists ([] : List CertKey)
  iunfold memCertAuth at Ha
  isplitl [Ha]
  · iexact Ha
  iapply (BigSepL.bigSepL_nil (Φ := fun _ e => certElemApi (GF := GF) γ N e)).2
  iempintro

theorem storageCert_read_impl (γ : Cluster) (N : Namespace) (γs : MemStorNames) (k : SnapTrip)
    (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ storageCertInv (GF := GF) γ N γs -∗ memStorCert γs k ={E}=∗ snapshotCert γ N k := by
  iintro #Hinv #Hc
  iunfold memStorCert at Hc
  icases Hc with ⟨%L0, #Hlb, %Hin⟩
  obtain ⟨e, he, hc⟩ := Hin
  unfold storageCertInv
  have hE' := certN_sub N hE
  iinv Hinv with ⟨%L, >Ha, >#Hall⟩ Hclose
  icases mono_list_auth_lb_valid _ _ _ _ $$ Ha Hlb with %Hv
  obtain ⟨-, Hpre⟩ := Hv
  have he' : e ∈ L := Hpre.subset he
  ihave ⟨#He, -⟩ := BigSepL.bigSepL_mem_acc he' $$ Hall
  ihave #Hk := certElemApi_covers γ N e k hc $$ He
  imod Hclose $$ [Ha] with -
  · inext
    iexists L
    iframe Ha Hall
  imodintro
  iexact Hk

theorem storageCert_register_impl (γ : Cluster) (N : Namespace) (γs : MemStorNames) (k : SnapTrip)
    (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ storageCertInv (GF := GF) γ N γs -∗ snapshotCert γ N k ={E}=∗ memStorCert γs k := by
  iintro #Hinv #Hk
  unfold storageCertInv
  have hE' := certN_sub N hE
  iinv Hinv with ⟨%L, >Ha, >#Hall⟩ Hclose
  imod monoListAuthOwn_update_app [((k, false) : CertKey)] $$ Ha with ⟨Ha, #Hlb⟩
  ihave #He : certElemApi (GF := GF) γ N ((k, false) : CertKey) $$ []
  · simp only [certElemApi, Bool.false_eq_true, ↓reduceIte]
    iexact Hk
  imod Hclose $$ [Ha] with -
  · inext
    iexists L ++ [((k, false) : CertKey)]
    iframe Ha
    iapply BigSepL.bigSepL_snoc.2
    iframe Hall He
  imodintro
  iapply memStorCert_of_lb γs (L ++ [((k, false) : CertKey)]) (k, false) k (by simp)
    (by simp [certCovers]) $$ Hlb

theorem storageCert_registerAny_impl (γ : Cluster) (N : Namespace) (γs : MemStorNames) (i : w64)
    (cl : CSLists) (al : Bool) (d : List w8) (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ storageCertInv (GF := GF) γ N γs -∗ (□ ∀ t : w64, snapshotCert γ N ⟨⟨t, i⟩, cl, al, d⟩) ={E}=∗
      □ ∀ t : w64, memStorCert γs ⟨⟨t, i⟩, cl, al, d⟩ := by
  iintro #Hinv #Hk
  unfold storageCertInv
  have hE' := certN_sub N hE
  iinv Hinv with ⟨%L, >Ha, >#Hall⟩ Hclose
  imod monoListAuthOwn_update_app [((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey)] $$ Ha
    with ⟨Ha, #Hlb⟩
  ihave #He : certElemApi (GF := GF) γ N ((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey) $$ []
  · simp only [certElemApi, ↓reduceIte]
    iexact Hk
  imod Hclose $$ [Ha] with -
  · inext
    iexists L ++ [((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey)]
    iframe Ha
    iapply BigSepL.bigSepL_snoc.2
    iframe Hall He
  imodintro
  imodintro
  iintro %t
  iapply memStorCert_of_lb γs (L ++ [((⟨⟨W64 0, i⟩, cl, al, d⟩, true) : CertKey)])
    (⟨⟨W64 0, i⟩, cl, al, d⟩, true) ⟨⟨t, i⟩, cl, al, d⟩ (by simp) (by simp [certCovers]) $$ Hlb

theorem storageCertLink_intro_impl (γ : Cluster) (N : Namespace) (st : Storage) :
    (□ ∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ storCert st k ={E}=∗
        snapshotCert (GF := GF) γ N k) ∗
      (□ ∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ snapshotCert γ N k ={E}=∗ storCert st k) ⊢
      storageCertLink γ N st := by
  unfold storageCertLink; exact .rfl

/-- What a certified snapshot's data is, in a static cluster. -/
theorem snapshotCert_data_impl (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (k : SnapTrip) :
    isStaticCluster (GF := GF) γ N vs snapOk ∗ snapshotCert γ N k ⊢
      ∃ l, isCommittedLogLb γ l ∗ ⌜l.length = uint.nat k.sid.index' ∧ snapOk l k.dat⌝ := by
  unfold isStaticCluster snapshotCert
  iintro ⟨⟨%Hst, -⟩, -, -, %L, %M, #Hlb, -, %HL, -⟩
  iexists strip L
  iframe Hlb
  ipureintro
  exact ⟨by rw [strip_length]; exact HL.2.1,
    (reSnapOk_sokOf γ.raft snapOk Hst.2.2.2.1 L k.dat).1 HL.2.2.1⟩

theorem toEntries_idx (l : List LogEntry) (Hl : l.length < 2 ^ 64) :
    IdxOk (LogEntry.toEntries l 0) := by
  intro k e Hk
  rw [toEntries_getElem?] at Hk
  cases hb : l[k]? with
  | none => rw [hb] at Hk; cases Hk
  | some e0 =>
    rw [hb] at Hk
    simp only [Option.map_some, Option.some.injEq] at Hk
    subst Hk
    have hk : k < l.length := (List.getElem?_eq_some_iff.mp hb).1
    show uint.Z (W64 ((0 + k + 1 : Nat) : Int)) = _
    have : ((0 + k + 1 : Nat) : Int) < 2 ^ 64 := by omega
    rw [uint_Z_W64 _ (by omega) this]
    push_cast; omega

/-- Certifying a snapshot of a static cluster, at any term. -/
theorem snapshotCert_static_impl (γ : Cluster) (N : Namespace) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (l : List LogEntry) (i : w64) (d : List w8) :
    (∀ t : w64, SnapListsOk ⟨⟨t, i⟩, ⟨vs, [], [], []⟩, false, d⟩) →
    l.length = uint.nat i → snapOk l d →
    isStaticCluster (GF := GF) γ N vs snapOk ∗ isCommittedLogLb γ l ⊢
      □ ∀ t : w64, snapshotCert γ N ⟨⟨t, i⟩, ⟨vs, [], [], []⟩, false, d⟩ := by
  intro Hok Hl Hso
  unfold isStaticCluster
  iintro ⟨⟨%Hst, -⟩, #Hlb⟩
  obtain ⟨Hcfg, Hdyn, Hns, Hsok, -, -, -, Hreg, Htrk, -⟩ := Hst
  have Hlen : l.length < 2 ^ 64 := by have := word.unsigned_range i; rw [Hl]; word
  imodintro
  iintro %t
  unfold snapshotCert
  isplitr; · ipureintro; exact Hns
  isplitl []
  · iapply raftSnapCert_static γ.raft _ (by unfold RaftNames.dyn; rw [Hdyn]; rfl) (Hok t) (hr := Hreg)
    intro _
    refine ⟨Hcfg.symm, rfl, ?_⟩
    intro T hT
    rcases Htrk with h | h
    · rw [h] at hT; cases hT
    · rw [h] at hT; cases hT
      apply (GMap.union_subseteq _ _ _).2
      refine ⟨(GMap.union_subseteq _ _ _).2 ⟨GMap.subseteq_refl _, GMap.empty_subseteq _⟩,
        GMap.empty_subseteq _⟩
  iexists LogEntry.toEntries l 0, ∅
  rw [strip_toEntries]
  iframe Hlb
  isplitr; · iapply decLb_empty
  isplitr
  · ipureintro
    refine ⟨toEntries_idx l Hlen, by rw [toEntries_length]; exact Hl, ?_, fun h => absurd Hreg h⟩
    rw [reSnapOk_sokOf γ.raft snapOk Hsok, strip_toEntries]
    exact Hso
  iapply snapRegOk_none Hreg

end cert

/-! ## The nodes -/

/-! ## A channel receive's update, with a fancy update after it

(`recvAu_wand` with an update at `⊤` in the wand: every commit of a receive ends at `⊤`.) -/

section recvFupd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable (γc : ChanNames) (V : Type) [Pos.Countable V] [ZeroVal V]

theorem recvNestedAu_wand_fupd (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ recvNestedAu γc V Φ1 -∗ (∀ v ok, Φ1 v ok ={⊤}=∗ Φ2 v ok) -∗ recvNestedAu γc V Φ2 := by
  unfold recvNestedAu
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals first
    | (iintro H; imod Hcont $$ H with H; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

theorem recvAu_wand_fupd (Φ1 Φ2 : V → Bool → IProp GF) :
    ⊢ recvAu γc V Φ1 -∗ (∀ v ok, Φ1 v ok ={⊤}=∗ Φ2 v ok) -∗ recvAu γc V Φ2 := by
  unfold recvAu
  iintro Hau Hw
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  case Idle =>
    iintro H
    imod Hcont $$ H with H
    imodintro
    iapply recvNestedAu_wand_fupd $$ H Hw
  all_goals first
    | (iintro H; imod Hcont $$ H with H; iapply Hw $$ H)
    | iexact Hcont
    | itrivial

end recvFupd

section node
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What a node's names say of it: of the cluster's names and budget, with no snapshot directory,
in the cluster's mode (`Cluster.mode`), taking snapshots from the network unless the cluster is in
raft's no-snapshot mode. (2026-10-27: until then in the static mode, taking snapshots.) -/
def NodeOk (γ : Cluster) (γn : NodeNames) : Prop :=
  γn.raft = γ.raft ∧ γn.bud = γ.bud ∧ γ.raft.reSnapLoc = (fun _ => none) ∧
    γn.mode = γ.mode inferInstance ∧ (γn.snapIn = true ∨ γ.raft.reNoSnap = true)

/-- The configuration names of a node's `NodeNames` (`Cluster.nodeTab`); (2026-10-29, stage U9a) and its
`live` name, by which `nodeLive` and `nodeStopped` agree. -/
abbrev CfgNames := GName × GName × GName × GName × GName

def cfgNamesOf (γn : NodeNames) : CfgNames := (γn.dlm, γn.cap, γn.ccq, γn.cam, γn.live)

/-- **Node `id`'s configuration names are `γn`'s** (persistent): the entry of its table. -/
def nodeTabOk (γ : Cluster) (id : w64) (γn : NodeNames) : IProp GF :=
  iprop(∃ g : GName, ⌜γ.nodeTab !! id = some g⌝ ∗ id ↪[g]□ (cfgNamesOf γn))

instance nodeTabOk_persistent (γ : Cluster) (id : w64) (γn : NodeNames) :
    Persistent (nodeTabOk (GF := GF) γ id γn) := by
  unfold nodeTabOk; infer_instance

theorem nodeTabOk_agree (γ : Cluster) (id : w64) (γ1 γ2 : NodeNames) :
    ⊢ nodeTabOk (GF := GF) γ id γ1 -∗ nodeTabOk γ id γ2 -∗ ⌜(cfgNamesOf γ1) = (cfgNamesOf γ2)⌝ := by
  unfold nodeTabOk
  iintro ⟨%g1, %H1, #E1⟩ ⟨%g2, %H2, #E2⟩
  rw [H1] at H2; cases H2
  iapply ghostMapElem_agree $$ E1 E2

/-- The driver's view of the configuration depends on the configuration names only. -/
theorem nodeCfg_names (γ1 γ2 : NodeNames) (H : (cfgNamesOf γ1) = (cfgNamesOf γ2)) (ca : Nat)
    (cfg : CCState) : nodeCfg (GF := GF) γ1 ca cfg ⊢ nodeCfg γ2 ca cfg := by
  simp only [cfgNamesOf, Prod.mk.injEq] at H
  obtain ⟨-, h2, h3, h4, -⟩ := H
  unfold nodeCfg; rw [h2, h3, h4]

theorem dlvLb_names (γ1 γ2 : NodeNames) (H : (cfgNamesOf γ1) = (cfgNamesOf γ2)) (ds : List EntryM) :
    dlvLb (GF := GF) γ1 ds ⊢ dlvLb γ2 ds := by
  simp only [cfgNamesOf, Prod.mk.injEq] at H
  unfold dlvLb; rw [H.1]

/-- Raft's nodes at one location have one id (`isNode`'s persistent points-to's). -/
theorem isNode_id_agree (γ1 γ2 : NodeNames) (id1 id2 : w64) (n : Loc) :
    ⊢ EtcdGrove.isNodeChan (GF := GF) γ1 id1 n -∗ EtcdGrove.isNodeChan γ2 id2 n -∗ ⌜id1 = id2⌝ := by
  iintro H1 H2
  iunfold EtcdGrove.isNodeChan at H1 H2
  icases H1 with ⟨%nv1, %r1, %lok1, H1⟩
  icases H2 with ⟨%nv2, %r2, %lok2, H2⟩
  icases H1 with ⟨#Hn1, #Hr1, #Hi1, -⟩
  icases H2 with ⟨#Hn2, #Hr2, #Hi2, -⟩
  icombine Hn1 Hn2 gives %Hnv
  subst Hnv
  icombine Hr1 Hr2 gives %Hr
  subst Hr
  icombine Hi1 Hi2 gives %Hi
  ipureintro; exact Hi

/-- **A running node** `n` of id `id` in the cluster `γ` (persistent): raft's node, of the
cluster's names and budget (`NodeOk`), and the cluster's invariants. -/
def isNode (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(∃ γn : NodeNames, ⌜NodeOk γ γn⌝ ∗ EtcdGrove.isNodeChan γn id n ∗ clusterInv γ N)

instance isNode_persistent (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) :
    Persistent (isNode (GF := GF) n γ N id) := by
  unfold isNode; infer_instance

/-- (2026-10-29, stage U9a) **The node runs**, a share `q` of the client's token (`q = 1`: the
whole, which `node.Stop` takes): raft's node `n` with the client's half of `live` (`nodeLiveRaw`).
Only a node of a dynamic cluster, whose table (`nodeTabOk`) names its `live` name, so that this and
`nodeStopped` agree on the node's names (`nodeRunning_stopped_impl`, `nodeRunning_split_impl`):
nothing else makes two `isNodeChan`s of one location name the same ghost state. -/
def nodeRunning (n : Loc) (γ : Cluster) (_N : Namespace) (q : Qp) : IProp GF :=
  iprop(∃ (γn : NodeNames) (id : w64), ⌜NodeOk γ γn ∧ γn.mode.isDyn = true⌝ ∗
    EtcdGrove.isNodeChan γn id n ∗ nodeTabOk γ id γn ∗ EtcdGrove.nodeLiveRaw γn q)

/-- (2026-10-29, stage U9a) **The node stopped** (persistent): `run` closed `done`
(`nodeStoppedRaw`). For a dynamic cluster's node, of the names its table names (`nodeTabOk`), so that
it excludes the node's running (`nodeRunning_stopped_impl`); (temporary, until the static clusters
go in U9) for a static one's, of some names of the node. -/
def nodeStopped (n : Loc) (γ : Cluster) (_N : Namespace) : IProp GF :=
  iprop(∃ (γn : NodeNames) (id : w64), ⌜NodeOk γ γn⌝ ∗ EtcdGrove.isNodeChan γn id n ∗
    (⌜γn.mode.isDyn = false⌝ ∨ nodeTabOk γ id γn) ∗ EtcdGrove.nodeStoppedRaw γn)

instance nodeStopped_persistent (n : Loc) (γ : Cluster) (N : Namespace) :
    Persistent (nodeStopped (GF := GF) n γ N) := by
  unfold nodeStopped; infer_instance

/-- Two dynamic nodes' names at one location, of one cluster's table, have one `live` name. -/
theorem nodeNames_live_agree (γ : Cluster) (γ1 γ2 : NodeNames) (id1 id2 : w64) (n : Loc) :
    ⊢ EtcdGrove.isNodeChan (GF := GF) γ1 id1 n -∗ nodeTabOk γ id1 γ1 -∗
      EtcdGrove.isNodeChan γ2 id2 n -∗ nodeTabOk γ id2 γ2 -∗ ⌜γ1.live = γ2.live⌝ := by
  iintro #H1 #T1 #H2 #T2
  ihave %Hid := isNode_id_agree γ1 γ2 id1 id2 n $$ H1 H2
  subst Hid
  ihave %Hn := nodeTabOk_agree γ id1 γ1 γ2 $$ T1 T2
  simp only [cfgNamesOf, Prod.mk.injEq] at Hn
  ipureintro; exact Hn.2.2.2.2

theorem nodeRunning_stopped_impl (n : Loc) (γ : Cluster) (N : Namespace) (q : Qp) :
    nodeRunning (GF := GF) n γ N q ∗ nodeStopped n γ N ⊢ False := by
  unfold nodeRunning nodeStopped
  iintro ⟨⟨%γ1, %id1, %Hok1, #H1, #T1, Hl⟩, ⟨%γ2, %id2, %Hok2, #H2, Hd, #Hs⟩⟩
  have Hm : γ2.mode.isDyn = true := by rw [Hok2.2.2.2.1, ← Hok1.1.2.2.2.1]; exact Hok1.2
  icases Hd with (%Hd | #T2)
  · rw [Hm] at Hd; cases Hd
  ihave %Hlv := nodeNames_live_agree γ γ1 γ2 id1 id2 n $$ H1 T1 H2 T2
  unfold EtcdGrove.nodeLiveRaw EtcdGrove.nodeStoppedRaw
  rw [Hlv]
  ihave %H := dghostVar_agree _ _ _ _ _ $$ Hl Hs
  cases H

theorem nodeRunning_split_impl (n : Loc) (γ : Cluster) (N : Namespace) (p q : Qp) :
    nodeRunning (GF := GF) n γ N (p + q) ⊣⊢ nodeRunning n γ N p ∗ nodeRunning n γ N q := by
  unfold nodeRunning
  constructor
  · iintro ⟨%γ1, %id1, %Hok1, #H1, #T1, Hl⟩
    icases (EtcdGrove.nodeLiveRaw_fractional (GF := GF) γ1).fractional p q |>.1 $$ Hl with ⟨Hl1, Hl2⟩
    isplitl [Hl1]
    · iexists γ1, id1; iframe Hl1 H1 T1; ipureintro; exact Hok1
    · iexists γ1, id1; iframe Hl2 H1 T1; ipureintro; exact Hok1
  · iintro ⟨⟨%γ1, %id1, %Hok1, #H1, #T1, Hl1⟩, ⟨%γ2, %id2, %Hok2, #H2, #T2, Hl2⟩⟩
    ihave %Hlv := nodeNames_live_agree γ γ1 γ2 id1 id2 n $$ H1 T1 H2 T2
    iexists γ1, id1
    iframe H1 T1
    isplitr
    · ipureintro; exact Hok1
    iapply ((EtcdGrove.nodeLiveRaw_fractional (GF := GF) γ1).fractional p q).2
    iframe Hl1
    iunfold EtcdGrove.nodeLiveRaw at Hl2
    unfold EtcdGrove.nodeLiveRaw
    rw [Hlv]
    iexact Hl2

/-- The node's `Ready` channel `ch` (persistent): the node struct's `readyc`. -/
def isReadyChan (n : Loc) (_γ : Cluster) (_N : Namespace) (ch : Loc) : IProp GF :=
  iprop(∃ nv : node, n ↦□ nv ∗ ⌜ch = nv.readyc'⌝)

instance isReadyChan_persistent (n : Loc) (γ : Cluster) (N : Namespace) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) n γ N ch) := by
  unfold isReadyChan; infer_instance

/-- **The `Ready` loop's token**: raft's driver token (idle, or busy with a `Ready`) at the raft
log `ds` the client sees as `st.delivered`, which is committed. A static node's also holds the
storage's certificate link and raft's view of the configuration (`nodeCfg`), which never moves; a
dynamic node's (2026-10-27) its configuration names (`nodeTabOk`: its view of the configuration is
`nodeConfig`, which the application holds apart), the witness of its hard state
(`hsCommitted`) and (2026-10-28, stage U3d) outside raft's no-snapshot mode the storage's certificate
link. -/
def nodeDriver (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) : IProp GF :=
  iprop(∃ (γn : NodeNames) (id : w64) (ds : List EntryM),
    ⌜NodeOk γ γn ∧ γn.stor = st.storage ∧ strip ds = st.delivered⌝ ∗ clusterInv γ N ∗
    isCommittedLogLb γ st.delivered ∗
    (⌜γn.mode.isDyn = true⌝ ∨
      storageCertLink γ N st.storage ∗ ∃ (ca : Nat) (cfg : CCState), nodeCfg γn ca cfg) ∗
    (⌜γn.mode.isDyn = false⌝ ∨
      nodeTabOk γ id γn ∗ hsCommitted γ N st.hardState st.delivered.length ∗
      (⌜γ.raft.reNoSnap = true⌝ ∨ storageCertLink γ N st.storage)) ∗
    ((⌜st.handling = none⌝ ∗ EtcdGrove.nodeDriverChan γn id n ds st.hardState) ∨
     (∃ (es : List EntryM) (L : Option SnapLoan), ⌜st.handling = some (es, L)⌝ ∗
       nodeDriverBusy γn id n ds es st.hardState L)))

/-- A sent message's snapshot, if it is a `MsgSnap`, is certified (`snapshotCert`). -/
def sentSnapCert (γ : Cluster) (N : Namespace) (st : MsgSt) : IProp GF :=
  iprop(⌜st.msg.Type' ≠ MsgSnap⌝ ∨
    ∃ sv, ⌜st.snap = some sv⌝ ∗ snapshotCert γ N (snapTrip sv sv.Metadata'.ConfState'.lists))

instance sentSnapCert_persistent (γ : Cluster) (N : Namespace) (st : MsgSt) :
    Persistent (sentSnapCert (GF := GF) γ N st) := by
  unfold sentSnapCert; infer_instance

/-- (open) **A message node `src`'s `Ready` handed out**: sent by that node of the cluster, of a
term within the cluster's budget; (2026-10-27) a `MsgSnap`'s snapshot certified for the client
(`sentMsg_snapshot`). -/
def sentMsg (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) : IProp GF :=
  iprop(clusterInv γ N ∗ isRaftMsg γ.raft src st ∗ termLB γ.bud st.msg.Term' ∗
    sentSnapCert γ N st)

instance sentMsg_persistent (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    Persistent (sentMsg (GF := GF) γ N src st) := by
  unfold sentMsg; infer_instance

/-- In the no-transfer mode, a sent message has the shape `SentMsgOk`. -/
theorem sentMsg_transferOff_impl (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    leaderTransferOff (GF := GF) γ N ∗ sentMsg γ N src st ⊢ ⌜SentMsgOk st⌝ := by
  unfold leaderTransferOff sentMsg isRaftMsg
  iintro ⟨%Hx, -, ⟨-, %Hok, -⟩, -⟩
  ipureintro; exact Hok Hx

omit [StorageModel GF] sem package_sem in
/-- A sent `MsgSnap` carries a certified snapshot (the draft's `sentMsg_snapshot`). -/
theorem sentMsg_snapshot_impl (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    st.msg.Type' = MsgSnap →
    sentMsg (GF := GF) γ N src st ⊢
      ∃ sv, ⌜st.snap = some sv⌝ ∗ snapshotCert γ N (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  intro Hty
  unfold sentMsg sentSnapCert
  iintro ⟨-, -, -, (%Hn | H)⟩
  · exact absurd Hty Hn
  · iexact H

/-- A message's snapshot certificate, from raft's (`isRaftMsg`'s abstraction and data
certificate). -/
theorem api_sentSnapCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (src : w64)
    (st : MsgSt) :
    ⊢ clusterInv (GF := GF) γ N -∗ isRaftMsg γ.raft src st ={E}=∗ sentSnapCert γ N st := by
  iintro #Hci #Hraft
  unfold sentSnapCert
  by_cases Hty : st.msg.Type' = MsgSnap
  rotate_left
  · imodintro; ileft; ipureintro; exact Hty
  ihave #Hdat := isRaftMsg_dat γ.raft src st $$ Hraft
  iunfold isRaftMsg at Hraft
  icases Hraft with ⟨%Hns0, -, ⟨%a, %Habs, #Hl⟩, -, -⟩
  have Hms : mtypeOf st.msg.Type' = some .snap := by rw [Hty]; exact mtypeOf_MsgSnap
  rcases Habs with ⟨Hn, -⟩ | ⟨ty0, Hty0, Hne0, -⟩ | ⟨sv, -, Hsv, rfl⟩
  · rw [Hn] at Hms; cases Hms
  · rw [Hty0] at Hms; cases Hms; exact absurd rfl Hne0
  have Hns : γ.raft.reNoSnap = false := by
    cases h : γ.raft.reNoSnap
    · rfl
    · exact absurd Hty (Hns0 h)
  simp only [Option.toList_some]
  ihave #Hx := (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessageC (GF := GF) γ.raft x)).1 $$ Hl
  ihave #Hc := isMessageC_snap_cert γ.raft _ rfl $$ Hx
  iunfold msgDat at Hdat
  ihave #Hd := Hdat $$ %sv %(⟨Hty, Hsv⟩ : st.msg.Type' = MsgSnap ∧ st.snap = some sv)
  ihave #HD : raftSnapCertD γ.raft (snapTrip sv sv.Metadata'.ConfState'.lists) $$ []
  · unfold raftSnapCertD
    isplitr
    · iExactEq Hc
      unfold raftSnapCert; rfl
    · iExactEq Hd
      rfl
  imod snapshotCert_of_raft γ N E HE Hns _ $$ Hci HD with #Hk
  imodintro
  iright
  iexists sv
  iframe Hk
  ipureintro; exact Hsv

/-- A `MsgApp` is from the node that sent it (`AppFrom`). -/
theorem sentMsg_appFrom_impl (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt) :
    sentMsg (GF := GF) γ N src st ⊢ ⌜AppFrom src st⌝ := by
  unfold sentMsg isRaftMsg
  iintro ⟨-, ⟨-, -, -, -, %H⟩, -⟩
  ipureintro; exact H.2

/-- (open) **What a sent message carries for its receiver's `Step`.** -/
def msgCredits (γ : Cluster) (_N : Namespace) (st : MsgSt) : IProp GF :=
  iprop(rdCred γ.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ stTks γ.raft st)

/-- (open) A `Ready`'s storage part (the draft's `readySnap`). -/
def readySnap (γ : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) : Option SnapLoan → IProp GF
  | none => iprop(⌜rd.Snapshot' = null⌝ ∗ appendRight st.storage es)
  | some l => iprop(
      ⌜l.dlv = LogEntry.toEntries (strip l.dlv) 0 ∧ l.ptr = rd.Snapshot' ∧ ce = [] ∧
        st.delivered <+: strip l.dlv ∧ st.delivered.length < l.dlv.length ∧
        l.dlv.length = uint.nat l.snap.Metadata'.Index' ∧ 0 < uint.Z l.snap.Metadata'.Index' ∧
        uint.Z l.snap.Metadata'.Index' < 2 ^ 61 ∧ uint.Z l.fl ≤ uint.Z l.snap.Metadata'.Index' ∧
        LogIndicesOk (snapId l.snap) es⌝ ∗
      ownSnapS l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommittedLogLb γ (strip l.dlv) ∗
      snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) ∗
      readyOut st.storage es (some l))

/-- (open) **The rest of a `Ready`** (the draft's `readyRest`). -/
def readyRest (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) : IProp GF :=
  iprop(∃ ms : List QMsg,
    entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N id q.st ∗
      msgCredits γ N q.st) ∗
    hsOpt rd.HardState' h ∗ softStateRO rd.SoftState' ∗
    ⌜∃ Lx : Int, Lx < 2 ^ 64 ∧
      (∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ Lx + 1) ∧
      ((st.delivered ++ ce).length : Int) ≤ Lx ∧
      Lx < (receiptBound GF : Int) + γ.raft.reBoot.length⌝ ∗
    readySnap γ N rd st ce es L)

/-- What receiving a `Ready` gives (`node.readyRecv.spec`'s postcondition). -/
abbrev readyPost (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState)
    (rd : Ready) : IProp GF :=
  iprop(∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan),
        committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
        isCommittedLogLb γ (st.delivered ++ ce) ∗
        (∃ rs, readStatesPts rd.ReadStates' rs ∗
          [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
        readyRest γ N id rd st ce es h L ∗
        nodeDriver n γ N (match L with
          | none => { st with
              delivered := st.delivered ++ ce
              hardState := phsNext st.hardState h
              handling := some (es, none) }
          | some l => { st with
              delivered := strip l.dlv
              hardState := phsNext st.hardState h
              handling := some (es, some l) }))

/-- **Receiving a `Ready`** (the draft's `node.readyRecv`). -/
abbrev node.readyRecv.spec : Prop :=
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState),
  st.handling = none →
  {{ isReadyChan (GF := GF) n γ N ch ∗ isNode n γ N id ∗ nodeDriver n γ N st }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true); readyPost n γ N id st rd }}

/-- A message a `Ready` hands out, as the client sees it. -/
theorem api_msg (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (γn : NodeNames)
    (Hγr : γn.raft = γ.raft) (Hγb : γn.bud = γ.bud) (q : QMsg) :
    ⊢ clusterInv (GF := GF) γ N -∗
      (msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γn.raft γn.id q.st ∗
        termLB γn.bud q.st.msg.Term') -∗
      rdCred γn.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0) -∗
      stTks γn.raft q.st ={E}=∗
      msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N γn.id q.st ∗ msgCredits γ N q.st := by
  iintro #Hci ⟨Ho, #Hraft, #Htlb⟩ Hcr Htk
  ihave #Hraft' : isRaftMsg γ.raft γn.id q.st $$ []
  · rw [← Hγr]; iexact Hraft
  imod api_sentSnapCert γ N E HE γn.id q.st $$ Hci Hraft' with #Hsc
  imodintro
  iframe Ho
  unfold sentMsg msgCredits
  rw [← Hγr, ← Hγb]
  iframe Hci Htlb Hcr Htk Hraft Hsc

/-- The messages a `Ready` hands out, as the client sees them. -/
theorem api_msgs (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (γn : NodeNames)
    (Hγr : γn.raft = γ.raft) (Hγb : γn.bud = γ.bud) (ms : List QMsg) :
    ⊢ clusterInv (GF := GF) γ N -∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γn.raft γn.id q.st ∗
        termLB γn.bud q.st.msg.Term') -∗
      ([∗list] q ∈ ms, rdCred γn.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) -∗
      ([∗list] q ∈ ms, stTks γn.raft q.st) ={E}=∗
      [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N γn.id q.st ∗
        msgCredits γ N q.st := by
  induction ms with
  | nil =>
    iintro #_ - - -
    imodintro
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (q : QMsg) => iprop(msgOwn (GF := GF) q.loc
      (readyDq q.st) q.st ∗ sentMsg γ N γn.id q.st ∗ msgCredits γ N q.st))).2
    iempintro
  | cons q ms ih =>
    iintro #Hci Hmo Hcr Htks
    icases BigSepL.bigSepL_cons.1 $$ Hmo with ⟨Hm1, Hmo⟩
    icases BigSepL.bigSepL_cons.1 $$ Hcr with ⟨Hc1, Hcr⟩
    icases BigSepL.bigSepL_cons.1 $$ Htks with ⟨Ht1, Htks⟩
    imod api_msg γ N E HE γn Hγr Hγb q $$ Hci Hm1 Hc1 Ht1 with H1
    imod ih $$ Hci Hmo Hcr Htks with H
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe H1 H

theorem readyOut_cert (st : Storage) (es : List EntryM) (l : SnapLoan) :
    readyOut (GF := GF) st es (some l) ⊢
      readyOut st es (some l) ∗ storCert st (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) := by
  simp only [readyOut]
  iintro ⟨Hs, #Hc⟩
  isplitl [Hs]
  · iframe Hs Hc
  · iexact Hc

/-- **Receiving a `Ready`, opened**: the node's raft channel and driver token, and the update
from what raft's receive gives to `readyPost`. -/
theorem readyRecv_open (n ch : Loc) (γ : Cluster) (N : Namespace) (id0 : w64)
    (st : NodeDriverState) (Hh : st.handling = none) :
    ⊢ isReadyChan (GF := GF) n γ N ch -∗ isNode n γ N id0 -∗ nodeDriver n γ N st -∗
      ∃ (γn : NodeNames) (id : w64) (ds : List EntryM),
        EtcdGrove.isReadyChanRaw γn ch ∗ EtcdGrove.nodeDriverChan γn id n ds st.hardState ∗
        (∀ rd : Ready, (∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM)
            (L : Option SnapLoan), readyDataL γn rd ds ce es ms st.hardState p' L ∗
            nodeDriverBusy γn id n (dlvAfter ds ce L) es p' L) ={⊤}=∗
          readyPost n γ N id0 st rd) := by
  iintro #Hrc #Hnode0 Hdrv
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, #Hlb0, Hst, #Hdy, Htok⟩
  obtain ⟨Hnok, Hγs, Hds⟩ := Hf
  have Hγr := Hnok.1
  have Hγb := Hnok.2.1
  icases Htok with (⟨-, Htok⟩ | ⟨%es0, %L0, %Hh', -⟩)
  rotate_left
  · rw [Hh] at Hh'; cases Hh'
  ihave ⟨Htok, #Hnode⟩ := nodeDriver_isNode γn id n ds st.hardState $$ Htok
  ihave %Hid0 : ⌜γn.id = id0⌝ $$ []
  · iunfold isNode at Hnode0
    icases Hnode0 with ⟨%γn0, -, #Hn0', -⟩
    icases isNode_id_agree γn γn0 id id0 n $$ Hnode Hn0' with %He
    ihave #Hn1 := Hnode
    iunfold EtcdGrove.isNodeChan at Hn1
    icases Hn1 with ⟨%nv1, %r1, %lok1, #Hn1⟩
    iNamed Hn1
    ipureintro; rw [Hgid]; exact He
  iunfold isReadyChan at Hrc
  icases Hrc with ⟨%nv, #Hn0, %Hch⟩
  ihave #Hnode' := Hnode
  iunfold EtcdGrove.isNodeChan at Hnode'
  icases Hnode' with ⟨%nv', %r, %lok, #Hnode'⟩
  iNamed Hnode'
  icombine Hn0 Hn gives %Hnv
  subst Hnv
  ihave #Hrc' : EtcdGrove.isReadyChanRaw γn ch $$ []
  · unfold EtcdGrove.isReadyChanRaw; rw [Hch]; iexact Hreadyc
  have Hlen : st.delivered.length = ds.length := by rw [← Hds, strip_length]
  iexists γn, id, ds
  iframe Hrc' Htok
  iintro %rd ⟨%ce, %es, %ms, %p', %L, Hdata, Hbusy⟩
  cases L with
  | none =>
    iunfold readyDataL at Hdata
    iunfold readyData at Hdata
    icases Hdata with ⟨#Hce, #Hcom, #Hes, Happ, Hmsgs, Hmo, Hcr, Htks, ⟨%sts, Hsts, Hrs⟩,
      ⟨%h, Hhs, %Hp'⟩, #Hhw, Hss, %Hnull, #Hidx⟩
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top (ds ++ ce) $$ Hci [Hcom] with ⟨#Hlb, %HidxOk⟩
    · rw [Hγr]; iexact Hcom
    imod hsCommitted_of_raft γ N ⊤ CoPset.subseteq_top p' (ds ++ ce).length $$ Hci [Hhw] with #Hhc
    · rw [← Hγr]; iexact Hhw
    imod api_readStates γ N ⊤ CoPset.subseteq_top sts $$ Hci [Hrs] with Hrs
    · rw [← Hγr]; iexact Hrs
    imod api_msgs γ N ⊤ CoPset.subseteq_top γn Hγr Hγb ms $$ Hci Hmo Hcr Htks with Hms
    rw [Hid0]
    iunfold readyIdx at Hidx
    icases Hidx with ⟨%Lx, #Hlr, %HLx⟩
    imod lastRec_receipt γn.raft Lx $$ Hlr with #Hrc
    ihave %Hrl := preceipt_lt _ $$ Hrc
    imodintro
    iexists strip ce, es, h, none
    have Hce : LogEntry.toEntries (strip ce) st.delivered.length = ce := by
      apply toEntries_strip
      intro k e Hk
      have := HidxOk (ds.length + k) e
        (by rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact Hk)
      rw [this, Hlen]; push_cast; omega
    isplitl []
    · unfold committedEntriesAt; rw [Hce]; iexact Hce
    isplitl []
    · rw [← Hds, ← strip_append]; iexact Hlb
    isplitl [Hsts Hrs]
    · iexists sts; iframe Hsts Hrs
    isplitl [Hes Happ Hmsgs Hms Hhs Hss]
    · unfold readyRest
      iexists ms
      iframe Hes Hmsgs Hms Hhs Hss
      isplitr
      · ipureintro
        refine ⟨Lx, HLx.1, HLx.2.1, ?_, by rw [← Hγr]; omega⟩
        have := HLx.2.2
        simp only [List.length_append, strip_length] at this ⊢
        omega
      unfold readySnap
      isplitr
      · ipureintro; exact Hnull
      rw [← Hγs]; iexact Happ
    unfold nodeDriver
    dsimp only
    iexists γn, id, ds ++ ce
    isplitr
    · ipureintro
      exact ⟨Hnok, Hγs, by rw [strip_append, Hds]⟩
    iframe Hci Hst
    isplitr
    · rw [← Hds, ← strip_append]; iexact Hlb
    isplitr
    · icases Hdy with (%Hd | ⟨#Htab, -, #Hcl⟩)
      · ileft; ipureintro; exact Hd
      iright
      iframe Htab Hcl
      have HL : (st.delivered ++ strip ce).length = (ds ++ ce).length := by
        simp only [List.length_append, strip_length, Hlen]
      rw [HL, ← Hp']
      iexact Hhc
    iright
    iexists es, none
    isplitr
    · ipureintro; rfl
    rw [← Hp', show ds ++ ce = dlvAfter ds ce none from rfl]; iexact Hbusy
  | some l =>
    iunfold readyDataL at Hdata
    iunfold readySnapData at Hdata
    icases Hdata with ⟨#Hce, #Hcom, #Hes, Hmsgs, Hmo, Hcr, Htks, ⟨%sts, Hsts, Hrs⟩,
      ⟨%h, Hhs, %Hp'⟩, -, Hss, #Hidx, %Hsf, Hsnap, #Hdlv, -, -, %Hfacts, Hout⟩
    obtain ⟨Hptr, Hce0, Hpre, Hlt, Hdl, Hpos, H61, Hfl, Hind⟩ := Hfacts
    subst Hce0
    -- (2026-10-28, stage U3d) the storage's certificate link, in either mode (dynamically, outside
    -- the no-snapshot mode, which a snapshot `Ready` is in)
    ihave ⟨#Hlink, Hst⟩ : storageCertLink γ N st.storage ∗ (⌜γn.mode.isDyn = true⌝ ∨
        storageCertLink γ N st.storage ∗ ∃ (ca : Nat) (cfg : CCState), nodeCfg γn ca cfg) $$ [Hst]
    · icases Hst with (%Hd | ⟨#Hl, Hcfg⟩)
      · icases Hdy with (%Hd' | ⟨-, -, (%Hns' | #Hl)⟩)
        · exfalso; rw [Hd] at Hd'; cases Hd'
        · exfalso; have := Hsf.2; rw [Hγr, Hns'] at this; cases this
        · isplitr
          · iexact Hl
          ileft; ipureintro; exact Hd
      · isplitr
        · iexact Hl
        iright; iframe Hl Hcfg
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top (ds ++ []) $$ Hci [Hcom] with ⟨#Hlb, -⟩
    · rw [Hγr]; iexact Hcom
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top l.dlv $$ Hci [Hdlv] with ⟨#Hlbd, %Hidxd⟩
    · rw [Hγr]; iexact Hdlv
    imod api_readStates γ N ⊤ CoPset.subseteq_top sts $$ Hci [Hrs] with Hrs
    · rw [← Hγr]; iexact Hrs
    imod api_msgs γ N ⊤ CoPset.subseteq_top γn Hγr Hγb ms $$ Hci Hmo Hcr Htks with Hms
    rw [Hid0]
    ihave ⟨Hout, #Hsc⟩ := readyOut_cert _ es l $$ Hout
    ihave #Hlink' := Hlink
    iunfold storageCertLink at Hlink'
    icases Hlink' with ⟨#Hl1, -⟩
    imod Hl1 $$ %_ %⊤ %CoPset.subseteq_top [Hsc] with #Hcert
    · rw [← Hγs]; iexact Hsc
    iunfold readyIdx at Hidx
    icases Hidx with ⟨%Lx, #Hlr, %HLx⟩
    imod lastRec_receipt γn.raft Lx $$ Hlr with #Hrc
    ihave %Hrl := preceipt_lt _ $$ Hrc
    imodintro
    iexists [], es, h, some l
    isplitl []
    · unfold committedEntriesAt LogEntry.toEntries; simp only [List.mapIdx_nil]
      iexact Hce
    isplitl []
    · have e : st.delivered ++ [] = strip (ds ++ []) := by rw [List.append_nil, List.append_nil, Hds]
      rw [e]; iexact Hlb
    isplitl [Hsts Hrs]
    · iexists sts; iframe Hsts Hrs
    isplitl [Hes Hmsgs Hms Hhs Hss Hsnap Hout]
    · unfold readyRest
      iexists ms
      iframe Hes Hmsgs Hms Hhs Hss
      isplitr
      · ipureintro
        refine ⟨Lx, HLx.1, HLx.2.1, ?_, by rw [← Hγr]; omega⟩
        have := HLx.2.2
        simp only [List.length_append, strip_length, List.length_nil] at this ⊢
        omega
      unfold readySnap
      dsimp only
      iframe Hsnap Hlbd Hcert
      isplitr
      · ipureintro
        refine ⟨(toEntries_strip l.dlv 0 (IdxOk_base Hidxd)).symm, Hptr, rfl,
          by rw [← Hds]; exact strip_prefix Hpre, by rw [Hlen]; exact Hlt, ?_, Hpos, H61, Hfl, Hind⟩
        rw [Hdl]; rfl
      rw [← Hγs]; iexact Hout
    unfold nodeDriver
    dsimp only
    iexists γn, id, l.dlv
    isplitr
    · ipureintro
      exact ⟨Hnok, Hγs, rfl⟩
    iframe Hci Hlbd
    isplitl [Hst]
    · iexact Hst
    isplitr
    · icases Hdy with (%Hd | ⟨#Htab, -, -⟩)
      · ileft; ipureintro; exact Hd
      iright
      iframe Htab
      isplitr
      · unfold hsCommitted; iright; iright; ipureintro; rw [← Hγr]; exact Hsf.2
      iright; iexact Hlink
    iright
    iexists es, some l
    isplitr
    · ipureintro; rfl
    rw [← Hp', show l.dlv = dlvAfter ds [] (some l) from rfl]; iexact Hbusy

theorem node.wp_readyRecv_impl : node.readyRecv.spec (GF := GF) (hG := hG) := by
  intro n ch γ N id0 st Hh
  iintro %Φ ⟨#Hrc, #Hnode0, Hdrv⟩ HΦ
  icases readyRecv_open n ch γ N id0 st Hh $$ Hrc Hnode0 Hdrv
    with ⟨%γn, %id, %ds, #Hrc', Htok, Hk⟩
  iapply wp_fupd
  iapply node_ready_receive γn id n ch ds st.hardState $$ [Htok]
  · iframe Hrc' Htok
  iintro !> %rd Hraw
  imod Hk $$ %rd Hraw with Hpost
  imodintro
  iapply HΦ
  iexact Hpost

/-- Raft's `Ready` receive as a channel receive's update (`node_ready_receive`'s). -/
theorem node_ready_recvAu (γn : NodeNames) (id : w64) (n ch : Loc) (ds : List EntryM)
    (p : HardStateM) (Φ : Ready → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ EtcdGrove.isReadyChanRaw γn ch -∗ EtcdGrove.nodeDriverChan γn id n ds p -∗
      ▷ (∀ rd : Ready, (∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM)
          (L : Option SnapLoan), readyDataL γn rd ds ce es ms p p' L ∗
          nodeDriverBusy γn id n (dlvAfter ds ce L) es p' L) -∗ Φ rd true) -∗
      recvAu γn.readyc Ready Φ := by
  iintro Hlc #Hrc Hdrv HΦ
  iunfold EtcdGrove.nodeDriverChan at Hdrv
  icases Hdrv with ⟨#Hnode, Hds, -, Hreq⟩
  unfold EtcdGrove.isReadyChanRaw
  iapply handshake_receive_au γn.readyc ch (readyP γn) iprop(True) Φ
    $$ Hlc Hrc [] [HΦ Hds Hreq]
  · itrivial
  inext
  iintro %rd HP
  unfold readyP
  icases HP with ⟨%d, %ce, %es, %ms, %p0, %p', %L, Hd, Hrof, Hdata, #Hlb, #Hld⟩
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hd Hds
  cases Heq
  iapply HΦ
  iexists ce, es, ms, p', L
  iframe Hdata
  unfold nodeDriverBusy
  iframe Hnode Hld
  isplitr
  · unfold dlvLb; iexact Hlb
  iexists ds, ce, p
  iframe Hd Hds Hrof Hreq
  ipureintro; rfl

/-- **Receiving a `Ready` as a channel's receive** (the draft's `isReadyChan_recvAu`). -/
theorem isReadyChan_recvAu_impl (n ch : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (st : NodeDriverState) (Φ : Ready → Bool → IProp GF) (Hh : st.handling = none) :
    ⊢ isReadyChan (GF := GF) n γ N ch -∗ isNode n γ N id -∗ nodeDriver n γ N st -∗
      ∃ γc : ChanNames, isChan ch γc Ready ∗
        (£ 1 ∗ £ 1 -∗ ▷ (∀ rd : Ready, readyPost n γ N id st rd -∗ Φ rd true) -∗
          recvAu γc Ready Φ) := by
  iintro #Hrc #Hnode0 Hdrv
  icases readyRecv_open n ch γ N id st Hh $$ Hrc Hnode0 Hdrv
    with ⟨%γn, %id', %ds, #Hrc', Htok, Hk⟩
  iexists γn.readyc
  isplitr
  · iunfold EtcdGrove.isReadyChanRaw at Hrc'
    iunfold isHandshake at Hrc'
    icases Hrc' with ⟨#Hc, -⟩
    iexact Hc
  iintro Hlc HΦ
  iapply recvAu_wand_fupd γn.readyc Ready
    (fun rd ok => iprop(⌜ok = true⌝ ∗ (∃ (ce es : List EntryM) (ms : List QMsg) (p' : HardStateM)
          (L : Option SnapLoan), readyDataL γn rd ds ce es ms st.hardState p' L ∗
          nodeDriverBusy γn id' n (dlvAfter ds ce L) es p' L) ∗
        (∀ rd : Ready, readyPost n γ N id st rd -∗ Φ rd true))) Φ
    $$ [Htok Hlc HΦ] [Hk]
  · iapply node_ready_recvAu γn id' n ch ds st.hardState $$ Hlc Hrc' Htok
    inext
    iintro %rd Hraw
    iframe Hraw HΦ
    ipureintro; rfl
  iintro %rd %ok ⟨%Hok, Hraw, HΦ⟩
  subst Hok
  imod Hk $$ %rd Hraw with Hpost
  iapply HΦ $$ Hpost

end node

/-! ## Proposals -/

section propose
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A key registered** with the trivial predicate: the adapter registers it the first time
(`prop_register_at`, with the client's fresh token, which the adapter holds). -/
theorem api_key_register (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (k : List w8) :
    ⊢ clusterInv (GF := GF) γ N ={E}=∗ propIs γ.raft k (fun _ => iprop(True)) := by
  iintro #Hci
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, #Hinv, #HspT⟩
  ihave Hat : |={E}=> propIsAt γ.raft k γ.trueQ $$ []
  · unfold apiInv apiInvBody
    have Ha := apiN_sub N HE
    iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩
      Hclose
    cases HFk : F !! k with
    | some u =>
      imod Hclose $$ [HrL Hfull Hops HF HRF] with -
      · inext
        iexists L, F, RF
        iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
        ipureintro; exact Hidx
      imodintro
      iunfold freshOk at HFok
      iapply HFok $$ %k %(by cases u; exact HFk)
    | none =>
      imod ghost_map_insert k () HFk $$ HF with ⟨HF, Hfr⟩
      have HrN : ↑(raftN γ.raft) ⊆ E \ ↑(apiN N) := by
        intro p hp
        unfold raftN at hp; rw [HNs] at hp
        rw [Iris.Std.LawfulSet.mem_diff]
        exact ⟨raftN_sub N HE p hp,
          fun h => ndot_ne_disjoint N (show "raft" ≠ "api" by decide) p ⟨hp, h⟩⟩
      imod prop_register_at γ.raft (E \ ↑(apiN N)) k γ.trueQ HrN $$ Hcinv [Hfr] with #Hat
      · unfold propFresh; iexact Hfr
      imod Hclose $$ [HrL Hfull Hops HF HRF] with -
      · inext
        iexists L, GMap.insert k () F, RF
        iframe HrL Hfull Hops HF HRF HRk HRFok Hcf
        isplitr
        · ipureintro; exact Hidx
        unfold freshOk
        imodintro
        iintro %k' %Hk'
        have := (GMap.lookup_insert_Some F k k' () ()).1 Hk'
        rcases this with ⟨rfl, -⟩ | ⟨-, h⟩
        · iexact Hat
        · iapply HFok $$ %k' %h
      imodintro
      iexact Hat
  imod Hat with #Hat
  imodintro
  iapply propIsAt_propIs $$ Hat HspT

/-- **A proposal's update for raft, from the client's**: when raft appends the proposal's entry
(of the key `entKey ty data`, so of type `ty` and bytes `data`), the client's update runs, at the
entry's term; both logs grow by it. -/
theorem api_propAu1 (γ : Cluster) (N : Namespace) (ty : w32) (data : List w8)
    (_Hnf : ¬ Filler ty data) (HNs : γ.raft.reNs = N .@ "raft") :
    ⊢ apiInv (GF := GF) γ N -∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [⟨t, ty, data⟩]), COMM True }> -∗
      propAu1 γ.raft (entKey ty data) (fun _ => iprop(True)) := by
  iintro #Hinv Hau
  unfold propAu1
  iauintro
  unfold atomic_acc apiInv apiInvBody
  have Hsub : (↑(apiN N) : CoPset) ⊆ ⊤ \ ↑(raftN γ.raft) := by
    unfold raftN; rw [HNs]; exact apiN_sub_raft N
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩ Hclose
  have Hm : (⊤ \ ↑N : CoPset) ⊆ (⊤ \ ↑(raftN γ.raft)) \ ↑(apiN N) := by
    unfold raftN; rw [HNs]; exact mask_api_raft N
  imod (fupd_mask_subseteq (PROP := IProp GF) Hm) with Hback
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%ops, Hown, Hucl⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists L
  iframe HrL
  imodintro
  isplit
  · -- abort: the client's update back
    iintro HrL
    icases Hucl with ⟨Habort, -⟩
    imod Habort $$ Hown with Hau
    imod Hback with -
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iexact Hau
  · -- commit: the entry holds the proposal's key
    iintro %e ⟨HrL, #He, %HeIdx⟩
    icases Hucl with ⟨-, Hcommit⟩
    iunfold entDataIs at He
    iunfold propDataIs at He
    icases He with ⟨⟨%Hek, -⟩, -⟩
    obtain ⟨Hkey, Hnf', Hdec⟩ := Hek
    ihave #Hen := ev2At_nonfiller γ.raft L e Hnf'
    ihave #Hcf' := cmtFacts_snoc γ L e Hdec $$ Hcf Hen
    obtain ⟨Hty, Hd⟩ := entKey_inj Hkey
    have Hx : LogEntry.ofEntryM e = ⟨e.Term', ty, data⟩ := by
      unfold LogEntry.ofEntryM; rw [Hty, Hd]
    have Hxf : ¬ ((LogEntry.ofEntryM e).isFiller ∨ (LogEntry.ofEntryM e).isEmptyV2) :=
      fun h => Hnf' ((isFiller_ofEntryM e).1 h)
    iunfold ownCommittedOps at Hown
    icases Hown with ⟨Hown, -⟩
    ihave %Hag := monoListAuthOwn_agree $$ Hops Hown
    obtain ⟨-, Hops_eq⟩ := Hag
    subst Hops_eq
    icombine Hops Hown as Hops
    imod monoListAuthOwn_update_app [LogEntry.ofEntryM e] $$ Hops with ⟨Hops, #Holb⟩
    imod monoListAuthOwn_update_app [LogEntry.ofEntryM e] $$ Hfull with ⟨Hfull, #Hflb⟩
    icases ((monoListAuthOwn_fractional (GF := GF) γ.ops
        (opsOf (strip L) ++ [LogEntry.ofEntryM e])).fractional (1 : Qp).half (1 : Qp).half).1
      $$ [Hops] with ⟨Hops, Hown⟩
    · rw [Qp.half_add_half]; iexact Hops
    have Hstrip : strip (L ++ [e]) = strip L ++ [LogEntry.ofEntryM e] := by
      rw [strip_append]; rfl
    have Hopsn : opsOf (strip (L ++ [e])) = opsOf (strip L) ++ [LogEntry.ofEntryM e] := by
      rw [Hstrip, opsOf_snoc_op _ _ Hxf]
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    imod Hcommit $$ %e.Term' [Hown] with -
    · unfold ownCommittedOps
      rw [← Hx]
      iframe Hown
      iexists strip (L ++ [e])
      unfold isCommittedLogLb
      rw [Hopsn, Hstrip]
      isplitl []
      · iright; iframe Hflb Holb
        isplitl []
        · ipureintro; have := HeIdx.2; have := HeIdx.1
          simp only [List.length_append, List.length_singleton, strip_length] at *; push_cast; omega
        unfold cmtFactsS
        iexists L ++ [e]
        iframe Hcf'
        ipureintro; exact Hstrip
      ipureintro; rfl
    imod Hback with -
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L ++ [e], F, RF
      rw [Hopsn, Hstrip]
      iframe HrL Hfull Hops HF HFok Hcf' HRF HRk HRFok
      ipureintro
      refine ⟨IdxOk_snoc Hidx.1 HeIdx.1, ?_⟩
      have := HeIdx.2; simp only [List.length_append, List.length_singleton]; push_cast; omega
    imodintro
    imodintro
    itrivial

/-- The errors of a proposal. -/
theorem propErr_api (cd : context.ContextDesc (IProp GF)) (err : GoInterface) :
    propErr cd err ⊢
      ⌜err = interface.nil⌝ ∨ errStopped err ∨ errProposalDropped err ∨ ctxErr cd err := by
  unfold propErr nodeErr stepErr
  iintro ((%H | H | H) | (%H | H))
  · ileft; ipureintro; exact H
  · iright; ileft; iexact H
  · iright; iright; iright; iexact H
  · ileft; ipureintro; exact H
  · iright; iright; ileft; iexact H

end propose

/-! ## Reads -/

section read
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Depositing a read** (raft's `read_deposit`, at a mask `E` around raft's namespace), its update
fired the first time by the caller's own means `Hfire` (which may borrow `R`) rather than by the
update itself: a caller that holds the client's half of the log (the adapter, its invariant open)
cannot let the update open its invariant again. -/
theorem read_deposit_with (γ : RaftNames) (E : CoPset) (c : List w8) (Qr : List EntryM → IProp GF)
    (φ : List EntryM → Prop) (R : IProp GF) (HE : ↑(raftN γ) ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γ -∗ rdFresh γ c -∗ readAu γ Qr -∗ R -∗
      (∀ P, R -∗ ghostVar γ.reRLog (1 : Qp).half P ={(E \ ↑(raftRegN γ)) \ ↑(raftLogN γ)}=∗
        R ∗ ghostVar γ.reRLog (1 : Qp).half P ∗ □ Qr P ∗ ⌜φ P⌝) ={E}=∗
      R ∗ ∃ Lc, readReq γ c Lc ∗ isRead γ c Qr ∗ ⌜φ Lc⌝ := by
  iintro #Hinv Hfr #Hau HR Hfire
  ihave #Hri := raftCommitInv_reg γ $$ Hinv
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  have HE1 := raftRegN_of HE
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, >Hq2, Hregs⟩ Hclose2
  have HE2 := raftLogN_of_diff HE
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  icases rlq_join γ P l $$ Hq1 Hq2 with ⟨%Heq, Hv⟩
  subst Heq
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R0, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold readsReg at Hreads
  icases Hreads with ⟨>Hra, Hs⟩
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  cases HRc : RR !! c with
  | some r =>
    icases (BigSepM.bigSepM_delete (Φ := fun c r =>
      iprop(▷ (readSlot (GF := GF) γ r P ∗ rdFresh γ c))) HRc).1 $$ Hs
      with ⟨⟨-, >Hfr'⟩, -⟩
    unfold rdFresh
    ihave %Hne := ghostMapElem_ne γ.reRdFresh c c (DFrac.own 1) () () $$ Hfr Hfr'
    exact absurd rfl Hne
  | none =>
  imod Hfire $$ %P HR Hv with ⟨HR, Hv, #HQ, %Hφ⟩
  imod saved_pred_alloc Qr DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod ghost_map_insert_persist c ((γq, P) : GName × List EntryM) HRc $$ Hra
    with ⟨Hra, #Hel⟩
  ihave #Hslot : readSlot γ (γq, P) P $$ []
  · unfold readSlot
    iexists Qr
    iframe Hsp Hau
    isplitr
    · ipureintro; exact List.prefix_refl _
    imodintro
    iintro %n %Hn
    have : n = P.length := by simp at Hn; omega
    rw [this, List.take_length]
    iexact HQ
  ihave #HcP := ownCommitted_lb γ P $$ HP
  icases rlq_split γ P $$ Hv with ⟨Hq1, Hq2⟩
  imod Hclose1 $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imod Hclose2 $$ [Hq2 Hprops Hra Hs Hfr] with -
  · iexists P
    iframe Hq2
    unfold regsAt readsReg
    inext
    iexists R0, Std.insert RR c (γq, P)
    iframe Hprops Hnoop Hra
    iapply (BigSepM.bigSepM_insert (Φ := fun c r =>
      iprop(readSlot (GF := GF) γ r P ∗ rdFresh γ c)) HRc).2
    iframe Hslot Hfr
    iexact Hs
  imodintro
  iframe HR
  iexists P
  isplitr
  · unfold readReq
    iexists γq
    iframe Hel HcP
  isplitr
  · unfold isRead
    iexists γq, P
    iframe Hel Hsp
  ipureintro; exact Hφ

/-- **Firing a read context's update** at the requested entries `opsOf l`, with the adapter's half
of them: they are the client's, and the update gives `□ Q` of them. -/
theorem api_fire_read (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ⊤ \ ↑N ⊆ E)
    (Q : List LogEntry → IProp GF) (l : List LogEntry) :
    ⊢ monoListAuthOwn (GF := GF) γ.ops (1 : Qp).half (opsOf l) -∗ ctxAu γ N Q ={E}=∗
      monoListAuthOwn γ.ops (1 : Qp).half (opsOf l) ∗ □ Q (opsOf l) := by
  iintro Hops #Hau
  imod (fupd_mask_subseteq (PROP := IProp GF) HE) with Hback
  iunfold ctxAu at Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%ops, Hown, Hucl⟩
  iunfold ownCommittedOps at Hown
  icases Hown with ⟨Hhalf, Hrest⟩
  ihave %Hag := monoListAuthOwn_agree $$ Hops Hhalf
  obtain ⟨-, Hops_eq⟩ := Hag
  subst Hops_eq
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [Hhalf Hrest] with #HQ
  · unfold ownCommittedOps; iframe Hhalf Hrest
  imod Hback with -
  imodintro
  iframe Hops HQ

/-- **A read context's update for raft**, from the client's: the log lent and returned, the
client's update fired at its requested entries. -/
theorem api_readAu (γ : Cluster) (N : Namespace) (Q : List LogEntry → IProp GF)
    (HNs : γ.raft.reNs = N .@ "raft") :
    ⊢ apiInv (GF := GF) γ N -∗ ctxAu γ N Q -∗ readAu γ.raft (qrOf Q) := by
  iintro #Hinv #Hau
  unfold readAu
  imodintro
  iauintro
  unfold atomic_acc apiInv apiInvBody
  have Hsub : (↑(apiN N) : CoPset) ⊆ ⊤ \ ↑(raftN γ.raft) := by
    unfold raftN; rw [HNs]; exact apiN_sub_raft N
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑(raftN γ.raft)) \ ↑(apiN N) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down]
  iexists L
  iframe HrL
  isplit
  · iintro HrL
    imod Hclose2 with -
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iempintro
  · iintro HrL
    imod Hclose2 with -
    have Hm : (⊤ \ ↑N : CoPset) ⊆ (⊤ \ ↑(raftN γ.raft)) \ ↑(apiN N) := by
      unfold raftN; rw [HNs]; exact mask_api_raft N
    imod api_fire_read γ N _ Hm Q (strip L) $$ Hops Hau with ⟨Hops, #HQ⟩
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    unfold qrOf
    iexact HQ

/-- A lower bound of the committed log is no longer than the adapter's log. -/
theorem api_full_lb_len (γ : Cluster) (L : List EntryM) (l0 : List LogEntry) :
    ⊢ monoListAuthOwn (GF := GF) γ.full 1 (strip L) -∗ isCommittedLogLb γ l0 -∗
      monoListAuthOwn γ.full 1 (strip L) ∗ ⌜l0.length ≤ L.length⌝ := by
  iintro Hfull #Hl
  unfold isCommittedLogLb
  icases Hl with (%Hnil | ⟨#Hfl, -⟩)
  · iframe Hfull; ipureintro; subst Hnil; simp
  icases mono_list_auth_lb_valid $$ Hfull Hfl with %Hpre
  iframe Hfull
  ipureintro
  have := Hpre.2.length_le
  rw [strip_length] at this; exact this

/-- **A committed context's read deposited in raft**, the first time (raft's `read_deposit`, its
first firing by the adapter), or the deposit found. -/
theorem api_read_ensure (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) :
    ⊢ clusterInv (GF := GF) γ N -∗ isReadCtx γ N c Q ={⊤}=∗ ∃ Lc, readReq γ.raft c Lc := by
  iintro #Hci #Hctx
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, #Hinv, -⟩
  ihave #Hctx' := Hctx
  iunfold isReadCtx at Hctx'
  icases Hctx' with ⟨%γq, %l0, #Hel, #Hsp, #Hau, #Hl0⟩
  ihave #HrAu := api_readAu γ N Q HNs $$ Hinv Hau
  iunfold apiInv at Hinv
  unfold apiInvBody
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >#Hcf, >HRF, >#HRk, #HRFok⟩
    Hclose
  cases HRc : RF !! c with
  | some u =>
    ihave #HRk' := HRk
    iunfold rdKeys at HRk'
    ihave #Hk := HRk' $$ %c %(by cases u; exact HRc)
    iunfold readKey at Hk
    icases Hk with ⟨%γq', %l0', %Lc, -, #Hrq, -⟩
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok Hcf HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iexists Lc
    iexact Hrq
  | none =>
    imod ghost_map_insert c () HRc $$ HRF with ⟨HRF, Hfr⟩
    have HrN : (↑(raftN γ.raft) : CoPset) ⊆ ⊤ \ ↑(apiN N) := by
      unfold raftN; rw [HNs]
      intro p hp
      rw [Iris.Std.LawfulSet.mem_diff]
      exact ⟨CoPset.subseteq_top p hp,
        fun h => ndot_ne_disjoint N (show "raft" ≠ "api" by decide) p ⟨hp, h⟩⟩
    have Hm : (⊤ \ ↑N : CoPset) ⊆
        ((⊤ \ ↑(apiN N)) \ ↑(raftRegN γ.raft)) \ ↑(raftLogN γ.raft) := by
      intro p hp
      rw [Iris.Std.LawfulSet.mem_diff] at hp
      have hN := hp.2
      simp only [Iris.Std.LawfulSet.mem_diff]
      refine ⟨⟨⟨hp.1, fun h => hN (apiN_sub N (fun _ h => h) p h)⟩, fun h => hN ?_⟩, fun h => hN ?_⟩
      · unfold raftRegN raftN at h; rw [HNs] at h
        exact nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "reg" p h)
      · unfold raftLogN raftN at h; rw [HNs] at h
        exact nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p h)
    icases api_full_lb_len γ L l0 $$ Hfull Hl0 with ⟨Hfull, %Hl0L⟩
    imod read_deposit_with γ.raft (⊤ \ ↑(apiN N)) c (qrOf Q) (fun P => l0.length ≤ P.length)
        iprop(rLog γ.raft L ∗ monoListAuthOwn γ.ops (1 : Qp).half (opsOf (strip L))) HrN
      $$ Hcinv [Hfr] HrAu [HrL Hops] [] with ⟨⟨HrL, Hops⟩, %Lc, #Hrq, #Hrd, %HLc⟩
    · unfold rdFresh; iexact Hfr
    · iframe HrL Hops
    · iintro %P ⟨HrL, Hops⟩ Hv
      iunfold rLog at HrL
      ihave %Heq := ghostVar_agree γ.raft.reRLog P (1 : Qp).half L (1 : Qp).half $$ Hv HrL
      subst Heq
      imod api_fire_read γ N _ Hm Q (strip P) $$ Hops Hau with ⟨Hops, #HQ⟩
      imodintro
      iframe Hv Hops
      isplitl [HrL]
      · unfold rLog; iexact HrL
      isplitr
      · unfold qrOf; iexact HQ
      ipureintro; exact Hl0L
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, GMap.insert c () RF
      iframe HrL Hfull Hops HF HFok Hcf HRF
      isplitr
      · ipureintro; exact Hidx
      isplitr
      · unfold rdKeys
        imodintro
        iintro %c' %Hc'
        rcases (GMap.lookup_insert_Some RF c c' () ()).1 Hc' with ⟨rfl, -⟩ | ⟨-, h⟩
        · unfold readKey
          iexists γq, l0, Lc
          iframe Hel Hrq
          ipureintro; exact HLc
        · iapply HRk $$ %c' %h
      · unfold rdFreshOk
        imodintro
        iintro %c' %Hc'
        rcases (GMap.lookup_insert_Some RF c c' () ()).1 Hc' with ⟨rfl, -⟩ | ⟨-, h⟩
        · unfold readDep
          iexists γq, l0, Q
          iframe Hel Hsp Hrd
        · iapply HRFok $$ %c' %h
    imodintro
    iexists Lc
    iexact Hrq

end read

/-! ## Conf changes -/

section cc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseInterp] [GooseSemantics] go_gctx hG [StorageModel GF] sem package_sem in
/-- An entry that is no filler to raft is a requested entry (2026-10-29, stage U5). -/
theorem opsOf_single_nonFiller (t : w64) (ty : w32) (bs : List w8) (Hnf : ¬ Filler ty bs) :
    opsOf [(⟨t, ty, bs⟩ : LogEntry)] = [⟨t, ty, bs⟩] :=
  opsOf_eq_self _ fun e he => by
    simp only [List.mem_singleton] at he; subst he
    exact ⟨fun h => Hnf ⟨h.1, .inl h.2⟩, fun h => Hnf ⟨h.1, .inr h.2⟩⟩

/-- The client's conf-change update, at the bytes raft marshaled, when they are no filler's
(2026-10-29, stage U5: the update's `opsOf` of the entry is then the entry). -/
theorem au_cc_fix (γ : Cluster) (N : Namespace) (ty : w32) (o : ConfChangeIM) (bs : List w8)
    (Hm : MarshalsConfChange (some o) bs) (Hnf : ¬ Filler ty bs) :
    AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps (GF := GF) γ ops }> @ ⊤ \ ↑N, ∅
       <{ ∀∀ (t : w64) (bs' : List w8), ⌜MarshalsConfChange (some o) bs'⌝ ∗
            ownCommittedOps γ (ops ++ opsOf [⟨t, ty, bs'⟩]), COMM True }> ⊢
    AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps (GF := GF) γ ops }> @ ⊤ \ ↑N, ∅
       <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [⟨t, ty, bs⟩]), COMM True }> := by
  iintro Hau
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases Hacc with ⟨%ops, Hown, Hucl⟩
  imodintro
  iexists ops
  iframe Hown
  isplit
  · iintro Hown
    icases Hucl with ⟨Hab, -⟩
    iapply Hab $$ Hown
  · iintro %t Hown
    icases Hucl with ⟨-, Hc⟩
    iapply Hc $$ %t %bs [Hown]
    rw [opsOf_single_nonFiller t ty bs Hnf]
    iframe Hown
    ipureintro; exact Hm

end cc

/-! ## Advance, Step, Tick, TransferLeadership -/

section misc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (open) **Tick credits** (raft's `tickCred`: time receipts). -/
def tickCredit (_γ : Cluster) (n : Nat) : IProp GF := ⧗ n

theorem tickCredit_intro_impl (γ : Cluster) (n : Nat) : ⧗ n ⊢ tickCredit (GF := GF) γ n := by
  unfold tickCredit; exact .rfl

theorem tickCredit_zero_impl (γ : Cluster) : ⊢ |==> tickCredit (GF := GF) γ 0 := by
  unfold tickCredit; exact receipt_zero

/-- (open) **A message `node.Step` takes** at the node `id`: raft's (`stepP`), for any node names
of the cluster's (`NodeOk`), given a time receipt (2026-10-29, stage U7: `node.Step` takes it from
a Go step of its own, a `MsgTimeoutNow`'s tick credit; until then the caller's `tickCredit`), and
the message not `nil` (what `node.Step` checks before taking the receipt). -/
def stepIn (γ : Cluster) (_N : Namespace) (id : w64) (ml : Loc) : IProp GF :=
  iprop(⌜ml ≠ null⌝ ∗ ∀ γn : NodeNames, ⌜NodeOk γ γn⌝ -∗ ⧗ 1 -∗ stepP γn id ml)

/-- A list without repeats is a permutation of the elements of its set. -/
theorem perm_elements_listToSet' (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

/-- **Stepping a sent message** (the draft's `stepIn_intro`). -/
theorem stepIn_intro_impl (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64)
    (st : MsgSt) :
    (st.msg.Type' ≠ MsgProp → NetMsgOk id ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∧
      st.msg.Type' ≠ MsgTransferLeader) →
    (st.msg.Type' = MsgSnap → ∃ sv, st.snap = some sv ∧ uint.Z sv.Metadata'.Index' < 2 ^ 61) →
    st.msg.To' = id →
    sentMsg (GF := GF) γ N src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ⊢
    |==> stepIn γ N id ml := by
  intro Hnet Hsnap _
  iintro ⟨#Hsent, Hm, Hcr⟩
  icases msgPtsC_nn $$ Hm with ⟨%Hnn, Hm⟩
  iunfold sentMsg at Hsent
  icases Hsent with ⟨-, #Hraft, #Hlb, -⟩
  ihave #Hdat := isRaftMsg_dat γ.raft src st $$ Hraft
  iunfold isRaftMsg at Hraft
  icases Hraft with ⟨%Hns0, -, ⟨%a, %Habs, #Hl⟩, -, %Hra⟩
  have Hst : (⟨st.msg, st.ents, st.snap, st.ctx, []⟩ : MsgSt) = st := by
    cases st; simp only at Hra ⊢; rw [Hra.1]
  rw [Hst] at Hnet
  rw [Hst]
  iunfold msgCredits at Hcr
  icases Hcr with ⟨Hrd, Htk⟩
  -- the message's abstraction, but a snapshot's
  ihave #Hmsg : □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
      isMessage (GF := GF) γ.raft (absMsg ty st.msg st.ents st.ctx)) $$ []
  · imodintro
    iintro %ty %Hty %Hne
    unfold msgAbs at Habs
    rcases Habs with ⟨Hn, -⟩ | ⟨ty0, Hty0, -, rfl⟩ | ⟨sv, Hs, -, -⟩
    · rw [Hn] at Hty; cases Hty
    · rw [Hty0] at Hty; cases Hty
      simp only [Option.toList_some]
      ihave #Hx := (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessageC (GF := GF) γ.raft x)).1
        $$ Hl
      iapply isMessageC_isMessage $$ Hx
    · rw [Hs] at Hty; cases Hty; exact absurd rfl Hne
  by_cases Hp : st.msg.Type' = MsgProp
  · imodintro
    unfold stepIn
    isplitr; · ipureintro; exact Hnn
    iintro %γn %Hnok -
    obtain ⟨Hγr, -, -, -, -⟩ := Hnok
    unfold stepP
    iright
    unfold fwdP
    iexists st
    isplitl [Hm]
    · iapply msgPtsC_cap_any $$ Hm
    isplitr
    · ipureintro; exact ⟨Hp, Hra.1⟩
    isplitr
    · rw [Hγr]
      ihave #H := Hmsg $$ %MsgType.propose %(by rw [Hp]; exact mtypeOf_MsgProp) %(by decide)
      -- a proposal's abstraction does not read its context
      iExactEq H
      rfl
    simp only [stTks, if_pos Hp]
    rw [Hγr]
    iexact Htk
  · imod msgPtsC_persist_els $$ Hm with Hm
    obtain ⟨Hnok', Hntl⟩ := Hnet Hp
    imodintro
    unfold stepIn
    isplitr; · ipureintro; exact Hnn
    iintro %γn %Hnok Htc
    obtain ⟨Hγr, Hγb, Hsl, -, Hsi⟩ := Hnok
    unfold stepP
    ileft
    unfold netP
    iexists st
    isplitl [Hm]
    · iapply msgPtsC_cap_any $$ Hm
    isplitr
    · ipureintro; exact Hnok'
    isplitr
    · ipureintro
      exact ⟨fun h => absurd h Hntl,
        fun hty => Hsi.resolve_right (fun h => Hns0 h hty)⟩
    rw [Hγr, Hγb]
    isplitr
    · iexact Hmsg
    isplitr
    · imodintro
      iintro %Hty
      unfold msgAbs at Habs
      have Hms : mtypeOf st.msg.Type' = some .snap := by rw [Hty]; exact mtypeOf_MsgSnap
      rcases Habs with ⟨Hn, -⟩ | ⟨ty0, Hty0, Hne0, -⟩ | ⟨sv, -, Hsv, rfl⟩
      · rw [Hn] at Hms; cases Hms
      · rw [Hty0] at Hms; cases Hms; exact absurd rfl Hne0
      obtain ⟨sv', Hsv', Hix⟩ := Hsnap Hty
      rw [Hsv] at Hsv'; cases Hsv'
      iexists sv, sv.Metadata'.ConfState'.lists
      isplitr
      · ipureintro; exact ⟨Hsv, rfl, Hix⟩
      isplitr
      · simp only [Option.toList_some]
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessageC (GF := GF) γ.raft x)).1
          $$ Hl
      isplitr
      · iunfold msgDat at Hdat
        iapply Hdat $$ %sv
        ipureintro; exact ⟨Hty, Hsv⟩
      iapply snapLocal_none (by rw [Hsl])
    iframe Hlb Hrd
    unfold tickCred
    split
    · iexact Htc
    · icases receipt_zero_of 1 $$ Htc with ⟨H0, -⟩
      iexact H0

end misc

end ApiImpl
end EtcdGrove
end Perennial
