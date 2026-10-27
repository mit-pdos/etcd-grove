/-
# Raft's node API over an abstract log: the implementation (2026-10-27)

The definitions behind the drafted API (`NodeApiDraft.lean`, namespace `Draft`) and the proofs of
its laws and specs (`*_impl`), from raft's internals. Once done, the draft's `sorry` bodies are
replaced by these (`notes/decisions.md`, "Raft's node API over an abstract log").

**The ghost state** (`Cluster`): raft's names (`raft`, the commit invariant's namespace
`N .@ "raft"`) and the adapter's own:
- `full`, a monotone list of `LogEntry`: the full committed log (fillers included), its authority
  in the adapter's invariant (`apiInv`), its lower bounds the client's (`isCommittedLogLb`);
- `ops`, a monotone list of `LogEntry`: the committed requested entries (`opsOf`), its authority
  halved between `apiInv` and the client (`ownCommittedOps`);
- `ctxs`, a ghost map `c ↦ γq` (persistent elements) of the read contexts the client committed,
  `γq` naming the context's predicate; the client holds the authority (`ownReadCtxs`).

The adapter's invariant `apiInv γ N` (at `N .@ "api"`, disjoint from raft's `N .@ "raft"`) holds the
client half of raft's committed log (`rLog`), the authority of `full` at it (as `LogEntry`s) and
half of `ops` at its requested entries, and the client side of raft's registries.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context
public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Perennial.Ghost.MonoList
public import Spec.go_etcd_io.raft.v3.Api
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.node__Ready

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

/-- An entry of the committed log as a client sees it. Its index is its position (the `i`-th entry,
from 0, has index `i + 1`). -/
structure LogEntry where
  term : w64
  type : raftpb.EntryType
  data : List w8

instance LogEntry_countable : Pos.Countable LogEntry :=
  countableOfLeftInverse (fun e : LogEntry => (e.term, e.type, e.data))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

/-- The Go record of the entry at index `idx`. -/
def LogEntry.toEntryM (idx : w64) (e : LogEntry) : EntryM := ⟨e.term, idx, e.type, e.data⟩

/-- **A filler** (the draft's): raft's own entries, and a client's empty proposal. -/
def LogEntry.isFiller (e : LogEntry) : Prop :=
  e.data = [] ∧ (e.type = W32 0 ∨ e.type = W32 2)

instance (e : LogEntry) : Decidable e.isFiller := by unfold LogEntry.isFiller; infer_instance

/-- **The requested entries** of a log: everything but its fillers. -/
def opsOf (l : List LogEntry) : List LogEntry := l.filter fun e => !decide e.isFiller

/-- The Go entries of the log entries `l`, at the indices after `base`. -/
def LogEntry.toEntries (l : List LogEntry) (base : Nat) : List EntryM :=
  l.mapIdx fun i e => e.toEntryM (W64 (base + i + 1))

/-- A raft entry as a client sees it: its index dropped. -/
def LogEntry.ofEntryM (e : EntryM) : LogEntry := ⟨e.Term', e.Type', e.Data'⟩

/-- A raft log as a client sees it. -/
def strip (L : List EntryM) : List LogEntry := L.map LogEntry.ofEntryM

theorem opsOf_append (a b : List LogEntry) : opsOf (a ++ b) = opsOf a ++ opsOf b := by
  unfold opsOf; exact List.filter_append _ _

theorem opsOf_prefix {a b : List LogEntry} (h : a <+: b) : opsOf a <+: opsOf b := by
  obtain ⟨r, rfl⟩ := h
  rw [opsOf_append]
  exact List.prefix_append _ _

theorem opsOf_snoc_filler (l : List LogEntry) (e : LogEntry) (h : e.isFiller) :
    opsOf (l ++ [e]) = opsOf l := by
  rw [opsOf_append]
  simp [opsOf, h]

theorem opsOf_snoc_op (l : List LogEntry) (e : LogEntry) (h : ¬ e.isFiller) :
    opsOf (l ++ [e]) = opsOf l ++ [e] := by
  rw [opsOf_append]
  simp [opsOf, h]

theorem strip_append (a b : List EntryM) : strip (a ++ b) = strip a ++ strip b := by
  unfold strip; exact List.map_append

theorem strip_prefix {a b : List EntryM} (h : a <+: b) : strip a <+: strip b := by
  obtain ⟨r, rfl⟩ := h
  rw [strip_append]
  exact List.prefix_append _ _

theorem strip_length (a : List EntryM) : (strip a).length = a.length := by
  unfold strip; exact List.length_map _

/-- A filler as raft sees it is one as the client does. -/
theorem isFiller_ofEntryM (e : EntryM) :
    (LogEntry.ofEntryM e).isFiller ↔ Filler e.Type' e.Data' := Iff.rfl

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

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The client's views of the committed log, and their laws -/

/-- **A lower bound of the committed log**, fillers included (persistent): `l` is a prefix of the
full log (`full`), and its requested entries of the requested entries (`ops`). -/
def isCommittedLogLb (γ : Cluster) (l : List LogEntry) : IProp GF :=
  iprop(monoListLbOwn γ.full l ∗ monoListLbOwn γ.ops (opsOf l))

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

theorem ownCommittedOps_get_lb_impl (γ : Cluster) (ops : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ⊢
      ownCommittedOps γ ops ∗ ∃ l, isCommittedLogLb γ l ∗ ⌜opsOf l = ops⌝ := by
  unfold ownCommittedOps
  iintro ⟨Ha, %l, #Hl, %Hops⟩
  iframe Ha
  isplitl []
  · iexists l; iframe Hl; ipureintro; exact Hops
  · iexists l; iframe Hl; ipureintro; exact Hops

theorem ownCommittedOps_lb_prefix_impl (γ : Cluster) (ops l : List LogEntry) :
    ownCommittedOps (GF := GF) γ ops ∗ isCommittedLogLb γ l ⊢ ⌜opsOf l <+: ops⌝ := by
  unfold ownCommittedOps isCommittedLogLb
  iintro ⟨⟨Ha, -⟩, -, #Hlb⟩
  icases mono_list_auth_lb_valid $$ Ha Hlb with %H
  ipureintro; exact H.2

theorem isCommittedLogLb_mono_impl (γ : Cluster) (l1 l2 : List LogEntry) :
    l1 <+: l2 → isCommittedLogLb (GF := GF) γ l2 ⊢ isCommittedLogLb γ l1 := by
  intro Hp
  unfold isCommittedLogLb
  iintro ⟨#H1, #H2⟩
  isplitl []
  · iapply monoListLbOwn_le _ Hp $$ H1
  · iapply monoListLbOwn_le _ (opsOf_prefix Hp) $$ H2

theorem isCommittedLogLb_agree_impl (γ : Cluster) (l1 l2 : List LogEntry) :
    isCommittedLogLb (GF := GF) γ l1 ∗ isCommittedLogLb γ l2 ⊢ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold isCommittedLogLb
  iintro ⟨⟨#H1, -⟩, #H2, -⟩
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
  iprop(∃ (γq : GName) (Q : List LogEntry → IProp GF), c ↪[γ.ctxs]□ γq ∗
    savedPredOwn γq DFrac.discard Q ∗ isRead γ.raft c (qrOf Q))

instance readDep_persistent (γ : Cluster) (c : List w8) : Persistent (readDep (GF := GF) γ c) := by
  unfold readDep; infer_instance

/-- **A read context deposited in raft** (timeless): its entry in `γ.ctxs` and raft's record. -/
def readKey (γ : Cluster) (c : List w8) : IProp GF :=
  iprop(∃ (γq : GName) (Lc : List EntryM), c ↪[γ.ctxs]□ γq ∗ readReq γ.raft c Lc)

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
  iprop(□ ∀ k : List w8, ⌜F !! k = some ()⌝ -∗ propIs γ.raft k (fun _ => iprop(True)))

instance freshOk_persistent (γ : Cluster) (F : GMap (List w8) Unit) :
    Persistent (freshOk (GF := GF) γ F) := by
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
    rLog γ.raft L ∗ ⌜IdxOk L⌝ ∗
    monoListAuthOwn γ.full 1 (strip L) ∗ monoListAuthOwn γ.ops (1 : Qp).half (opsOf (strip L)) ∗
    ghostMapAuth γ.raft.reFresh 1 F ∗ freshOk γ F ∗
    ghostMapAuth γ.raft.reRdFresh 1 RF ∗ rdKeys γ RF ∗ rdFreshOk γ RF)

def apiInv (γ : Cluster) (N : Namespace) : IProp GF := inv (apiN N) (apiInvBody γ)

instance apiInv_persistent (γ : Cluster) (N : Namespace) : Persistent (apiInv (GF := GF) γ N) := by
  unfold apiInv; infer_instance

/-- **The cluster's invariants**: raft's, in `N .@ "raft"`, and the adapter's. -/
def clusterInv (γ : Cluster) (N : Namespace) : IProp GF :=
  iprop(⌜γ.raft.reNs = N .@ "raft"⌝ ∗ raftCommitInv γ.raft ∗ apiInv γ N)

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
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, #HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iempintro
  · iintro %e ⟨HrL, #He, %HeIdx⟩
    imod Hclose2 with -
    iunfold entDataIs at He
    iunfold propDataIs at He
    icases He with %Hfill
    have Hf : (LogEntry.ofEntryM e).isFiller := (isFiller_ofEntryM e).2 Hfill.1
    imod monoListAuthOwn_update_app [LogEntry.ofEntryM e] $$ Hfull with ⟨Hfull, -⟩
    have Hstrip : strip (L ++ [e]) = strip L ++ [LogEntry.ofEntryM e] := by
      rw [strip_append]; rfl
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L ++ [e], F, RF
      rw [Hstrip, opsOf_snoc_filler _ _ Hf]
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
      ipureintro; exact IdxOk_snoc Hidx HeIdx
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
  iprop(∃ M : GMap (List w8) GName, ghostMapAuth γ.ctxs 1 M ∗ ⌜∀ c, c ∈ U ↔ c ∈ M⌝)

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

/-- **The read context `c` is committed to `Q`**: its entry in `ctxs`, naming `Q`, and the update. -/
def isReadCtx (γ : Cluster) (N : Namespace) (c : List w8) (Q : List LogEntry → IProp GF) :
    IProp GF :=
  iprop(∃ γq : GName, c ↪[γ.ctxs]□ γq ∗ savedPredOwn γq DFrac.discard Q ∗ ctxAu γ N Q)

instance isReadCtx_persistent (γ : Cluster) (N : Namespace) (c : List w8)
    (Q : List LogEntry → IProp GF) : Persistent (isReadCtx (GF := GF) γ N c Q) := by
  unfold isReadCtx; infer_instance

theorem readCtx_commit_impl (γ : Cluster) (N : Namespace) (U : GSet (List w8)) (c : List w8)
    (Q : List LogEntry → IProp GF) :
    c ∉ U →
    ownReadCtxs (GF := GF) γ U ∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
           <{ ownCommittedOps γ ops, COMM □ Q ops }> ⊢
    |==> (ownReadCtxs γ (insert c U) ∗ isReadCtx γ N c Q) := by
  intro Hc
  unfold ownReadCtxs isReadCtx ctxAu
  iintro ⟨⟨%M, HM, %HU⟩, #Hau⟩
  have HMc : M !! c = none := by
    have h : ¬ c ∈ M := fun h => Hc ((HU c).mpr h)
    cases hM : M !! c with
    | none => rfl
    | some v => exact absurd (show c ∈ M from by show (M.lookup c).isSome = true; rw [hM]; rfl) h
  imod saved_pred_alloc Q DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod ghost_map_insert_persist c γq HMc $$ HM with ⟨HM, #Hel⟩
  imodintro
  isplitl [HM]
  · iexists _
    iframe HM
    ipureintro
    intro c'
    rw [GMap.elem_of_insert_set]
    have := GMap.lookup_insert_is_Some M c c' γq
    change _ ↔ ((<[c := γq]> M) !! c').isSome = true
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
  · iexists γq
    iframe Hel Hsp Hau

end ctx

/-! ## A new cluster -/

section boot
variable [GooseExts]

/-- The bootstrap log (the draft's): a `ConfChangeAddNode` of each peer, its context `ctx`, at term
1, as `MarshalConfChange` encodes it. -/
def BootLog (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) : Prop :=
  boot.length = ps.length ∧ (boot.length : Int) < 2 ^ 61 ∧
  ∀ (k : Nat) (e : LogEntry), boot[k]? = some e →
    ∃ id ctx, ps[k]? = some id ∧ ctxs[k]? = some ctx ∧ e.term = W64 1 ∧ e.type = W32 1 ∧
      MarshalsConfChange (some (.v1 ⟨W32 0, id, ctx, W64 0⟩)) e.data

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

theorem opsOf_eq_self (l : List LogEntry) (H : ∀ e ∈ l, ¬ e.isFiller) : opsOf l = l := by
  unfold opsOf
  rw [List.filter_eq_self]
  intro e he
  simp [H e he]

theorem BootLog.ok {ps : List w64} {ctxs : List (List w8)} {boot : List LogEntry}
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

theorem BootLog.opsOf {ps : List w64} {ctxs : List (List w8)} {boot : List LogEntry}
    (H : BootLog ps ctxs boot) : opsOf boot = boot := by
  apply opsOf_eq_self
  intro e he
  obtain ⟨k, hk⟩ := List.getElem?_of_mem he
  obtain ⟨-, -, -, -, -, Hty, -⟩ := H.2.2 k e hk
  rintro ⟨-, h | h⟩ <;> rw [Hty] at h <;> have := congrArg (fun x : w32 => uint.Z x) h <;>
    revert this <;> decide

theorem BootLog.idx {ps : List w64} {ctxs : List (List w8)} {boot : List LogEntry}
    (H : BootLog ps ctxs boot) : IdxOk (LogEntry.toEntries boot 0) := by
  intro k e He
  have Hok := H.ok
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

theorem readCredits_split (γ : Cluster) (a b : Nat) :
    readCredits (GF := GF) γ (a + b) ⊣⊢ readCredits γ a ∗ readCredits γ b := by
  unfold readCredits; exact rdCred_split γ.raft a b

/-- **A node's boot token** of a new cluster of the peers `ps` with the contexts `ctxs`: its raft
ghost state at the bootstrap state, the committed bootstrap log, the bytes of its entries
(`bootMarshal`), and the cluster's invariants. The cluster is static, in raft's no-snapshot mode,
with leader transfer on. -/
def nodeBoot (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (id : w64) :
    IProp GF :=
  iprop(⌜γ.raft.reCfg = GMap.listToSet ps ∧ γ.raft.reDyn = none ∧ BootLogOk ps γ.raft.reBoot ∧
      γ.raft.reNoSnap = true ∧ γ.raft.reNoXfer = false⌝ ∗
    clusterInv γ N ∗ ownRaftGhost γ.raft id (bootPState γ.raft.reBoot) ∗
    isCommitted γ.raft γ.raft.reBoot ∗ bootMarshal ps ctxs γ.raft.reBoot ∗
    inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 1))

/-- The client's part of a new cluster, built in raft's allocation (`allocClientGen`). -/
def allocOut (N : Namespace) (boot : List LogEntry) (bud : BudgetNames) (γr : RaftNames) :
    IProp GF :=
  iprop(∃ γ : Cluster, ⌜γ.raft = γr ∧ γ.bud = bud⌝ ∗ apiInv γ N ∗ ownCommittedOps γ boot ∗ ownReadCtxs γ ∅)

/-- The adapter's part of raft's allocation: its ghost state and invariant, raft's standing update
from it. -/
theorem api_alloc_client (N : Namespace) (E : CoPset) (cfg : GSet w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (bud : BudgetNames) (HB : BootLog ps ctxs boot) :
    ⊢ allocClientGen (GF := GF) E cfg none (fun _ _ => True) (LogEntry.toEntries boot 0)
        (allocOut N boot bud) (N .@ "raft") := by
  unfold allocClientGen
  iintro %γr %Hγr #Hc HrL Hfa Hrfa #Hpis
  obtain ⟨-, -, -, -, HNs⟩ := Hγr
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γf, Hf, #Hflb⟩
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γo, Ho, #Holb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName) with ⟨%γc, Hca⟩
  icases ((monoListAuthOwn_fractional (GF := GF) γo
      boot).fractional (1 : Qp).half (1 : Qp).half).1
    $$ [Ho] with ⟨Ho1, Ho2⟩
  · rw [Qp.half_add_half]; iexact Ho
  let γ : Cluster := ⟨γr, γf, γo, γc, bud⟩
  imod inv_alloc (apiN N) E (apiInvBody (GF := GF) γ) $$ [HrL Hf Ho1 Hfa Hrfa] with #Hinv
  · inext
    unfold apiInvBody
    iexists LogEntry.toEntries boot 0, bootFresh (LogEntry.toEntries boot 0), ∅
    rw [strip_toEntries, HB.opsOf]
    iframe HrL Hf Ho1 Hfa Hrfa
    isplitr
    · ipureintro; exact HB.idx
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
          propIs (GF := GF) γr (entKey e.Type' e.Data') (fun _ => iprop(True))) hj) $$ Hpis
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
  isplitr; · ipureintro; exact ⟨rfl, rfl⟩
  iframe Hinv'
  isplitl [Ho2]
  · unfold ownCommittedOps
    iframe Ho2
    iexists boot
    unfold isCommittedLogLb
    rw [HB.opsOf]
    iframe Hflb Holb
    ipureintro; rfl
  · unfold ownReadCtxs
    iexists ∅
    iframe Hca
    ipureintro
    intro c
    constructor <;> intro h <;> exact absurd h (by simp [Membership.mem, GMap.lookup_empty])

/-- **A new cluster** (the draft's `cluster_alloc`; see the report for the differences). -/
theorem cluster_alloc_impl (N : Namespace) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 →
    BootLog ps ctxs boot → ps.Nodup → ps ≠ [] → W64 0 ∉ ps →
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      |={E}=> ∃ γ, ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        [∗list] id ∈ ps, nodeBoot γ N ps ctxs id := by
  intro Hrb HB Hnd Hne Hnz
  iintro #Hm
  imod budget_alloc_boot (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  have Hok := HB.ok
  have Hwf := Hok.wf Hnd
  have Hbne : LogEntry.toEntries boot 0 ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [toEntries_length, HB.1] at this
    exact Hne (List.eq_nil_of_length_eq_zero this)
  have Hcne : GMap.listToSet ps ≠ ∅ := by
    intro h
    obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil Hne
    have : p ∈ GMap.listToSet (p :: ps') := (GMap.elem_of_list_to_set p _).2 (List.mem_cons_self ..)
    rw [h] at this
    exact (GMap.not_elem_of_empty p) this
  have Hnz' : W64 0 ∉ GMap.listToSet ps := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  ihave Hcl := api_alloc_client (GF := GF) N E (GMap.listToSet ps) ps ctxs boot bud HB
  imod ownRaftGhost_alloc_core E (GMap.listToSet ps) (GMap.listToSet ps) none (fun _ _ => True)
    (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot bud) (some (GMap.listToSet ps))
    (fun T hT => by cases hT; exact ⟨GMap.subseteq_refl _, rfl⟩) true (fun _ => Hbne)
    false (fun h => by cases h) (fun _ _ => True) (fun _ => none) (N .@ "raft") Hcne Hnz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, Hboot, -, Hns, Hnx, -, -, HNs⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb⟩ := Hγr
  subst Hγr
  imodintro
  iexists γ
  iframe Hops Hctx
  isplitl [Hcr]
  · unfold readCredits; iexact Hcr
  simp only [Option.isSome_none]
  rw [← bootPState_eq]
  iapply bigSepM_listToSet _ ps Hnd
  iapply BigSepM.bigSepM_impl $$ Hnodes
  imodintro
  iintro %id %u %_ Hg
  unfold nodeBoot clusterInv
  rw [Hboot]
  rw [Hγb]
  iframe Hg Hc0 Hm Hcinv Hinv Hbinv Htlb
  isplitr
  · ipureintro; exact ⟨Hcfg, Hdyn, Hok, Hns, Hnx⟩
  ipureintro; exact HNs

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
  icases Hci with ⟨%HNs, #Hcinv, #Hinv⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, #HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
    iframe HrL Hfull Hops HF HFok HRF HRk HRFok
    ipureintro; exact Hidx
  imodintro
  isplitl []
  · unfold isCommittedLogLb
    isplitl []
    · iapply monoListLbOwn_le _ (strip_prefix HDP) $$ Hflb
    · iapply monoListLbOwn_le _ (opsOf_prefix (strip_prefix HDP)) $$ Holb
  ipureintro
  intro k e Hk
  obtain ⟨r, rfl⟩ := HDP
  exact Hidx k e (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hk).1]; exact Hk)

/-- **A read state** (persistent): raft's (`readOk`), its context committed (`γ.ctxs`). -/
def readStateOk (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64) : IProp GF :=
  iprop(clusterInv γ N ∗ readOk γ.raft c idx ∗ ∃ γq : GName, c ↪[γ.ctxs]□ γq)

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
  icases Hci with ⟨%HNs, #Hcinv, #Hinv⟩
  unfold readReq
  icases Hrq with ⟨%γq, #Hel, -⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, #HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
    iframe HrL Hfull Hops HF HFok HRF HRk HRFok
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
    ⊢ clusterInv (GF := GF) γ N -∗ EtcdGrove.readStateOk γ.raft st ={E}=∗
      readStateOk γ N st.RequestCtx' st.Index' := by
  iintro #Hci #Hst
  iunfold EtcdGrove.readStateOk at Hst
  icases Hst with ⟨%c, %Hc, #Hok⟩
  rw [Hc]
  ihave #Hok' := Hok
  iunfold readOk at Hok'
  icases Hok' with ⟨%Lc, #Hrq, -⟩
  imod api_readReq_dep γ N E HE c Lc $$ Hci Hrq with ⟨#Hdep, -⟩
  iunfold readKey at Hdep
  icases Hdep with ⟨%γq, %Lc', #Hel, -⟩
  imodintro
  unfold readStateOk
  iframe Hci Hok
  iexists γq
  iframe Hel

theorem api_readStates (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (sts : List ReadStateM) :
    ⊢ clusterInv (GF := GF) γ N -∗ ([∗list] st ∈ sts, EtcdGrove.readStateOk γ.raft st) ={E}=∗
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
      EtcdGrove.readStateOk (GF := GF) γ.raft st)).1 $$ H with ⟨H1, H⟩
    imod api_readState γ N E HE st $$ Hci H1 with #H1
    imod ih $$ Hci H with H
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (st : ReadStateM) =>
      readStateOk (GF := GF) γ N st.RequestCtx' st.Index')).2
    iframe H1 H

theorem readStateOk_used_impl (γ : Cluster) (N : Namespace) (c : List w8) (idx : w64)
    (U : GSet (List w8)) :
    readStateOk (GF := GF) γ N c idx ∗ ownReadCtxs γ U ⊢ ⌜c ∈ U⌝ := by
  unfold readStateOk ownReadCtxs
  iintro ⟨⟨-, -, %γq, #Hel⟩, %M, HM, %HU⟩
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
  icases Hci with ⟨%HNs, #Hcinv, #Hinv⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, #HFok, >HRF, >#HRk, #HRFok⟩ Hclose
  have Hl : (↑(raftLogN γ.raft) : CoPset) ⊆ E \ ↑(apiN N) := by
    unfold raftLogN raftN; rw [HNs]; exact raftN_api N HE "log"
  imod rLog_committed γ.raft L (E \ ↑(apiN N)) Hl $$ Hcinv HrL with ⟨HrL, #HLc⟩
  unfold isCommittedLogLb
  icases Hl with ⟨#Hfl, -⟩
  icases mono_list_auth_lb_valid $$ Hfull Hfl with %Hpre
  imod Hclose $$ [HrL Hfull Hops HF HRF] with -
  · inext
    iexists L, F, RF
    iframe HrL Hfull Hops HF HFok HRF HRk HRFok
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
  icases Hst with ⟨#Hci, #Hok, %γq0, #Hel0⟩
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
  icases Hdep with ⟨%γq, %Q0, #Hel, #HspQ, #Hrd⟩
  iunfold isRead at Hrd
  icases Hrd with ⟨%γr', %Lc', #Hrel', #Hspr⟩
  ihave %Hagr := ghostMapElem_agree $$ Hrel Hrel'
  cases Hagr
  unfold isReadCtx
  icases Hctx with ⟨%γq1, #Hel1, #Hsp1, -⟩
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

/-! ## The nodes -/

section node
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A running node** `n` of id `id` in the cluster `γ` (persistent): raft's node, of the
cluster's names and budget, and the cluster's invariants. -/
def isNode (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(∃ γn : NodeNames, ⌜γn.raft = γ.raft ∧ γn.bud = γ.bud⌝ ∗ EtcdGrove.isNode γn id n ∗
    clusterInv γ N)

instance isNode_persistent (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) :
    Persistent (isNode (GF := GF) n γ N id) := by
  unfold isNode; infer_instance

/-- The node's `Ready` channel `ch` (persistent): the node struct's `readyc`. -/
def isReadyChan (n : Loc) (_γ : Cluster) (_N : Namespace) (ch : Loc) : IProp GF :=
  iprop(∃ nv : node, n ↦□ nv ∗ ⌜ch = nv.readyc'⌝)

instance isReadyChan_persistent (n : Loc) (γ : Cluster) (N : Namespace) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) n γ N ch) := by
  unfold isReadyChan; infer_instance

/-- The state of a node's `Ready` loop (the draft's). -/
structure NodeDriverState where
  storage : Storage
  delivered : List LogEntry
  hardState : HardStateM
  handling : Option (List EntryM × Option SnapLoan)

def NodeDriverState.init (stor : Storage) : NodeDriverState := ⟨stor, [], hsZero, none⟩

/-- **The `Ready` loop's token**: raft's driver token (idle, or busy with a `Ready`) at the raft
log `ds` the client sees as `st.delivered`, at a node that takes no snapshot. -/
def nodeDriver (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) : IProp GF :=
  iprop(∃ (γn : NodeNames) (id : w64) (ds : List EntryM),
    ⌜γn.raft = γ.raft ∧ γn.bud = γ.bud ∧ γn.stor = st.storage ∧ γn.snapIn = false ∧
      strip ds = st.delivered⌝ ∗ clusterInv γ N ∗
    ((⌜st.handling = none⌝ ∗ EtcdGrove.nodeDriver γn id n ds st.hardState) ∨
     (∃ (es : List EntryM) (L : Option SnapLoan), ⌜st.handling = some (es, L)⌝ ∗
       nodeDriverBusy γn id n ds es st.hardState L)))

/-- The Go entries `sl` are the log entries `ce`, at the indices after `base` (read-only). -/
def committedEntriesAt (sl : GoSlice) (base : Nat) (ce : List LogEntry) : IProp GF :=
  entsRO sl (LogEntry.toEntries ce base)

/-- (open) **A message a `Ready` handed out**: sent by a node of the cluster, of a term within the
cluster's budget. -/
def sentMsg (γ : Cluster) (N : Namespace) (st : MsgSt) : IProp GF :=
  iprop(clusterInv γ N ∗ (∃ src : w64, isRaftMsg γ.raft src st) ∗ termLB γ.bud st.msg.Term')

instance sentMsg_persistent (γ : Cluster) (N : Namespace) (st : MsgSt) :
    Persistent (sentMsg (GF := GF) γ N st) := by
  unfold sentMsg; infer_instance

/-- (open) **What a sent message carries for its receiver's `Step`.** -/
def msgCredits (γ : Cluster) (_N : Namespace) (st : MsgSt) : IProp GF :=
  iprop(rdCred γ.raft (if st.msg.Type' = MsgReadIndex then 1 else 0) ∗ stTks γ.raft st)

/-- (open) A `Ready`'s storage part (the draft's `readySnap`; the snapshot case is not reached
yet: no node takes snapshots). -/
def readySnap (_γ : Cluster) (_N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (st' : NodeDriverState) (es : List EntryM) : Option SnapLoan → IProp GF
  | none => iprop(⌜st'.delivered = st.delivered ++ ce ∧ rd.Snapshot' = null⌝ ∗
      appendRight st.storage es)
  | some _ => iprop(False)

/-- (open) **The rest of a `Ready`** (the draft's `readyRest`). -/
def readyRest (γ : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (st' : NodeDriverState) : IProp GF :=
  iprop(∃ (es : List EntryM) (ms : List QMsg) (L : Option SnapLoan) (h : HardStateM),
    ⌜st'.storage = st.storage ∧ st'.handling = some (es, L) ∧
      st'.hardState = phsNext st.hardState h⌝ ∗
    entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N q.st ∗ msgCredits γ N q.st) ∗
    hsOpt rd.HardState' h ∗ softStateRO rd.SoftState' ∗
    ⌜∃ Lx : Int, Lx < 2 ^ 64 ∧
      (∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ Lx + 1) ∧
      ((st.delivered ++ ce).length : Int) ≤ Lx⌝ ∗
    readySnap γ N rd st ce st' es L)

/-- **`node.Ready()`** (the draft's). -/
abbrev node.Ready.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Ready")) (Val #()))
  {{ (ch : Loc), RET #ch; isReadyChan n γ N ch }}

theorem node.wp_Ready_impl : node.Ready.spec (GF := GF) (hG := hG) := by
  intro γ N id n
  wp_start as Hnode
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hnode, -⟩
  iunfold EtcdGrove.isNode at Hnode
  icases Hnode with ⟨%nv, %r, %lok, #Hnode⟩
  iNamed Hnode
  ihave #Hn' := Hn
  iStructNamed Hn'
  wp_auto
  iapply HΦ
  unfold isReadyChan
  iexists nv
  iframe Hn
  ipureintro; rfl

/-- **Receiving a `Ready`** (the draft's `node.readyRecv`). -/
abbrev node.readyRecv.spec : Prop :=
  ∀ (n ch : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState),
  st.handling = none →
  {{ isReadyChan (GF := GF) n γ N ch ∗ nodeDriver n γ N st }}
    (App (Val (chan.receive Ready.ty)) (Val #ch))
  {{ (rd : Ready), RET (PairV #rd #true);
      ∃ (ce : List LogEntry) (st' : NodeDriverState),
        committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
        isCommittedLogLb γ (st.delivered ++ ce) ∗
        (∃ rs, readStatesPts rd.ReadStates' rs ∗
          [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
        readyRest γ N rd st ce st' ∗
        nodeDriver n γ N st' }}

theorem node.wp_readyRecv_impl : node.readyRecv.spec (GF := GF) (hG := hG) := by
  intro n ch γ N st Hh
  iintro %Φ ⟨#Hrc, Hdrv⟩ HΦ
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, Htok⟩
  obtain ⟨Hγr, Hγb, Hγs, Hsn, Hds⟩ := Hf
  icases Htok with (⟨-, Htok⟩ | ⟨%es0, %L0, %Hh', -⟩)
  rotate_left
  · rw [Hh] at Hh'; cases Hh'
  ihave ⟨Htok, #Hnode⟩ := nodeDriver_isNode γn id n ds st.hardState $$ Htok
  iunfold isReadyChan at Hrc
  icases Hrc with ⟨%nv, #Hn0, %Hch⟩
  ihave #Hnode' := Hnode
  iunfold EtcdGrove.isNode at Hnode'
  icases Hnode' with ⟨%nv', %r, %lok, #Hnode'⟩
  iNamed Hnode'
  icombine Hn0 Hn gives %Hnv
  subst Hnv
  ihave #Hrc' : EtcdGrove.isReadyChan γn ch $$ []
  · unfold EtcdGrove.isReadyChan; rw [Hch]; iexact Hreadyc
  iapply wp_fupd
  iapply node_ready_receive_ns γn id n ch ds st.hardState (Or.inr (Or.inr Hsn)) $$ [Htok]
  · iframe Hrc' Htok
  iintro !> %rd ⟨%ce, %es, %ms, %p', Hdata, Hbusy⟩
  iunfold readyData at Hdata
  icases Hdata with ⟨#Hce, #Hcom, #Hes, Happ, Hmsgs, Hmo, Hcr, Htks, ⟨%sts, Hsts, Hrs⟩,
    ⟨%h, Hhs, %Hp'⟩, -, Hss, %Hnull, #Hidx⟩
  imod api_committed_lb γ N ⊤ CoPset.subseteq_top (ds ++ ce) $$ Hci [Hcom] with ⟨#Hlb, %HidxOk⟩
  · rw [Hγr]; iexact Hcom
  imod api_readStates γ N ⊤ CoPset.subseteq_top sts $$ Hci [Hrs] with Hrs
  · rw [← Hγr]; iexact Hrs
  iunfold readyIdx at Hidx
  icases Hidx with ⟨%Lx, -, %HLx⟩
  imodintro
  iapply HΦ
  iexists strip ce, ⟨st.storage, st.delivered ++ strip ce, p', some (es, none)⟩
  have Hlen : st.delivered.length = ds.length := by rw [← Hds, strip_length]
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
  isplitl [Hes Happ Hmsgs Hmo Hcr Htks Hhs Hss]
  · unfold readyRest
    iexists es, ms, none, h
    isplitr
    · ipureintro; exact ⟨rfl, rfl, Hp'⟩
    iframe Hes Hmsgs Hhs Hss
    isplitl [Hmo Hcr Htks]
    · ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [Hcr Htks]
      · iframe Hcr Htks
      ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [Hmo H]
      · iframe Hmo H
      iapply (BigSepL.bigSepL_impl) $$ H
      imodintro
      iintro %k %q %_ ⟨⟨Ho, #Hraft, #Htlb⟩, Hcr, Htk⟩
      iframe Ho
      unfold sentMsg msgCredits
      rw [← Hγr, ← Hγb]
      iframe Hci Htlb Hcr Htk
      iexists γn.id
      iexact Hraft
    isplitr
    · ipureintro
      refine ⟨Lx, HLx.1, HLx.2.1, ?_⟩
      have := HLx.2.2
      simp only [List.length_append, strip_length] at this ⊢
      omega
    unfold readySnap
    isplitr
    · ipureintro; exact ⟨rfl, Hnull⟩
    rw [← Hγs]; iexact Happ
  unfold nodeDriver
  iexists γn, id, ds ++ ce
  isplitr
  · ipureintro
    exact ⟨Hγr, Hγb, Hγs, Hsn, by rw [strip_append, Hds]⟩
  iframe Hci
  iright
  iexists es, none
  isplitr
  · ipureintro; rfl
  iexact Hbusy

/-- **`StartNode(c, peers)`** (the draft's, with the differences in the report: the boot token
names the peers and their contexts, the term budget is the cluster's, and the storage is never
compacted past index `1`, raft's no-snapshot mode). -/
abbrev StartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM) (R : IProp GF)
    (peers : GoSlice) (dq : DFrac) (pv : List Peer) (ps : List w64) (ctxs : List (List w8)),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  cv.Applied' = W64 0 →
  σ.prev = entryID.mk (W64 0) (W64 0) → σ.ents = [] → (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] → HsEmpty hs →
  csm.Voters' = [] → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  ps = pv.map Peer.ID' → ps ≠ [] → ps.Nodup → W64 0 ∉ ps → (ps.length : Int) ≤ 2 ^ 62 →
  cv.ID' ∈ ps →
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            R -∗ hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      peers ↦*{dq} pv ∗ peersCtx pv ctxs ∗
      nodeBoot γ N ps ctxs cv.ID' ∗
      -- the storage never compacted past index `1` (raft's no-snapshot mode, `NsCap`)
      storCap (interface.ok si) 1 }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      R ∗ ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) }}

theorem wp_StartNode_impl (hS : EtcdGrove.StartNode.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) := by
  intro γ N c cv lok si σ hs csm R peers dq pv ps ctxs H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss
    Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid Hfl
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, Hinst, Hpeers, #Hpc, Hboot, #Hcap⟩ HΦ
  iunfold nodeBoot at Hboot
  icases Hboot with ⟨%Hf, #Hci, Hg, #Hc0, #Hm, #Hbinv, #Htlb⟩
  obtain ⟨Hcfg, Hdyn, Hok, Hns, Hnx⟩ := Hf
  iapply (hS γ.raft .static γ.bud c cv lok si σ hs csm R peers dq pv ps ctxs γ.raft.reBoot false
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid
    Hcfg rfl Hok Hfl (fun h => by cases h)) $$ [Hc Hown Hinst Hpeers Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hpeers Hpc Hm Hc0 Hbinv Htlb
    isplitl [Hg]
    · unfold bootInit; iexact Hg
    isplitr
    · unfold NsCap; imodintro; iintro -; iexact Hcap
    · iapply certLink_noSnap γ.raft _ Hns
  iintro !> %nd ⟨HR, %γn, %n, %Hf, -, #Hnode, Hdrv, -, -⟩
  obtain ⟨Hγr, Hγb, Hγs, -, Hsn, Hnd'⟩ := Hf
  iapply HΦ
  iframe HR
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact ⟨Hγr, Hγb⟩
  unfold nodeDriver
  iexists γn, cv.ID', []
  isplitr
  · ipureintro; exact ⟨Hγr, Hγb, Hγs, Hsn, rfl⟩
  iframe Hci
  ileft
  isplitr
  · ipureintro; rfl
  unfold NodeDriverState.init
  iexact Hdrv

end node

end ApiImpl
end EtcdGrove
end Perennial
