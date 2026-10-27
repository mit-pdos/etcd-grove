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
public import Proof.go_etcd_io.raft.v3.NodeApiVocab
public import Spec.go_etcd_io.raft.v3.Api
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.node__Ready
public import Proof.go_etcd_io.raft.v3.node__ReadIndexReq

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 Draft

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
  /-- the trivial result predicate the adapter registers its proposals with -/
  trueQ : GName

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The client's views of the committed log, and their laws -/

/-- **A lower bound of the committed log**, fillers included (persistent): `l` is empty, or a
prefix of the full log (`full`) whose requested entries are a prefix of the requested entries
(`ops`). -/
def isCommittedLogLb (γ : Cluster) (l : List LogEntry) : IProp GF :=
  iprop(⌜l = []⌝ ∨ (monoListLbOwn γ.full l ∗ monoListLbOwn γ.ops (opsOf l)))

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
  iintro ⟨⟨Ha, -⟩, (%Hnil | ⟨-, #Hlb⟩)⟩
  · ipureintro; subst Hnil; exact List.nil_prefix
  icases mono_list_auth_lb_valid $$ Ha Hlb with %H
  ipureintro; exact H.2

theorem isCommittedLogLb_nil_impl (γ : Cluster) : ⊢ isCommittedLogLb (GF := GF) γ [] := by
  unfold isCommittedLogLb
  ileft; ipureintro; rfl

theorem isCommittedLogLb_mono_impl (γ : Cluster) (l1 l2 : List LogEntry) :
    l1 <+: l2 → isCommittedLogLb (GF := GF) γ l2 ⊢ isCommittedLogLb γ l1 := by
  intro Hp
  unfold isCommittedLogLb
  iintro (%Hnil | ⟨#H1, #H2⟩)
  · ileft; ipureintro; subst Hnil; exact List.prefix_nil.mp Hp
  iright
  isplitl []
  · iapply monoListLbOwn_le _ Hp $$ H1
  · iapply monoListLbOwn_le _ (opsOf_prefix Hp) $$ H2

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
    rLog γ.raft L ∗ ⌜IdxOk L⌝ ∗
    monoListAuthOwn γ.full 1 (strip L) ∗ monoListAuthOwn γ.ops (1 : Qp).half (opsOf (strip L)) ∗
    ghostMapAuth γ.raft.reFresh 1 F ∗ freshOk γ F ∗
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
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
  rintro ⟨-, h | h⟩ <;> rw [Hty] at h <;> have := congrArg (fun x : w32 => uint.Z x) h <;>
    revert this <;> decide

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
  γ.raft.reNoXfer = false ∧ γ.raft.reSnapOkRaw = sokOf snapOk ∧
  γ.raft.reSnapLoc = (fun _ => none) ∧ γ.raft.reCertNs = N ∧
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
def allocOut (N : Namespace) (boot : List LogEntry) (bud : BudgetNames) (γr : RaftNames) :
    IProp GF :=
  iprop(∃ γ : Cluster, ⌜γ.raft = γr ∧ γ.bud = bud⌝ ∗
    savedPredOwn γ.trueQ DFrac.discard (fun _ : List EntryM => iprop(True : IProp GF)) ∗ apiInv γ N ∗ ownCommittedOps γ boot ∗ ownReadCtxs γ ∅)

/-- The adapter's part of raft's allocation: its ghost state and invariant, raft's standing update
from it. -/
theorem api_alloc_client (N : Namespace) (E : CoPset) (cfg : GSet w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (bud : BudgetNames) (HB : BootLog ps ctxs boot) :
    ⊢ allocClientGen (GF := GF) E cfg none (fun _ _ => True) (LogEntry.toEntries boot 0)
        (allocOut N boot bud) (N .@ "raft") := by
  unfold allocClientGen
  iintro %γr %Hγr #Hc HrL Hfa Hrfa ⟨%γT, #HspT, #Hpis⟩
  obtain ⟨-, -, -, -, HNs⟩ := Hγr
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γf, Hf, #Hflb⟩
  imod mono_list_own_alloc (GF := GF) boot with ⟨%γo, Ho, #Holb⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName) with ⟨%γc, Hca⟩
  icases ((monoListAuthOwn_fractional (GF := GF) γo
      boot).fractional (1 : Qp).half (1 : Qp).half).1
    $$ [Ho] with ⟨Ho1, Ho2⟩
  · rw [Qp.half_add_half]; iexact Ho
  let γ : Cluster := ⟨γr, γf, γo, γc, bud, γT⟩
  imod inv_alloc (apiN N) E (apiInvBody (GF := GF) γ) $$ [HrL Hf Ho1 Hfa Hrfa] with #Hinv
  · inext
    unfold apiInvBody
    iexists LogEntry.toEntries boot 0, bootFresh (LogEntry.toEntries boot 0), ∅
    rw [strip_toEntries, (BootLog_opsOf HB)]
    iframe HrL Hf Ho1 Hfa Hrfa
    isplitr
    · ipureintro; exact (BootLog_idx HB)
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
  iframe Hinv' HspT
  isplitl [Ho2]
  · unfold ownCommittedOps
    iframe Ho2
    iexists boot
    unfold isCommittedLogLb
    rw [(BootLog_opsOf HB)]
    isplitl []
    · iright; iframe Hflb Holb
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
    (boot : List LogEntry) (snapOk : List LogEntry → List w8 → Prop) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 →
    BootLog ps ctxs boot → ps.Nodup → ps ≠ [] → W64 0 ∉ ps →
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      |={E}=> ∃ γ, ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isStaticCluster γ N ps snapOk ∗ leaderTransferOn γ N ∗
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
  ihave Hcl := api_alloc_client (GF := GF) N E (GMap.listToSet ps) ps ctxs boot bud HB
  imod ownRaftGhost_alloc_core E (GMap.listToSet ps) (GMap.listToSet ps) none (fun _ _ => True)
    (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot bud) (some (GMap.listToSet ps))
    (fun T hT => by cases hT; exact ⟨GMap.subseteq_refl _, rfl⟩) false (fun h => by cases h)
    false (fun h => by cases h) (sokOf snapOk) (fun _ => none) (N .@ "raft") N Hcne
    Hnz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, Hboot, Htrk, Hns, Hnx, Hsok, Hsl, HNs, Hcert⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb⟩ := Hγr
  subst Hγr
  ihave #Hst : isStaticCluster (GF := GF) γ N ps snapOk $$ []
  · unfold isStaticCluster clusterInv
    iframe Hcinv Hinv HspT
    ipureintro
    exact ⟨⟨Hcfg, Hdyn, Hns, Hnx, Hsok, Hsl, Hcert, .inr Htrk, Hne, Hnd, Hnz, Hlen⟩, HNs⟩
  imodintro
  iexists γ
  iframe Hops Hctx Hst
  isplitl [Hcr]
  · unfold readCredits; iexact Hcr
  isplitr
  · unfold leaderTransferOn; ipureintro; exact Hnx
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
  have Hcl0 := api_alloc_client (GF := GF) N E (GMap.listToSet vs) [] [] [] bud HB
  rw [H0] at Hcl0
  ihave Hcl := Hcl0
  imod ownRaftGhost_alloc_core E (GMap.listToSet vs) (GMap.listToSet vs) none (fun _ _ => True)
    [] (W64 0) (allocOut N [] bud) none (fun _ h => by cases h) false (fun h => by cases h)
    false (fun h => by cases h) (sokOf snapOk) (fun _ => none) (N .@ "raft") N Hcne
    Hnz' BootWf_nil (fun h => absurd rfl h)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, -, Htrk, Hns, Hnx, Hsok, Hsl, HNs, Hcert⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb⟩ := Hγr
  subst Hγr
  ihave #Hst : isStaticCluster (GF := GF) γ N vs snapOk $$ []
  · unfold isStaticCluster clusterInv
    iframe Hcinv Hinv HspT
    ipureintro
    exact ⟨⟨Hcfg, Hdyn, Hns, Hnx, Hsok, Hsl, Hcert, .inl Htrk, Hne, Hnd, Hnz, Hlen⟩, HNs⟩
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
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
    iright
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
  icases Hci with ⟨%HNs, #Hcinv, #Hinv, -⟩
  unfold readReq
  icases Hrq with ⟨%γq, #Hel, -⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
  icases Hci with ⟨%HNs, #Hcinv, #Hinv, -⟩
  unfold apiInv apiInvBody
  have Ha := apiN_sub N HE
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩ Hclose
  have Hl : (↑(raftLogN γ.raft) : CoPset) ⊆ E \ ↑(apiN N) := by
    unfold raftLogN raftN; rw [HNs]; exact raftN_api N HE "log"
  imod rLog_committed γ.raft L (E \ ↑(apiN N)) Hl $$ Hcinv HrL with ⟨HrL, #HLc⟩
  iunfold isCommittedLogLb at Hl
  icases Hl with (%Hnil | ⟨#Hfl, -⟩)
  · imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
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

/-- **The snapshot `k` is certified** for the cluster: raft's configuration certificate, and its
data what the cluster admits of a committed log as long as its index, which the client knows. -/
def snapshotCert (γ : Cluster) (_N : Namespace) (k : SnapTrip) : IProp GF :=
  iprop(raftSnapCert γ.raft k ∗ ∃ L : List EntryM, isCommittedLogLb γ (strip L) ∗
    ⌜IdxOk L ∧ L.length = uint.nat k.sid.index' ∧ γ.raft.reSnapOk L k.dat⌝)

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
    (k : SnapTrip) :
    ⊢ clusterInv (GF := GF) γ N -∗ raftSnapCertD γ.raft k ={E}=∗ snapshotCert γ N k := by
  iintro #Hci #Hk
  iunfold raftSnapCertD at Hk
  icases Hk with ⟨#Hc, #Hd⟩
  iunfold snapDataOk at Hd
  icases Hd with ⟨%L, #HL, %HLp⟩
  imod api_committed_lb γ N E HE L $$ Hci HL with ⟨#Hlb, %Hidx⟩
  imodintro
  unfold snapshotCert
  iframe Hc
  iexists L
  iframe Hlb
  ipureintro; exact ⟨Hidx, HLp.1, HLp.2⟩

theorem raft_of_snapshotCert (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (k : SnapTrip) :
    ⊢ clusterInv (GF := GF) γ N -∗ snapshotCert γ N k ={E}=∗ raftSnapCertD γ.raft k := by
  iintro #Hci #Hk
  iunfold snapshotCert at Hk
  icases Hk with ⟨#Hc, %L, #Hlb, %HL⟩
  imod api_lb_committed γ N E HE (strip L) $$ Hci Hlb with ⟨%D, %HD, #HDc⟩
  imod api_committed_lb γ N E HE D $$ Hci HDc with ⟨-, %HDi⟩
  have HDL : D = L := by
    rw [← toEntries_strip D 0 (IdxOk_base HDi), ← toEntries_strip L 0 (IdxOk_base HL.1), HD]
  subst HDL
  imodintro
  unfold raftSnapCertD snapDataOk
  iframe Hc
  iexists D
  iframe HDc
  ipureintro; exact ⟨HL.2.1, HL.2.2⟩

/-- **The storage's certificates are the cluster's** (the draft's `storageCertLink`). -/
def storageCertLink (γ : Cluster) (N : Namespace) (st : Storage) : IProp GF :=
  iprop(□ (∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ storCert st k ={E}=∗ snapshotCert γ N k) ∗
    □ (∀ (k : SnapTrip) (E : CoPset), ⌜↑N ⊆ E⌝ -∗ snapshotCert γ N k ={E}=∗ storCert st k))

instance storageCertLink_persistent (γ : Cluster) (N : Namespace) (st : Storage) :
    Persistent (storageCertLink (GF := GF) γ N st) := by
  unfold storageCertLink; infer_instance

/-- Raft's certificate link (`storCertOk`), at the cluster's certificate namespace `N`. -/
theorem storCertOk_of_link (γ : Cluster) (N : Namespace) (st : Storage)
    (HN : γ.raft.reCertNs = N) :
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
    imod snapshotCert_of_raft γ N E HE k $$ Hci Hr with #Hc
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
  iintro ⟨⟨%Hst, -⟩, -, %L, #Hlb, %HL⟩
  iexists strip L
  iframe Hlb
  ipureintro
  exact ⟨by rw [strip_length]; exact HL.2.1,
    (reSnapOk_sokOf γ.raft snapOk Hst.2.2.2.2.1 L k.dat).1 HL.2.2⟩

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
  obtain ⟨Hcfg, Hdyn, -, -, Hsok, -, -, Htrk, -⟩ := Hst
  have Hlen : l.length < 2 ^ 64 := by have := word.unsigned_range i; rw [Hl]; word
  imodintro
  iintro %t
  unfold snapshotCert
  isplitl []
  · iapply raftSnapCert_static γ.raft _ (by unfold RaftNames.dyn; rw [Hdyn]; rfl) (Hok t)
    intro _
    refine ⟨Hcfg.symm, rfl, ?_⟩
    intro T hT
    rcases Htrk with h | h
    · rw [h] at hT; cases hT
    · rw [h] at hT; cases hT
      apply (GMap.union_subseteq _ _ _).2
      refine ⟨(GMap.union_subseteq _ _ _).2 ⟨GMap.subseteq_refl _, GMap.empty_subseteq _⟩,
        GMap.empty_subseteq _⟩
  iexists LogEntry.toEntries l 0
  rw [strip_toEntries]
  iframe Hlb
  ipureintro
  refine ⟨toEntries_idx l Hlen, by rw [toEntries_length]; exact Hl, ?_⟩
  rw [reSnapOk_sokOf γ.raft snapOk Hsok, strip_toEntries]
  exact Hso

end cert

/-! ## The nodes -/

section node
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What a node's names say of it: of the cluster's names and budget, in the static mode, taking
snapshots from the network, with no snapshot directory. -/
def NodeOk (γ : Cluster) (γn : NodeNames) : Prop :=
  γn.raft = γ.raft ∧ γn.bud = γ.bud ∧ γn.snapIn = true ∧ γn.mode = .static ∧
    γ.raft.reSnapLoc = (fun _ => none)

/-- **A running node** `n` of id `id` in the cluster `γ` (persistent): raft's node, of the
cluster's names and budget (`NodeOk`), and the cluster's invariants. -/
def isNode (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(∃ γn : NodeNames, ⌜NodeOk γ γn⌝ ∗ EtcdGrove.isNode γn id n ∗ clusterInv γ N)

instance isNode_persistent (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) :
    Persistent (isNode (GF := GF) n γ N id) := by
  unfold isNode; infer_instance

/-- The node's `Ready` channel `ch` (persistent): the node struct's `readyc`. -/
def isReadyChan (n : Loc) (_γ : Cluster) (_N : Namespace) (ch : Loc) : IProp GF :=
  iprop(∃ nv : node, n ↦□ nv ∗ ⌜ch = nv.readyc'⌝)

instance isReadyChan_persistent (n : Loc) (γ : Cluster) (N : Namespace) (ch : Loc) :
    Persistent (isReadyChan (GF := GF) n γ N ch) := by
  unfold isReadyChan; infer_instance

/-- **The `Ready` loop's token**: raft's driver token (idle, or busy with a `Ready`) at the raft
log `ds` the client sees as `st.delivered`, and the storage's certificate link. -/
def nodeDriver (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) : IProp GF :=
  iprop(∃ (γn : NodeNames) (id : w64) (ds : List EntryM),
    ⌜NodeOk γ γn ∧ γn.stor = st.storage ∧ strip ds = st.delivered⌝ ∗ clusterInv γ N ∗
    storageCertLink γ N st.storage ∗
    (∃ (ca : Nat) (cfg : CCState), nodeCfg γn ca cfg) ∗
    ((⌜st.handling = none⌝ ∗ EtcdGrove.nodeDriver γn id n ds st.hardState) ∨
     (∃ (es : List EntryM) (L : Option SnapLoan), ⌜st.handling = some (es, L)⌝ ∗
       nodeDriverBusy γn id n ds es st.hardState L)))

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
def readyRest (γ : Cluster) (N : Namespace) (rd : Ready) (st : NodeDriverState)
    (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan) : IProp GF :=
  iprop(∃ ms : List QMsg,
    entsRO rd.Entries' es ∗
    rd.Messages' ↦* ms.map QMsg.loc ∗
    ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N q.st ∗ msgCredits γ N q.st) ∗
    hsOpt rd.HardState' h ∗ softStateRO rd.SoftState' ∗
    ⌜∃ Lx : Int, Lx < 2 ^ 64 ∧
      (∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ Lx + 1) ∧
      ((st.delivered ++ ce).length : Int) ≤ Lx⌝ ∗
    readySnap γ N rd st ce es L)

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
      ∃ (ce : List LogEntry) (es : List EntryM) (h : HardStateM) (L : Option SnapLoan),
        committedEntriesAt rd.CommittedEntries' st.delivered.length ce ∗
        isCommittedLogLb γ (st.delivered ++ ce) ∗
        (∃ rs, readStatesPts rd.ReadStates' rs ∗
          [∗list] s ∈ rs, readStateOk γ N s.RequestCtx' s.Index') ∗
        readyRest γ N rd st ce es h L ∗
        nodeDriver n γ N (match L with
          | none => { st with
              delivered := st.delivered ++ ce
              hardState := phsNext st.hardState h
              handling := some (es, none) }
          | some l => { st with
              delivered := strip l.dlv
              hardState := phsNext st.hardState h
              handling := some (es, some l) }) }}

/-- The messages a `Ready` hands out, as the client sees them. -/
theorem api_msgs (γ : Cluster) (N : Namespace) (γn : NodeNames) (Hγr : γn.raft = γ.raft)
    (Hγb : γn.bud = γ.bud) (ms : List QMsg) :
    ⊢ clusterInv (GF := GF) γ N -∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γn.raft γn.id q.st ∗
        termLB γn.bud q.st.msg.Term') -∗
      ([∗list] q ∈ ms, rdCred γn.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) -∗
      ([∗list] q ∈ ms, stTks γn.raft q.st) -∗
      [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N q.st ∗ msgCredits γ N q.st := by
  iintro #Hci Hmo Hcr Htks
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [Hcr Htks]
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

theorem readyOut_cert (st : Storage) (es : List EntryM) (l : SnapLoan) :
    readyOut (GF := GF) st es (some l) ⊢
      readyOut st es (some l) ∗ storCert st (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) := by
  simp only [readyOut]
  iintro ⟨Hs, #Hc⟩
  isplitl [Hs]
  · iframe Hs Hc
  · iexact Hc

theorem node.wp_readyRecv_impl : node.readyRecv.spec (GF := GF) (hG := hG) := by
  intro n ch γ N st Hh
  iintro %Φ ⟨#Hrc, Hdrv⟩ HΦ
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, #Hlink, Hcfg, Htok⟩
  obtain ⟨Hnok, Hγs, Hds⟩ := Hf
  have Hγr := Hnok.1
  have Hγb := Hnok.2.1
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
  have Hlen : st.delivered.length = ds.length := by rw [← Hds, strip_length]
  iapply wp_fupd
  iapply node_ready_receive γn id n ch ds st.hardState $$ [Htok]
  · iframe Hrc' Htok
  iintro !> %rd ⟨%ce, %es, %ms, %p', %L, Hdata, Hbusy⟩
  cases L with
  | none =>
    iunfold readyDataL at Hdata
    iunfold readyData at Hdata
    icases Hdata with ⟨#Hce, #Hcom, #Hes, Happ, Hmsgs, Hmo, Hcr, Htks, ⟨%sts, Hsts, Hrs⟩,
      ⟨%h, Hhs, %Hp'⟩, -, Hss, %Hnull, #Hidx⟩
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top (ds ++ ce) $$ Hci [Hcom] with ⟨#Hlb, %HidxOk⟩
    · rw [Hγr]; iexact Hcom
    imod api_readStates γ N ⊤ CoPset.subseteq_top sts $$ Hci [Hrs] with Hrs
    · rw [← Hγr]; iexact Hrs
    ihave Hms := api_msgs γ N γn Hγr Hγb ms $$ Hci Hmo Hcr Htks
    iunfold readyIdx at Hidx
    icases Hidx with ⟨%Lx, -, %HLx⟩
    imodintro
    iapply HΦ
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
        refine ⟨Lx, HLx.1, HLx.2.1, ?_⟩
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
    iframe Hci Hlink Hcfg
    iright
    iexists es, none
    isplitr
    · ipureintro; rfl
    rw [← Hp', show ds ++ ce = dlvAfter ds ce none from rfl]; iexact Hbusy
  | some l =>
    iunfold readyDataL at Hdata
    iunfold readySnapData at Hdata
    icases Hdata with ⟨#Hce, #Hcom, #Hes, Hmsgs, Hmo, Hcr, Htks, ⟨%sts, Hsts, Hrs⟩,
      ⟨%h, Hhs, %Hp'⟩, -, Hss, #Hidx, -, Hsnap, #Hdlv, -, -, %Hfacts, Hout⟩
    obtain ⟨Hptr, Hce0, Hpre, Hlt, Hdl, Hpos, H61, Hfl, Hind⟩ := Hfacts
    subst Hce0
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top (ds ++ []) $$ Hci [Hcom] with ⟨#Hlb, -⟩
    · rw [Hγr]; iexact Hcom
    imod api_committed_lb γ N ⊤ CoPset.subseteq_top l.dlv $$ Hci [Hdlv] with ⟨#Hlbd, %Hidxd⟩
    · rw [Hγr]; iexact Hdlv
    imod api_readStates γ N ⊤ CoPset.subseteq_top sts $$ Hci [Hrs] with Hrs
    · rw [← Hγr]; iexact Hrs
    ihave Hms := api_msgs γ N γn Hγr Hγb ms $$ Hci Hmo Hcr Htks
    ihave ⟨Hout, #Hsc⟩ := readyOut_cert _ es l $$ Hout
    ihave #Hlink' := Hlink
    iunfold storageCertLink at Hlink'
    icases Hlink' with ⟨#Hl1, -⟩
    imod Hl1 $$ %_ %⊤ %CoPset.subseteq_top [Hsc] with #Hcert
    · rw [← Hγs]; iexact Hsc
    iunfold readyIdx at Hidx
    icases Hidx with ⟨%Lx, -, %HLx⟩
    imodintro
    iapply HΦ
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
        refine ⟨Lx, HLx.1, HLx.2.1, ?_⟩
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
    iframe Hci Hlink Hcfg
    iright
    iexists es, some l
    isplitr
    · ipureintro; rfl
    rw [← Hp', show l.dlv = dlvAfter ds [] (some l) from rfl]; iexact Hbusy

/-- **`StartNode(c, peers)`** (the draft's). -/
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
      storageCertLink γ N (interface.ok si) }}
    (App (App (Val #(functions StartNode [])) (Val #c)) (Val #peers))
  {{ (nd : GoInterface), RET #nd;
      R ∗ ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) }}

theorem wp_StartNode_impl (hS : EtcdGrove.StartNode.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) := by
  intro γ N c cv lok si σ hs csm R peers dq pv ps ctxs H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss
    Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid Hfl
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, Hinst, Hpeers, #Hpc, Hboot, #Hlink⟩ HΦ
  iunfold nodeBoot at Hboot
  icases Hboot with ⟨⟨%so, #Hst⟩, %Hok, Hg, #Hc0, #Hm, #Hbinv, #Htlb⟩
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, #Hci⟩
  obtain ⟨Hcfg, Hdyn, Hns, Hnx, -, Hsl, Hcert, -⟩ := Hsn
  ihave #Hok' := storCertOk_of_link γ N _ Hcert $$ Hci Hlink
  iapply (hS γ.raft .static γ.bud c cv lok si σ hs csm R peers dq pv ps ctxs γ.raft.reBoot true
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln Hal Hps Hne Hnd Hnz Hlen Hid
    Hcfg rfl Hok Hfl (fun _ => ⟨Hns, rfl⟩)) $$ [Hc Hown Hinst Hpeers Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hpeers Hpc Hm Hc0 Hbinv Htlb
    isplitl [Hg]
    · unfold bootInit; iexact Hg
    isplitr
    · unfold NsCap; imodintro; iintro %h; rw [Hns] at h; cases h
    · unfold certLink; iright; iexact Hok'
  iintro !> %nd ⟨HR, %γn, %n, %Hf, -, #Hnode, Hdrv, Hcfg, -⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd, Hsn, Hnd'⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsn, Hmd, Hsl⟩
  iapply HΦ
  iframe HR
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact Hnok
  unfold nodeDriver NodeDriverState.init
  iexists γn, cv.ID', []
  isplitr
  · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
  iframe Hci Hlink
  isplitl [Hcfg]
  · iexists 0, cfgState (GMap.listToSet ps) ∅; iexact Hcfg
  ileft
  isplitr
  · ipureintro; rfl
  iexact Hdrv

/-- **`RestartNode(c)`** (the draft's). -/
abbrev RestartNode.spec : Prop :=
  ∀ (γ : Cluster) (N : Namespace) (vs : List w64) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState) (hs : HardStateM) (csm : ConfStateM),
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
  csm.Voters' = vs → csm.VotersOutgoing' = [] → csm.Learners' = [] → csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  cv.ID' ∈ vs →
  σ.fl = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (interface.ok si) { σ with ss := ss' } -∗
            hsOpt hp hs -∗ csPts cs DFrac.discard csm al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      nodeRestartBoot γ N vs cv.ID' ∗ storageCertLink γ N (interface.ok si) }}
    (App (Val #(functions RestartNode [])) (Val #c))
  {{ (nd : GoInterface), RET #nd;
      ∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
        isNode n γ N cv.ID' ∗ nodeDriver n γ N (NodeDriverState.init (interface.ok si)) }}

theorem wp_RestartNode_impl (hS : EtcdGrove.RestartNode.spec (GF := GF) (hG := hG)) :
    RestartNode.spec (GF := GF) (hG := hG) := by
  intro γ N vs c cv lok si σ hs csm H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hv Hvo Hl Hln
    Hal Hid Hfl
  iintro %Φ ⟨#Hinit, Hc, #Hlog, #Hstor, Hown, #Hinst, Hboot, #Hlink⟩ HΦ
  iunfold nodeRestartBoot at Hboot
  icases Hboot with ⟨⟨%so, #Hst⟩, Hg, #Hc0, #Hbinv, #Htlb⟩
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, #Hci⟩
  obtain ⟨Hcfg, Hdyn, Hns, Hnx, -, Hsl, Hcert, -, Hne, Hnd, Hnz, Hlen⟩ := Hsn
  subst Hv
  ihave #Hok' := storCertOk_of_link γ N _ Hcert $$ Hci Hlink
  iapply (hS γ.raft .static γ.bud c cv lok si σ hs csm true
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hp He Hss Hpe Hhs Hne Hnd Hnz Hlen Hvo Hl Hln Hal Hcfg Hid
    Hfl (fun _ => ⟨Hns, rfl⟩)) $$ [Hc Hown Hg]
  · iframe Hinit Hc Hlog Hstor Hown Hinst Hc0 Hbinv Htlb
    isplitl [Hg]
    · unfold rnInit; iexact Hg
    · unfold certLink; iright; iexact Hok'
  iintro !> %nd ⟨%γn, %n, %Hf, #Hnode, Hdrv, Hcfg⟩
  obtain ⟨Hγr, Hγb, Hγs, Hmd, Hsn, Hnd'⟩ := Hf
  have Hnok : NodeOk γ γn := ⟨Hγr, Hγb, Hsn, Hmd, Hsl⟩
  iapply HΦ
  iexists n
  isplitr
  · ipureintro; exact Hnd'
  isplitr
  · unfold isNode
    iexists γn
    iframe Hnode Hci
    ipureintro; exact Hnok
  unfold nodeDriver NodeDriverState.init
  iexists γn, cv.ID', []
  isplitr
  · ipureintro; exact ⟨Hnok, Hγs, rfl⟩
  iframe Hci Hlink
  isplitl [Hcfg]
  · iexists 0, cfgState (GMap.listToSet csm.Voters') ∅; iexact Hcfg
  ileft
  isplitr
  · ipureintro; rfl
  iexact Hdrv

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
    iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩
      Hclose
    cases HFk : F !! k with
    | some u =>
      imod Hclose $$ [HrL Hfull Hops HF HRF] with -
      · inext
        iexists L, F, RF
        iframe HrL Hfull Hops HF HFok HRF HRk HRFok
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
        iframe HrL Hfull Hops HF HRF HRk HRFok
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
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    iexact Hau
  · -- commit: the entry holds the proposal's key
    iintro %e ⟨HrL, #He, %HeIdx⟩
    icases Hucl with ⟨-, Hcommit⟩
    iunfold entDataIs at He
    iunfold propDataIs at He
    icases He with ⟨⟨%Hek, -⟩, -⟩
    obtain ⟨Hkey, Hnf', -⟩ := Hek
    obtain ⟨Hty, Hd⟩ := entKey_inj Hkey
    have Hx : LogEntry.ofEntryM e = ⟨e.Term', ty, data⟩ := by
      unfold LogEntry.ofEntryM; rw [Hty, Hd]
    have Hxf : ¬ (LogEntry.ofEntryM e).isFiller := fun h => Hnf' ((isFiller_ofEntryM e).1 h)
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
      ipureintro; rfl
    imod Hback with -
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L ++ [e], F, RF
      rw [Hopsn, Hstrip]
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
      ipureintro; exact IdxOk_snoc Hidx HeIdx
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

/-- **`node.Propose(ctx, data)`** (the draft's). -/
abbrev node.Propose.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (data_sl : GoSlice) (data : List w8)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      data_sl ↦*□ data ∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64), ownCommittedOps γ (ops ++ [⟨t, W32 0, data⟩]), COMM True }> }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok ctx))) (Val #data_sl))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∨ errStopped err ∨ errProposalDropped err ∨ ctxErr cd err }}

theorem node.wp_Propose_impl (hP : EtcdGrove.node.Propose.spec (GF := GF) (hG := hG)) :
    node.Propose.spec (GF := GF) (hG := hG) := by
  intro n γ N id data_sl data ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, #Hd, Hau⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, #Hci⟩
  obtain ⟨Hγr, -⟩ := Hf
  by_cases Hne : data = []
  · iapply (hP γn id n data_sl data (fun _ => iprop(True)) ctx cd) $$ []
    · iframe Hinit Hrn Hctx Hd
      ileft; ipureintro; exact Hne
    iintro !> %err #Herr
    iapply HΦ
    iapply propErr_api $$ Herr
  have Hnf : ¬ Filler (W32 0) data := fun h => Hne h.1
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, #Hinv, -⟩
  imod api_key_register γ N ⊤ CoPset.subseteq_top (entKey (W32 0) data) $$ Hci with #Hpi
  ihave Hau1 := api_propAu1 γ N (W32 0) data Hnf HNs $$ Hinv Hau
  iapply (hP γn id n data_sl data (fun _ => iprop(True)) ctx cd) $$ [Hau1]
  · iframe Hinit Hrn Hctx Hd
    iright
    unfold propArg
    rw [Hγr]
    iframe Hpi Hau1
  iintro !> %err #Herr
  iapply HΦ
  iapply propErr_api $$ Herr

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
    (R : IProp GF) (HE : ↑(raftN γ) ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γ -∗ rdFresh γ c -∗ readAu γ Qr -∗ R -∗
      (∀ P, R -∗ ghostVar γ.reRLog (1 : Qp).half P ={(E \ ↑(raftRegN γ)) \ ↑(raftLogN γ)}=∗
        R ∗ ghostVar γ.reRLog (1 : Qp).half P ∗ □ Qr P) ={E}=∗
      R ∗ ∃ Lc, readReq γ c Lc ∗ isRead γ c Qr := by
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
  imod Hfire $$ %P HR Hv with ⟨HR, Hv, #HQ⟩
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
  unfold isRead
  iexists γq, P
  iframe Hel Hsp

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
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩ Hclose
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
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
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
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
      ipureintro; exact Hidx
    imodintro
    unfold qrOf
    iexact HQ

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
  icases Hctx' with ⟨%γq, #Hel, #Hsp, #Hau⟩
  ihave #HrAu := api_readAu γ N Q HNs $$ Hinv Hau
  iunfold apiInv at Hinv
  unfold apiInvBody
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, >#HFok, >HRF, >#HRk, #HRFok⟩
    Hclose
  cases HRc : RF !! c with
  | some u =>
    ihave #HRk' := HRk
    iunfold rdKeys at HRk'
    ihave #Hk := HRk' $$ %c %(by cases u; exact HRc)
    iunfold readKey at Hk
    icases Hk with ⟨%γq', %Lc, -, #Hrq⟩
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, RF
      iframe HrL Hfull Hops HF HFok HRF HRk HRFok
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
    imod read_deposit_with γ.raft (⊤ \ ↑(apiN N)) c (qrOf Q)
        iprop(rLog γ.raft L ∗ monoListAuthOwn γ.ops (1 : Qp).half (opsOf (strip L))) HrN
      $$ Hcinv [Hfr] HrAu [HrL Hops] [] with ⟨⟨HrL, Hops⟩, %Lc, #Hrq, #Hrd⟩
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
      unfold qrOf; iexact HQ
    imod Hclose $$ [HrL Hfull Hops HF HRF] with -
    · inext
      iexists L, F, GMap.insert c () RF
      iframe HrL Hfull Hops HF HFok HRF
      isplitr
      · ipureintro; exact Hidx
      isplitr
      · unfold rdKeys
        imodintro
        iintro %c' %Hc'
        rcases (GMap.lookup_insert_Some RF c c' () ()).1 Hc' with ⟨rfl, -⟩ | ⟨-, h⟩
        · unfold readKey
          iexists γq, Lc
          iframe Hel Hrq
        · iapply HRk $$ %c' %h
      · unfold rdFreshOk
        imodintro
        iintro %c' %Hc'
        rcases (GMap.lookup_insert_Some RF c c' () ()).1 Hc' with ⟨rfl, -⟩ | ⟨-, h⟩
        · unfold readDep
          iexists γq, Q
          iframe Hel Hsp Hrd
        · iapply HRFok $$ %c' %h
    imodintro
    iexists Lc
    iexact Hrq

/-- **`node.ReadIndex(ctx, rctx)`** (the draft's). -/
abbrev node.ReadIndex.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (rctx : GoSlice) (c : List w8)
    (Q : List LogEntry → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      rctx ↦*□ c ∗ isReadCtx γ N c Q ∗ readCredit γ }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok ctx))) (Val #rctx))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

theorem node.wp_ReadIndex_impl (hR : EtcdGrove.node.ReadIndex.specReq (GF := GF) (hG := hG)) :
    node.ReadIndex.spec (GF := GF) (hG := hG) := by
  intro n γ N id rctx c Q ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, #Hrctx, #Hrc, Hcred⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, #Hci⟩
  obtain ⟨Hγr, -⟩ := Hf
  imod api_read_ensure γ N c Q $$ Hci Hrc with ⟨%Lc, #Hrq⟩
  iapply (hR γn id n rctx c Lc ctx cd) $$ [Hcred]
  · iframe Hinit Hrn Hctx Hrctx
    rw [Hγr]
    iframe Hrq
    unfold readCredit readCredits
    iexact Hcred
  iintro !> %err #Herr
  iapply HΦ
  iexact Herr

end read

/-! ## Conf changes -/

section cc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The client's conf-change update, at the bytes raft marshaled. -/
theorem au_cc_fix (γ : Cluster) (N : Namespace) (ty : w32) (o : ConfChangeIM) (bs : List w8)
    (Hm : MarshalsConfChange (some o) bs) :
    AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps (GF := GF) γ ops }> @ ⊤ \ ↑N, ∅
       <{ ∀∀ (t : w64) (bs' : List w8), ⌜MarshalsConfChange (some o) bs'⌝ ∗
            ownCommittedOps γ (ops ++ [⟨t, ty, bs'⟩]), COMM True }> ⊢
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
    iframe Hown
    ipureintro; exact Hm

/-- **`node.ProposeConfChange(ctx, cc)`** (the draft's). -/
abbrev node.ProposeConfChange.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (c : GoInterface) (o : ConfChangeIM)
    (dq : DFrac) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      ownConfChangeI c dq (some o) ∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
              ownCommittedOps γ (ops ++ [⟨t, confChangeEntryType (some o), bs⟩]),
            COMM True }> }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownConfChangeI c dq (some o) ∗ nodeErr cd err }}

theorem node.wp_ProposeConfChange_impl
    (hP : EtcdGrove.node.ProposeConfChange.spec (GF := GF) (hG := hG)) :
    node.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  intro n γ N id c o dq ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, Hcc, Hau⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, #Hci⟩
  obtain ⟨Hγr, -⟩ := Hf
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, #Hinv, -⟩
  iapply (hP γn id n c o dq ctx cd) $$ [Hcc Hau]
  · iframe Hinit Hrn Hctx Hcc
    unfold ccPropArg
    iintro %bs %Hm
    by_cases Hf : Filler (confChangeEntryType (some o)) bs
    · imodintro; ileft; ipureintro; exact Hf
    imod api_key_register γ N ⊤ CoPset.subseteq_top
      (entKey (confChangeEntryType (some o)) bs) $$ Hci with #Hpi
    ihave Hau1 := au_cc_fix γ N (confChangeEntryType (some o)) o bs Hm $$ Hau
    ihave Hau1 := api_propAu1 γ N (confChangeEntryType (some o)) bs Hf HNs $$ Hinv Hau1
    imodintro
    iright
    iexists (fun _ => iprop(True))
    rw [Hγr]
    iframe Hpi Hau1
  iintro !> %err ⟨Hcc, #Herr⟩
  iapply HΦ
  iframe Hcc Herr

end cc

/-! ## Advance, Step, Tick, TransferLeadership -/

section misc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Advance()`** (the draft's). -/
abbrev node.Advance.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan),
  st.handling = some (es, L) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ nodeDriver n γ N st ∗
      advReceipt st.storage es L }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver n γ N { st with handling := none } ∗
      match L with
      | none => ∃ x : w64, storFloor st.storage x ∗ ⌜(st.delivered.length : Int) ≤ uint.Z x⌝
      | some _ => True }}

theorem node.wp_Advance_impl (hA : EtcdGrove.node.Advance.spec (GF := GF) (hG := hG)) :
    node.Advance.spec (GF := GF) (hG := hG) := by
  intro n γ N st es L Hh
  iintro %Φ ⟨#Hinit, Hdrv, Hrc⟩ HΦ
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, #Hlink, ⟨%ca, %cfg, Hcfg⟩, Htok⟩
  obtain ⟨Hnok, Hγs, Hds⟩ := Hf
  have Hmd := Hnok.2.2.2.1
  icases Htok with (⟨%Hh', -⟩ | ⟨%es0, %L0, %Hh', Htok⟩)
  · rw [Hh] at Hh'; cases Hh'
  rw [Hh] at Hh'
  cases Hh'
  iapply (hA γn id n ds es ca cfg st.hardState L
    (fun h => by rw [Hmd] at h; cases h)) $$ [Htok Hrc Hcfg]
  · iframe Hinit Htok Hcfg
    rw [Hγs]; iexact Hrc
  iintro !> ⟨Hdrv, Hcfg, #Hw⟩
  iapply HΦ
  isplitl [Hdrv Hcfg]
  · unfold nodeDriver
    iexists γn, id, ds
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, Hds⟩
    iframe Hci Hlink
    isplitl [Hcfg]
    · iexists ca, cfg; iexact Hcfg
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  cases L with
  | none =>
    simp only
    iunfold reqOf at Hw
    iunfold reqWit at Hw
    icases Hw with ⟨%x, #Hx, %Hle⟩
    iexists x
    rw [← Hγs]
    iframe Hx
    ipureintro
    rw [← Hds, strip_length]; exact Hle
  | some l => simp only; itrivial

/-- (open) **Tick credits** (raft's `tickCred`: time receipts). -/
def tickCredit (_γ : Cluster) (n : Nat) : IProp GF := ⧗ n

theorem tickCredit_intro_impl (γ : Cluster) (n : Nat) : ⧗ n ⊢ tickCredit (GF := GF) γ n := by
  unfold tickCredit; exact .rfl

theorem tickCredit_zero_impl (γ : Cluster) : ⊢ |==> tickCredit (GF := GF) γ 0 := by
  unfold tickCredit; exact receipt_zero

/-- **`node.Tick()`** (the draft's). -/
abbrev node.Tick.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ tickCredit γ 1 }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Tick")) (Val #()))
  {{ RET #(); True }}

theorem node.wp_Tick_impl (hT : EtcdGrove.node.Tick.spec (GF := GF) (hG := hG)) :
    node.Tick.spec (GF := GF) (hG := hG) := by
  intro n γ N id
  iintro %Φ ⟨#Hinit, #Hnode, Hcr⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hrn, -⟩
  iapply (hT γn id n) $$ [Hcr]
  · iframe Hinit Hrn
    unfold tickCredit tickCred; iexact Hcr
  iexact HΦ

/-- **`node.TransferLeadership(ctx, lead, transferee)`** (the draft's). -/
abbrev node.TransferLeadership.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (lead transferee : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      leaderTransferOn γ N }}
    (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"TransferLeadership"))
      (Val #(interface.ok ctx))) (Val #lead)) (Val #transferee))
  {{ RET #(); True }}

theorem node.wp_TransferLeadership_impl
    (hT : EtcdGrove.node.TransferLeadership.spec (GF := GF) (hG := hG)) :
    node.TransferLeadership.spec (GF := GF) (hG := hG) := by
  intro n γ N id lead transferee ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, Hx⟩ HΦ
  iunfold leaderTransferOn at Hx
  icases Hx with %Hx
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, -⟩
  obtain ⟨Hγr, -⟩ := Hf
  iapply (hT γn id n lead transferee ctx cd (by rw [Hγr]; exact Hx)) $$ []
  · iframe Hinit Hrn Hctx
  iexact HΦ

/-- (open) **A message `node.Step` takes** at the node `id`: raft's (`stepP`), for any node names
of the cluster's (`NodeOk`). -/
def stepIn (γ : Cluster) (_N : Namespace) (id : w64) (ml : Loc) : IProp GF :=
  iprop(∀ γn : NodeNames, ⌜NodeOk γ γn⌝ -∗ stepP γn id ml)

/-- **`node.Step(ctx, m)`** (the draft's). -/
abbrev node.Step.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      stepIn γ N id ml }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
      (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

theorem node.wp_Step_impl (hS : EtcdGrove.node.Step.spec (GF := GF) (hG := hG)) :
    node.Step.spec (GF := GF) (hG := hG) := by
  intro n γ N id ml ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, Hin⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, -⟩
  iapply (hS γn id n ml ctx cd) $$ [Hin]
  · iframe Hinit Hrn Hctx
    iunfold stepIn at Hin
    iapply Hin
    ipureintro; exact Hf
  iexact HΦ


/-- A list without repeats is a permutation of the elements of its set. -/
theorem perm_elements_listToSet' (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

/-- **`node.ApplyConfChange(cc)`** in a static cluster (the draft's). -/
abbrev node.ApplyConfChange.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (vs : List w64)
    (snapOk : List LogEntry → List w8 → Prop) (c : GoInterface) (o : ConfChangeIM),
  CCShrink (GMap.listToSet vs) (ccV2Of o).1 (ccV2Of o).2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      isStaticCluster γ N vs snapOk ∗ ownConfChangeI c DFrac.discard (some o) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp; csPts csp (DFrac.own 1) cs true ∗
      ⌜cs.Voters' ≡ₚ vs ∧ (∀ k ∈ cs.Learners', k ∉ vs) ∧ cs.VotersOutgoing' = [] ∧
        cs.LearnersNext' = [] ∧ cs.AutoLeave' = false⌝ }}

theorem node.wp_ApplyConfChange_impl
    (hA : EtcdGrove.node.ApplyConfChange.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro n γ N id vs so c o Hsh
  iintro %Φ ⟨#Hinit, #Hnode, #Hst, Hcc⟩ HΦ
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, -⟩
  obtain ⟨Hcfg, -, -, -, -, -, -, -, -, Hnd, -⟩ := Hsn
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hnok, #Hrn, -⟩
  obtain ⟨Hγr, -, -, Hmd, -⟩ := Hnok
  iapply (hA γn id n c o [] 0 (cfgState ∅ ∅) 0 ⟨W64 0, W64 0, W32 0, []⟩ (cfgState ∅ ∅)
    (fun _ => by rw [Hγr, Hcfg]; exact Hsh) (fun dec c0 h0 h1 h => by rw [Hmd] at h; cases h))
    $$ [Hcc]
  · iframe Hinit Hrn Hcc
    ileft; ipureintro; exact Hmd
  iintro !> %csp %cs ⟨Hcs, Hor⟩
  icases Hor with (⟨-, %Hs⟩ | ⟨%Hd, -⟩)
  · iapply HΦ
    iframe Hcs
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := Hs
    rw [Hγr, Hcfg] at h1 h2
    exact ⟨h1.trans (perm_elements_listToSet' vs Hnd).symm,
      fun k hk h => h2 k hk ((GMap.elem_of_list_to_set _ _).2 h), h3, h4, h5⟩
  · exfalso; rw [Hmd] at Hd; cases Hd

/-- **Stepping a sent message** (the draft's `stepIn_intro`). -/
theorem stepIn_intro_impl (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (st : MsgSt) :
    (st.msg.Type' = MsgProp → st.ctx = []) →
    (st.msg.Type' ≠ MsgProp → NetMsgOk id ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∧
      st.msg.Type' ≠ MsgPreVote ∧ st.msg.Type' ≠ MsgTransferLeader) →
    (st.msg.Type' = MsgSnap → ∃ sv, st.snap = some sv ∧ uint.Z sv.Metadata'.Index' < 2 ^ 61) →
    st.msg.To' = id →
    sentMsg (GF := GF) γ N st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ∗ tickCredit γ (if st.msg.Type' = MsgTimeoutNow then 1 else 0) ⊢
    |==> stepIn γ N id ml := by
  intro Hpc Hnet Hsnap _
  iintro ⟨#Hsent, Hm, Hcr, Htc⟩
  iunfold sentMsg at Hsent
  icases Hsent with ⟨-, ⟨%src, #Hraft⟩, #Hlb⟩
  ihave #Hdat := isRaftMsg_dat γ.raft src st $$ Hraft
  iunfold isRaftMsg at Hraft
  icases Hraft with ⟨-, -, ⟨%a, %Habs, #Hl⟩, -, %Hra⟩
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
    iintro %γn %Hnok
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
      iExactEq H
      rw [Hpc Hp]
    simp only [stTks, if_pos Hp]
    rw [Hγr]
    iexact Htk
  · imod msgPtsC_persist_els $$ Hm with Hm
    obtain ⟨Hnok', Hnpv, Hntl⟩ := Hnet Hp
    imodintro
    unfold stepIn
    iintro %γn %Hnok
    obtain ⟨Hγr, Hγb, Hsi, -, Hsl⟩ := Hnok
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
      exact ⟨fun h => absurd h Hnpv, fun h => absurd h Hntl, fun _ => Hsi⟩
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
    unfold tickCredit tickCred
    iexact Htc

end misc

end ApiImpl
end EtcdGrove
end Perennial
