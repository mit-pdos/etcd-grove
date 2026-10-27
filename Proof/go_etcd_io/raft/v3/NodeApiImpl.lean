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

/-- A read context's result predicate, as raft's read records it: the context's predicate (named
by `γq`) holds of the requested entries of the log. -/
def qrOf (γq : GName) (L : List EntryM) : IProp GF :=
  iprop(∃ Q : List LogEntry → IProp GF, savedPredOwn γq DFrac.discard Q ∗ □ Q (opsOf (strip L)))

instance qrOf_persistent (γq : GName) (L : List EntryM) : Persistent (qrOf (GF := GF) γq L) := by
  unfold qrOf; infer_instance

/-- A read context deposited in raft: committed (`γ.ctxs`) to the predicate `γq` names, its read
deposited at `Lc` with the result predicate `qrOf γq`. -/
def readDep (γ : Cluster) (c : List w8) : IProp GF :=
  iprop(∃ (γq : GName) (Lc : List EntryM), c ↪[γ.ctxs]□ γq ∗ readReq γ.raft c Lc ∗
    isRead γ.raft c (qrOf γq))

instance readDep_persistent (γ : Cluster) (c : List w8) : Persistent (readDep (GF := GF) γ c) := by
  unfold readDep; infer_instance

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

instance rdFreshOk_persistent (γ : Cluster) (RF : GMap (List w8) Unit) :
    Persistent (rdFreshOk (GF := GF) γ RF) := by
  unfold rdFreshOk; infer_instance

/-- **The adapter's invariant** (see the file header). -/
def apiInvBody (γ : Cluster) : IProp GF :=
  iprop(∃ (L : List EntryM) (F RF : GMap (List w8) Unit),
    rLog γ.raft L ∗ ⌜IdxOk L⌝ ∗
    monoListAuthOwn γ.full 1 (strip L) ∗ monoListAuthOwn γ.ops (1 : Qp).half (opsOf (strip L)) ∗
    ghostMapAuth γ.raft.reFresh 1 F ∗ freshOk γ F ∗
    ghostMapAuth γ.raft.reRdFresh 1 RF ∗ rdFreshOk γ RF)

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
  iinv Hinv with ⟨%L, %F, %RF, >HrL, >%Hidx, >Hfull, >Hops, >HF, #HFok, >HRF, #HRFok⟩ Hclose
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
      iframe HrL Hfull Hops HF HFok HRF HRFok
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
      iframe HrL Hfull Hops HF HFok HRF HRFok
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

end ApiImpl
end EtcdGrove
end Perennial
