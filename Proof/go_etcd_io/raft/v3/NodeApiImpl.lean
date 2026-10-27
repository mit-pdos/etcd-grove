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
    isCommitted γ.raft γ.raft.reBoot ∗ bootMarshal ps ctxs γ.raft.reBoot)

/-- The client's part of a new cluster, built in raft's allocation (`allocClientGen`). -/
def allocOut (N : Namespace) (boot : List LogEntry) (γr : RaftNames) : IProp GF :=
  iprop(∃ γ : Cluster, ⌜γ.raft = γr⌝ ∗ apiInv γ N ∗ ownCommittedOps γ boot ∗ ownReadCtxs γ ∅)

/-- The adapter's part of raft's allocation: its ghost state and invariant, raft's standing update
from it. -/
theorem api_alloc_client (N : Namespace) (E : CoPset) (cfg : GSet w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) (HB : BootLog ps ctxs boot) :
    ⊢ allocClientGen (GF := GF) E cfg none (fun _ _ => True) (LogEntry.toEntries boot 0)
        (allocOut N boot) (N .@ "raft") := by
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
  let γ : Cluster := ⟨γr, γf, γo, γc⟩
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
  isplitr; · ipureintro; rfl
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
    BootLog ps ctxs boot → ps.Nodup → ps ≠ [] → W64 0 ∉ ps →
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      |={E}=> ∃ γ, ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        [∗list] id ∈ ps, nodeBoot γ N ps ctxs id := by
  intro HB Hnd Hne Hnz
  iintro #Hm
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
  ihave Hcl := api_alloc_client (GF := GF) N E (GMap.listToSet ps) ps ctxs boot HB
  imod ownRaftGhost_alloc_core E (GMap.listToSet ps) (GMap.listToSet ps) none (fun _ _ => True)
    (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot) (some (GMap.listToSet ps))
    (fun T hT => by cases hT; exact ⟨GMap.subseteq_refl _, rfl⟩) true (fun _ => Hbne)
    false (fun h => by cases h) (fun _ _ => True) (fun _ => none) (N .@ "raft") Hcne Hnz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, Hboot, -, Hns, Hnx, -, -, HNs⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #Hinv, Hops, Hctx⟩
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
  iframe Hg Hc0 Hm Hcinv Hinv
  isplitr
  · ipureintro; exact ⟨Hcfg, Hdyn, Hok, Hns, Hnx⟩
  ipureintro; exact HNs

end alloc

end ApiImpl
end EtcdGrove
end Perennial
