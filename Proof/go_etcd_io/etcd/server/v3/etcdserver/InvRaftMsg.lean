/-
raft v3.7's `raftpb` messages as the server's raft wrapper (`raft.go`) reads them: a
`Message`'s recipient and type, a `HardState`'s three fields. Lean-first (no Rocq counterpart).
As `entryAt` (`InvRaftpb.lean`), since stage R6 of the raft v3.7 retarget (2026-10-16, D9:
`notes/decisions.md`, "The swap") the server's predicates are definitions over raft's own
(`Proof/go_etcd_io/raft/v3/InvPb.lean`, `InvPbLog.lean`): `msgAt m to ty` is a message raft
built, read-only for good (`msgOwn m □ st`), of which the wrapper reads `To` and `Type`;
`hardStateAt p hs` is raft's nil-or-read-only hard state `hsOpt p hs.toM`, the server keeping
its model `HardStateModel` (`rnReadyP`, `isRNWal`). The lemmas below restate raft's getter and
helper specs in the shape the wrapper's proofs use, taking the raft spec as a hypothesis (as
raft's `LemmasMiscR.lean` does for `hsOpt`'s getters, which they use).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.raft.v3.LemmasMiscR
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A `HardState`'s fields (each absent reads as 0; the server's model, raft's is `HardStateM`). -/
structure HardStateModel where
  term : w64
  vote : w64
  commit : w64

/-- The empty `HardState` (`raft.IsEmptyHardState`). -/
def HardStateModel.empty : HardStateModel := ⟨W64 0, W64 0, W64 0⟩

/-- The server's hard state as raft's record (`HardStateM`: what the getters return). -/
def HardStateModel.toM (hs : HardStateModel) : HardStateM := ⟨hs.term, hs.vote, hs.commit⟩

-- Projection lemmas, `@[simp, word_unfold]` (`Proof/go_etcd_io/raft/v3/ProjSimps.lean`).
proj_simps Perennial.EtcdGrove.HardStateModel.toM

/-- Raft's record as the server's hard state (2026-10-16, stage R7b). -/
def HardStateModel.ofM (h : HardStateM) : HardStateModel := ⟨h.Term', h.Vote', h.Commit'⟩

proj_simps Perennial.EtcdGrove.HardStateModel.ofM

@[simp] theorem HardStateModel.toM_ofM (h : HardStateM) : (HardStateModel.ofM h).toM = h := by
  cases h; rfl

theorem HardStateModel.toM_zero_iff (hs : HardStateModel) :
    hs.toM = HardStateM.mk (W64 0) (W64 0) (W64 0) ↔ hs = HardStateModel.empty := by
  cases hs
  simp only [HardStateModel.toM, HardStateModel.empty, HardStateM.mk.injEq,
    HardStateModel.mk.injEq]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-! ## Raft's read-only predicates are persistent

(Candidates for raft's `InvPb.lean`, which states only `entRO`'s, `hsRO`'s and `csPts`'s.) -/

instance csOptA_discard_persistent (p : Loc) (c : ConfStateM) :
    Persistent (csOptA (GF := GF) p DFrac.discard c) := by
  unfold csOptA; infer_instance

instance smPts_discard_persistent (p : Loc) (md : SnapshotMetadataM) :
    Persistent (smPts (GF := GF) p DFrac.discard md) := by
  unfold smPts; infer_instance

instance smOpt_discard_persistent (p : Loc) (md : SnapshotMetadataM) :
    Persistent (smOpt (GF := GF) p DFrac.discard md) := by
  unfold smOpt; infer_instance

instance ownSnapM_discard_persistent (p : Loc) (s : SnapshotM) :
    Persistent (ownSnapM (GF := GF) p DFrac.discard s) := by
  unfold ownSnapM; infer_instance

instance snapOpt_discard_persistent (p : Loc) (o : Option SnapshotM) :
    Persistent (snapOpt (GF := GF) p DFrac.discard o) := by
  cases o <;> simp only [snapOpt] <;> infer_instance

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxHeartbeats 4000000 in
instance msgOwn_discard_persistent (l : Loc) (ms : MsgSt) :
    Persistent (msgOwn (GF := GF) l DFrac.discard ms) := by
  unfold msgOwn msgPts msgPtsC
  simp only [Bool.false_eq_true, ↓reduceIte]
  infer_instance

/-! ## The server's predicates -/

/-- `m` is a (non-nil) read-only message to `to` of type `ty` (the fields the raft wrapper
reads): a message raft built, read-only for good (D3: `msgOwn`, whose entries are read-only
too), of some content `st`. -/
def msgAt (m : Loc) (to : w64) (ty : w32) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ ⌜st.msg.To' = to ∧ st.msg.Type' = ty⌝)

instance msgAt_persistent (m : Loc) (to : w64) (ty : w32) :
    Persistent (msgAt (GF := GF) m to ty) := by
  unfold msgAt; infer_instance

/-- `p` is a read-only `*HardState` modelled by `hs`; nil reads as the empty one (raft's
`hsOpt`). -/
def hardStateAt (p : Loc) (hs : HardStateModel) : IProp GF := hsOpt p hs.toM

instance hardStateAt_persistent (p : Loc) (hs : HardStateModel) :
    Persistent (hardStateAt (GF := GF) p hs) := by
  unfold hardStateAt; infer_instance

end defs

/-! ## The getters and helpers, in the server's terms

(Under raft's package assumptions, as raft's `wp_hsOpt_GetCommit` is; the server's
`etcdserver.Assumptions` provides them.) -/

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.GetTerm()` of a hard state at `hs` (nil: the empty one) is `hs.term`. -/
theorem wp_hardStateAt_GetTerm
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG)) :
    ∀ (p : Loc) (hs : HardStateModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hardStateAt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #hs.term; True }} := by
  intro p hs
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold hardStateAt at H
  iapply wp_hsOpt_GetTerm wp_GetTerm p hs.toM $$ [$Hi $H]
  inext
  iintro -
  ispecialize HΦ $$ []
  · itrivial
  iExactEq HΦ
  rfl

/-- `p.GetCommit()` of a hard state at `hs` (nil: the empty one) is `hs.commit`. -/
theorem wp_hardStateAt_GetCommit
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    ∀ (p : Loc) (hs : HardStateModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hardStateAt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #hs.commit; True }} := by
  intro p hs
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold hardStateAt at H
  iapply wp_hsOpt_GetCommit wp_GetCommit p hs.toM $$ [$Hi $H]
  inext
  iintro -
  ispecialize HΦ $$ []
  · itrivial
  iExactEq HΦ
  rfl

/-- `raft.IsEmptyHardState(st)` of a hard state at `hs` (nil: the empty one) decides whether
`hs` is the empty one (raft's `IsEmptyHardState.spec`, over the record). -/
theorem wp_hardStateAt_IsEmptyHardState
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG)) :
    ∀ (st : Loc) (hs : HardStateModel),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hardStateAt st hs }}
      (App (Val #(functions IsEmptyHardState [])) (Val #st))
    {{ (r : Bool), RET #r; ⌜r = true ↔ hs = HardStateModel.empty⌝ }} := by
  intro st hs
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold hardStateAt at H
  iapply wp_IsEmptyHardState st hs.toM $$ [$Hi $H]
  inext
  iintro -
  iapply HΦ
  ipureintro
  rw [← HardStateModel.toM_zero_iff]
  cases hs
  simp only [HardStateModel.toM, HardStateM.mk.injEq]
  exact decide_eq_true_iff

/-- `raft.IsEmptySnap(nil)` is `true` (raft's `IsEmptySnap.spec` at `none`): the wrapper's
`Ready` carries no snapshot (`rnReadyData`). -/
theorem wp_IsEmptySnap_nil (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
      (App (Val #(functions IsEmptySnap [])) (Val #(null : Loc)))
    {{ RET #true; True }} := by
  iintro %Φ #Hi HΦ
  iapply wp_IsEmptySnap null DFrac.discard none $$ [$Hi]
  · simp only [snapOpt]; ipureintro; trivial
  inext
  iintro %b ⟨%Hb, -⟩
  simp only [Option.elim] at Hb
  subst Hb
  iapply HΦ
  itrivial

end lemmas

end EtcdGrove
end Perennial
