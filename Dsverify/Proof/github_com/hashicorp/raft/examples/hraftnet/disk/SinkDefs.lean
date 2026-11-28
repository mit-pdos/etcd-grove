/-
(hraft_robust R3) A `*Snaps`'s sinks (`snap.go`'s `Sink`), as `examples/snapstore`'s (`snapstore/Base.lean`):
`sinkCore` (the read-only part: the store, every metadata field but `Size`), `sinkSt` (the owner's state: open
with the bytes written, or closed), `sinkOwn` (with the commit the client fixed at `Create`), and the commit
`snapCommitAU` a `Close` runs.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SnapLemmas

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode github_com.hashicorp.raft proto EtcdGrove

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **The client's commit of a snapshot `(m, b)`** (`isSnapStore`'s `Create`, its close obligation given): the
latest becomes `newerSnap old m b`, with the result `R`. -/
def snapCommitAU (g : SnapGen) (m : SnapshotMeta) (b : List w8) (R : IProp GF) : IProp GF :=
  iprop(|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, snapsOwn g old ∗
    (snapsOwn g (newerSnap old m b) ={∅,⊤ \ ↑storeN}=∗ R))

/-- The read-only part of the sink `k` of `Create(ver, idx, term, cfg, cfgIdx, _)` with id `id` on the store `s`
(persistent): every field of its metadata but `Size`. -/
def sinkCore (k s : Loc) (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (id : GoString)
    (ver idx term cfgIdx : w64) (cfg : Configuration) : IProp GF :=
  iprop(k.[Sink, go!"st"] ↦□ s ∗ isSnaps g s Qc Wf ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Version"] ↦□ ver ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"ID"] ↦□ id ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Index"] ↦□ idx ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Term"] ↦□ term ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Peers"] ↦□ slice.nil ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Configuration"] ↦□ cfg ∗
    (k.[Sink, go!"meta"]).[SnapshotMeta, go!"ConfigurationIndex"] ↦□ cfgIdx ∗
    ⌜k.[Sink, go!"meta"] ≠ null⌝)

instance sinkCore_persistent k s g Qc Wf id ver idx term cfgIdx cfg :
    Persistent (sinkCore (GF := GF) k s g Qc Wf id ver idx term cfgIdx cfg) := by
  unfold sinkCore; infer_instance

/-- The owner's state of the sink `k`: open with `bs` written (`some bs`), or closed (`none`). -/
def sinkSt (k : Loc) : Option (List w8) → IProp GF
  | some bs => iprop(∃ dsl : GoSlice, k.[Sink, go!"data"] ↦ dsl ∗ dsl ↦* bs ∗
      ownSliceCap w8 dsl (DFrac.own 1) ∗ k.[Sink, go!"closed"] ↦ false ∗
      (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Size"] ↦ W64 0)
  | none => iprop(k.[Sink, go!"closed"] ↦ true)

/-- The owner's state of the sink `k` as `isSink`'s `own`: `sinkSt`, and while open the commit `Cm` the client
fixed at `Create`. -/
def sinkOwn (k : Loc) (Cm : IProp GF) : Option (List w8) → IProp GF
  | some bs => iprop(sinkSt k (some bs) ∗ Cm)
  | none => sinkSt k none

/-- `snapsMemAt`'s last conjunct, by name (so that a substitution in it is not simplified away). -/
def snapTail (lt : SLat) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice) : IProp GF :=
  match lt with
  | none => iprop(⌜has = false⌝)
  | some (m, b) => iprop(⌜has = true⌝ ∗ metaRep mv m b.length ∗ dt ↦*□ b)

theorem snapsMemAt_open (s : Loc) (nid : w64) (lt : SLat) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice) :
    snapsMemAt (GF := GF) s ⟨nid, lt⟩ has mv dt ⊢
      s.[Snaps, go!"has"] ↦ has ∗ s.[Snaps, go!"meta"] ↦ mv ∗ s.[Snaps, go!"data"] ↦ dt ∗
      s.[Snaps, go!"nextID"] ↦ nid ∗ snapTail lt has mv dt := by
  unfold snapsMemAt snapTail; iintro H; iexact H

theorem snapsMemAt_close (s : Loc) (nid : w64) (lt : SLat) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice) :
    s.[Snaps, go!"has"] ↦ has ∗ s.[Snaps, go!"meta"] ↦ mv ∗ s.[Snaps, go!"data"] ↦ dt ∗
      s.[Snaps, go!"nextID"] ↦ nid ∗ snapTail lt has mv dt ⊢
    snapsMemAt (GF := GF) s ⟨nid, lt⟩ has mv dt := by
  unfold snapsMemAt snapTail; iintro H; iexact H

/-- The fields `has`, `meta`, `data` at the latest `lat` (the lock holder's view of them). -/
def latCell (lat : SnapLatest) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice) : IProp GF :=
  match lat with
  | none => iprop(⌜has = false⌝)
  | some (m, b) => iprop(⌜has = true ∧ mv = m⌝ ∗ dt ↦*□ b)

instance latCell_persistent lat has mv dt : Persistent (latCell (GF := GF) lat has mv dt) := by
  unfold latCell; split <;> infer_instance

/-- The lock invariant's memory shows the latest. -/
theorem snapMem_view (s : Loc) (nid : w64) (lt : SLat) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice)
    (lat : SnapLatest) (hmv : latMv lat mv) :
    snapsMemAt (GF := GF) s ⟨nid, lt⟩ has mv dt ∗ latRep lat lt ⊢
      snapsMemAt s ⟨nid, lt⟩ has mv dt ∗ latCell lat has mv dt := by
  rcases lat with _ | ⟨m, b⟩ <;> rcases lt with _ | ⟨sm, b'⟩ <;>
    simp only [latRep, latCell, snapsMemAt, latMv] at hmv ⊢
  · iintro ⟨⟨H1, H2, H3, H4, %Hh⟩, -⟩
    isplitl [H1 H2 H3 H4]
    · iframe; ipureintro; exact Hh
    · ipureintro; exact Hh
  · iintro ⟨-, H⟩; iexfalso; iexact H
  · iintro ⟨-, H⟩; iexfalso; iexact H
  · iintro ⟨⟨H1, H2, H3, H4, %Hh, #Hmr, #Hd⟩, %Hb, -⟩
    subst Hb
    isplitl [H1 H2 H3 H4]
    · iframe; iframe #; ipureintro; exact Hh
    · iframe #; ipureintro; exact ⟨Hh, hmv⟩

/-- `ErrNoSnapshot` holds a non-nil error, for good. -/
theorem dk_errNoSnapshot_ok :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ⊢
      ∃ e : GoInterface, globalAddr ErrNoSnapshot ↦□ e ∗ ⌜e ≠ interface.nil⌝ := by
  iintro #Hi
  ihave Hi2 := isInit_access $$ Hi
  icases Hi2 with ⟨-, -, -, #H1, -⟩
  unfold errors.newVar
  icases H1 with ⟨%x, #Hx, -⟩
  iexists _
  iframe Hx
  ipureintro; simp

end defs

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
