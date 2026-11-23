/-
**The raftpb instance's hard-state laws** (W4c U4 b of `notes/wal-fsext-w4c-plan.md`, "W4c U4 log"):
`WalPbIn.NilLaw`, `ZeroLaw`, `MustSyncLaw` (raft's `MustSync`, `rawnode.go:191`), `IsEmptyLaw` (raft's
`IsEmptyHardState`, `node.go:122`, over raft's package fact `isInitialized`: `emptyState`), and
`WalHsOwn`'s `zero`, `getCommit`, `freeze` of `walRaftHsO`. (`MarshalHsLaw`: `LawsHsMarshal.lean`, over the
registered `raftpb.HardState`, wal-item3; `WalHsOwn.reset` over the trusted model `HardState.Reset.impl` since 2026-11-22; `WalHsOwn.unmarshal` and
`CloneHsLaw`: `LawsHsPb.lean`.) Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Getters
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleUnnamed
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- A zero `HardState`'s fields. -/
theorem hsZeroVal_fields :
    (zero_val go_etcd_io.raft.v3.raftpb.HardState).Term' = (null : Loc) ∧
    (zero_val go_etcd_io.raft.v3.raftpb.HardState).Vote' = (null : Loc) ∧
    (zero_val go_etcd_io.raft.v3.raftpb.HardState).Commit' = (null : Loc) ∧
    (zero_val go_etcd_io.raft.v3.raftpb.HardState).unknownFields' = slice.nil :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`NilLaw`.** -/
theorem walRaftP_nil : WalPbIn.NilLaw (walRaftP (GF := GF)) := by
  simp only [WalPbIn.NilLaw, walRaftP]
  unfold walHsIn
  ileft; ipureintro; exact ⟨rfl, rfl⟩

/-- A nil hard state holds only the zero state. -/
theorem walHsIn_null (h : HardStateM) : walHsIn (GF := GF) null h ⊢ ⌜h = hsZero⌝ := by
  unfold walHsIn hsRoC hsCells
  iintro (%H | ⟨%c, ⟨⟨%pt, %pv, %pc, %Hn, -⟩, -⟩, -⟩)
  · ipureintro; exact H.2
  · exact absurd rfl Hn

/-- **`ZeroLaw`.** -/
theorem walRaftP_zero : WalPbIn.ZeroLaw (walRaftP (GF := GF)) := by
  refine ⟨fun h => walHsIn_null h, ?_⟩
  intro p E
  simp only [walRaftP]
  iintro Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef, hsZeroVal_fields.1, hsZeroVal_fields.2.1,
    hsZeroVal_fields.2.2.1, hsZeroVal_fields.2.2.2]
  icases Hp with ⟨Hst, HT, HV, HC, Huf, Hsc, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod (pbMsg_alloc raftpb.HardState p _ _ _ [] E (ufWire_nil _)) $$ [Hst Hsc Huf Hnil] with #Hpb
  · iframe
  imodintro
  unfold walHsIn
  iright
  iexists walHsC0
  unfold hsRoC hsCells
  simp only [walHsC0]
  iframe Hpb
  isplitl
  · iexists _, _, _
    iframe HT HV HC
    unfold optCell
    ipureintro
    exact ⟨Hnn, rfl, rfl, rfl⟩
  · ipureintro
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- **`isHardStateEqual(a, b)`** (`node.go:117`): the three getters agree. (wal-link, 2026-11-19:
renamed from `wp_isHardStateEqual`, which raft's `Link` declares in the same namespace; the server's
`Link` imports both.) -/
theorem walRaft_isHardStateEqual (a b : Loc) (ha hb : HardStateM) :
    {{ hsGet (GF := GF) a ha ∗ hsGet b hb }}
      (App (App (Val (@! go_etcd_io.raft.v3.isHardStateEqual)) (Val #a)) (Val #b))
    {{ (r : Bool), RET #r; ⌜r = true ↔ (ha.Term' = hb.Term' ∧ ha.Vote' = hb.Vote' ∧ ha.Commit' = hb.Commit')⌝ }} := by
  wp_start as ⟨#Ha, #Hb⟩
  (try wp_auto)
  wp_apply (wp_hsGetTerm a ha) $$ []
  · iexact Ha
  wp_apply (wp_hsGetTerm b hb) $$ []
  · iexact Hb
  wp_if_destruct
  · wp_apply (wp_hsGetVote a ha) $$ []
    · iexact Ha
    wp_apply (wp_hsGetVote b hb) $$ []
    · iexact Hb
    wp_if_destruct
    · wp_apply (wp_hsGetCommit a ha) $$ []
      · iexact Ha
      wp_apply (wp_hsGetCommit b hb) $$ []
      · iexact Hb
      iapply HΦ
      ipureintro
      simp_all
    · iapply HΦ
      ipureintro
      simp_all
  · iapply HΦ
    ipureintro
    simp_all

/-- **`IsEmptyLaw`** (raft's package fact gives `emptyState`). -/
theorem walRaftP_isEmpty : WalPbIn.IsEmptyLaw (walRaftP (GF := GF)) := by
  intro hp hs
  simp only [walRaftP]
  wp_start as #Hh
  ihave Hr : (go_etcd_io.raft.v3.isInitialized : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave ⟨%es, #Hg, #Ges⟩ := rootInit_hsGet $$ Hr
  ihave #G := walHsIn_hsGet hp hs $$ Hh
  (try wp_auto)
  wp_if_destruct
  · ihave %Hz := walHsIn_null hs $$ Hh
    subst Hz
    iapply HΦ
    ipureintro
    exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl⟩
  · wp_apply (walRaft_isHardStateEqual hp es hs hsZero) $$ [] as %r %hr
    · iframe G Ges
    iapply HΦ
    ipureintro
    unfold hsEmptyP
    exact hr

/-- **`MustSyncLaw`.** -/
theorem walRaftP_mustSync : WalPbIn.MustSyncLaw (walRaftP (GF := GF)) := by
  intro p1 p2 h1 h2 n
  simp only [walRaftP]
  wp_start as ⟨#H1, #H2⟩
  ihave #G1 := walHsIn_hsGet p1 h1 $$ H1
  ihave #G2 := walHsIn_hsGet p2 h2 $$ H2
  (try wp_auto)
  wp_if_destruct
  · wp_apply (wp_hsGetVote p1 h1) $$ []
    · iexact G1
    wp_apply (wp_hsGetVote p2 h2) $$ []
    · iexact G2
    wp_if_destruct
    · wp_apply (wp_hsGetTerm p1 h1) $$ []
      · iexact G1
      wp_apply (wp_hsGetTerm p2 h2) $$ []
      · iexact G2
      iapply HΦ
      ipureintro
      simp_all
    · iapply HΦ
      ipureintro
      simp_all
  · iapply HΦ
    ipureintro
    simp_all

/-! ## The hard states `ReadAll` owns -/

/-- `WalHsOwn.zero`. -/
theorem walRaftHsO_zero (p : Loc) :
    p ↦ (zero_val go_etcd_io.raft.v3.raftpb.HardState) ⊢ walRaftHsO (GF := GF) p hsZero := by
  iintro Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef, hsZeroVal_fields.1, hsZeroVal_fields.2.1,
    hsZeroVal_fields.2.2.1, hsZeroVal_fields.2.2.2]
  icases Hp with ⟨Hst, HT, HV, HC, Huf, Hsc, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  unfold walRaftHsO
  rw [walHsCanon_zero]
  unfold hsOwnC
  simp only [walHsC0]
  iexists _, _, _, _, _, _
  iframe HT HV HC Hst Hsc Huf Hnil
  unfold optCell
  ipureintro
  exact ⟨Hnn, rfl, rfl, rfl⟩

/-- `WalHsOwn.getCommit`. -/
theorem walRaftHsO_getCommit (p : Loc) (h : HardStateM) :
    {{ walRaftHsO (GF := GF) p h }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty @!! go!"GetCommit"))
        (Val #()))
    {{ RET #h.Commit'; walRaftHsO p h }} := by
  wp_start_folded as Hh
  unfold walRaftHsO hsOwnC
  icases Hh with ⟨%pt, %pv, %pc, %st, %sc, %us, %Hn, HT, #cT, HV, #cV, HC, #cC, Hst, Hsc, Hus, Huf⟩
  wp_apply (wp_hsGetCommit_raw p pc (DFrac.own 1) (walHsCanon h).commit) $$ [HC] as HC
  · iframe HC cC; ipureintro; exact Hn
  rw [walHsCanon_commit]
  iapply HΦ
  iexists pt, pv, pc, st, sc, us
  iframe HT cT HV cV HC cC Hst Hsc Hus Huf
  ipureintro; exact Hn

/-- The trusted model's type by name is the translation's `HardState.ty`. -/
theorem raftpb_model_HardState_eq :
    go_etcd_io.raft.v3.raftpb.model.HardState = go_etcd_io.raft.v3.raftpb.HardState.ty := by
  unfold go_etcd_io.raft.v3.raftpb.HardState.ty; rfl

/-- `WalHsOwn.reset`, over the trusted model `HardState.Reset.impl`
(`TrustedCode/go_etcd_io/raft/v3/raftpb.lean`: the store of the zero value). -/
theorem walRaftHsO_reset (p : Loc) (h : HardStateM) :
    {{ walRaftHsO (GF := GF) p h }}
      (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty @!! go!"Reset"))
        (Val #()))
    {{ RET #(); walRaftHsO p hsZero }} := by
  wp_start_folded as Hh
  iunfold walRaftHsO at Hh
  iunfold hsOwnC at Hh
  icases Hh with ⟨%pt, %pv, %pc, %st, %sc, %us, %Hn, HT, -, HV, -, HC, -, Hst, Hsc, Hus, -⟩
  ihave Hp := typedPointsto_combine (GF := GF) p
    (go_etcd_io.raft.v3.raftpb.HardState.mk st pt pv pc us sc) (DFrac.own 1) Hn $$ [HT HV HC Hst Hsc Hus]
  · simp only [TypedPointsto.typedPointstoDef]
    iframe
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty) (m := go!"Reset")]
  unfold go_etcd_io.raft.v3.raftpb.HardState.Reset.impl
  rw [raftpb_model_HardState_eq]
  wp_auto
  iapply HΦ
  iapply walRaftHsO_zero
  iexact Hp

/-- `WalHsOwn.freeze`. -/
theorem walRaftHsO_freeze (p : Loc) (h : HardStateM) (E : CoPset) :
    walRaftHsO (GF := GF) p h ⊢ |={E}=> (walRaftP (GF := GF)).hsIn p h := by
  simp only [walRaftP]
  unfold walRaftHsO hsOwnC
  iintro ⟨%pt, %pv, %pc, %st, %sc, %us, %Hn, HT, #cT, HV, #cV, HC, #cC, Hst, Hsc, Hus, Huf⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  imod (pbMsg_alloc raftpb.HardState p st sc us (walHsCanon h).uf E
      (by rw [walHsCanon_uf]; exact ufWire_nil _)) $$ [Hst Hsc Hus Huf] with #Hpb
  · iframe
  imodintro
  unfold walHsIn
  iright
  iexists (walHsCanon h)
  unfold hsRoC hsCells
  iframe Hpb
  isplitl
  · iexists pt, pv, pc
    iframe HT cT HV cV HC cC
    ipureintro; exact Hn
  · ipureintro
    exact ⟨walHsCanon_model h, Or.inr rfl⟩

end laws

end EtcdGrove
end Perennial
