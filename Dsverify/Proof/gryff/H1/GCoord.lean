/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/GCoord.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1d: the gryff handlers of the coordinator's events (`handleRead`, `handleWrite`,
`handleRead1Reply`, `handleRead2Reply`, `handleWrite1Reply`, `handleWrite2Reply`,
`handleForceWrite`): `stepSpec`s from the coordinator's method specs, `Replica_icoordOk` and the
frame lemmas (`epf`).
-/
module

public import Dsverify.Proof.gryff.H1.HEnv
public import Dsverify.Proof.gryff.H1.Icoord
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)
open Perennial.gryff.replica (XS)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

variable [pD : GryffPartiDeps (GF := GF)]

/-- The coordinator's callbacks (H1c's `Replica_icoordOk_proof`, the frozen statement with H1b-R2's
premise). -/
theorem icoord_get (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
      r.[src.gryff.Replica, go!"parti"] ↦□ pa ⊢
      icoordOk ρ (replicaIface r) k (coordCtx γ ρ k r pa t ong) := by
  exact Replica_icoordOk_proof γ ρ k r pa t ong -- unit H1c (the frozen one is in `Link`)

variable [cD : GryffCoordDeps (GF := GF)]

theorem handleForceWrite.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    stepSpec γ ρ k r (App (repM r go!"handleForceWrite") (Val #())) iprop(True) .forceWrite := by
  intro t s s' outs hstep
  simp only [model.stepR, model.stepForceWrite, Pure.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, -⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t [] $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_auto
  wp_apply ((GryffCoordDeps.handleForceWrite (GF := GF) (hG := hG)) ρ co (replicaIface r) k s) $$ [$Hpc $Hco]
    as Hco
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s t rfl Hid $$ [$Henv $Hrest $Hco HC]
  simp only [List.nil_append]
  iexact HC

theorem handleRead2Reply.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read2ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead2Reply") (.read2Reply m) := by
  intro p t s s' outs hstep
  have hf := stepRead2Reply_epf k s s' m outs hstep
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t outs $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hic := icoord_get γ ρ k r pa t s.ongoing $$ [$Hpkg $Hrep $Hpa]
  icases (msgAt_read2Reply p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_ShiftInts $$ [$Hpc]
  have hspec := (GryffCoordDeps.handleRead2Reply (GF := GF) (hG := hG)) ρ co (replicaIface r) k
    (coordCtx γ ρ k r pa t s.ongoing) s s' outs [] _ g.T' g.ReplicaId' hstep
  simp only [read2ReplyOf] at hspec
  wp_apply hspec $$ [$Hpc $Hco $Hic $HC]
    as ⟨Hco, HC⟩
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s' t hf Hid $$ [$Henv $Hrest $Hco HC]
  iexact HC

theorem handleRead1Reply.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read1ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead1Reply") (.read1Reply m) := by
  intro p t s s' outs hstep
  have hf := stepRead1Reply_epf k s s' m outs hstep
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t outs $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  ihave #Hic := icoord_get γ ρ k r pa t s.ongoing $$ [$Hpkg $Hrep $Hpa]
  icases (msgAt_read1Reply p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  iStructNamedPrefix Hp "f"
  ipersist fVt
  wp_method_call
  wp_call
  wp_auto
  wp_lit_drop
  try wp_auto
  wp_apply wp_Replica_Printf $$ [$Hdlog]
  try wp_auto
  wp_apply wp_ShiftInts $$ [$Hpc]
  have hspec := (GryffCoordDeps.handleRead1Reply (GF := GF) (hG := hG)) ρ co (replicaIface r) k
    (coordCtx γ ρ k r pa t s.ongoing) s s' outs [] _ (p.[src.gryffproto.Read1Reply, go!"Vt"]) g.Vt' rfl Hid hstep
  simp only [read1ReplyOf] at hspec
  wp_apply hspec $$ [$Hpc $Hco $Hic $HC $fVt]
    as ⟨Hco, HC⟩
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s' t hf Hid $$ [$Henv $Hrest $Hco HC]
  iexact HC

theorem handleWrite1Reply.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write1ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite1Reply") (.write1Reply m) := by
  intro p t s s' outs hstep
  have hf := stepWrite1Reply_epf k s s' m outs hstep
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t outs $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hic := icoord_get γ ρ k r pa t s.ongoing $$ [$Hpkg $Hrep $Hpa]
  icases (msgAt_write1Reply p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  iStructNamedPrefix Hp "f"
  ipersist fVt
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_ShiftInts $$ [$Hpc]
  have hspec := (GryffCoordDeps.handleWrite1Reply (GF := GF) (hG := hG)) ρ co (replicaIface r) k
    (coordCtx γ ρ k r pa t s.ongoing) s s' outs [] _ g.ReplicaId'
    (p.[src.gryffproto.Write1Reply, go!"Vt"]) g.Vt' rfl Hid hstep
  simp only [write1ReplyOf] at hspec
  wp_apply hspec $$ [$Hpc $Hco $Hic $HC $fVt]
    as ⟨Hco, HC⟩
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s' t hf Hid $$ [$Henv $Hrest $Hco HC]
  iexact HC

theorem handleWrite2Reply.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write2ReplyM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite2Reply") (.write2Reply m) := by
  intro p t s s' outs hstep
  have hf := stepWrite2Reply_epf k s s' m outs hstep
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t outs $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hic := icoord_get γ ρ k r pa t s.ongoing $$ [$Hpkg $Hrep $Hpa]
  icases (msgAt_write2Reply p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_ShiftInts $$ [$Hpc]
  have hspec := (GryffCoordDeps.handleWrite2Reply (GF := GF) (hG := hG)) ρ co (replicaIface r) k
    (coordCtx γ ρ k r pa t s.ongoing) s s' outs [] _ g.ReplicaId'
    (p.[src.gryffproto.Write2Reply, go!"T"]) hstep
  simp only [write2ReplyOf] at hspec
  wp_apply hspec $$ [$Hpc $Hco $Hic $HC]
    as ⟨Hco, HC⟩
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s' t hf Hid $$ [$Henv $Hrest $Hco HC]
  iexact HC

theorem handleRead.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r p w : Loc)
    (g : src.gryffproto.Read) :
    stepSpec γ ρ k r (App (repM r go!"handleRead") (Val #p))
      iprop(p ↦ g ∗ writerIs ρ g.ClientId' w) (readEvOf g) := by
  intro t s s' outs hstep
  have hK : g.K' = 0 := by
    simp only [model.stepR, readEvOf] at hstep
    exact stepClientRead_key _ _ _ _ _ _ hstep
  have hstep' : model.stepR k s (.read g.RequestId' g.ClientId' 0 (depOf g.D')) = .ok (s', outs) := by
    rw [← hK]; exact hstep
  have hf : epf s' = epf s := by
    simp only [model.stepR] at hstep'
    exact stepClientRead_epf _ _ _ _ _ _ hstep'
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hp, Hw⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t outs $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  ihave #Hic := icoord_get γ ρ k r pa t s.ongoing $$ [$Hpkg $Hrep $Hpa]
  iStructNamedPrefix Hp "f"
  ipersist fD
  wp_method_call
  wp_call
  wp_auto
  wp_lit_drop
  try wp_auto
  wp_apply wp_Replica_Printf $$ [$Hdlog]
  try wp_auto
  rw [show g.K' = W64 0 by rw [hK]; rfl]
  have hspec := (GryffCoordDeps.startRead (GF := GF) (hG := hG)) ρ co (replicaIface r) k
    (coordCtx γ ρ k r pa t s.ongoing) s s' outs [] g.RequestId' g.ClientId'
    (p.[src.gryffproto.Read, go!"D"]) w g.D' Hid hstep'
  wp_apply hspec $$ [$Hpc $Hco $Hic $HC $fD $Hw]
    as ⟨Hco, HC⟩
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s' t hf Hid $$ [$Henv $Hrest $Hco HC]
  iexact HC

theorem handleWrite.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r p w : Loc)
    (g : src.gryffproto.Write) :
    stepSpec γ ρ k r (App (repM r go!"handleWrite") (Val #p))
      iprop(p ↦ g ∗ writerIs ρ g.ClientId' w) (writeEvOf g) := by
  intro t s s' outs hstep
  have hK : g.K' = 0 := by
    simp only [model.stepR, writeEvOf] at hstep
    exact stepClientWrite_key _ _ _ _ _ _ _ hstep
  have hstep' : model.stepR k s (.write g.RequestId' g.ClientId' 0 g.V' (depOf g.D')) =
      .ok (s', outs) := by
    rw [← hK]; exact hstep
  have hf : epf s' = epf s := by
    simp only [model.stepR] at hstep'
    exact stepClientWrite_epf _ _ _ _ _ _ _ hstep'
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hp, Hw⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  icases coord_split γ ρ k r gR h pa co xs s t outs $$ [$Henv $Hparts $Hpend] with
    ⟨Hco, HC, Hrest, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa, #Hco', -⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  ihave #Hic := icoord_get γ ρ k r pa t s.ongoing $$ [$Hpkg $Hrep $Hpa]
  iStructNamedPrefix Hp "f"
  ipersist fD
  wp_method_call
  wp_call
  wp_auto
  rw [show g.K' = W64 0 by rw [hK]; rfl]
  have hspec := (GryffCoordDeps.startWrite (GF := GF) (hG := hG)) ρ co (replicaIface r) k
    (coordCtx γ ρ k r pa t s.ongoing) s s' outs [] g.RequestId' g.ClientId' g.V'
    (p.[src.gryffproto.Write, go!"D"]) w g.D' Hid hstep'
  wp_apply hspec $$ [$Hpc $Hco $Hic $HC $fD $Hw]
    as ⟨Hco, HC⟩
  iapply HΦ
  iapply coord_close γ ρ k r gR h pa co xs s s' t hf Hid $$ [$Henv $Hrest $Hco HC]
  iexact HC

end

end Perennial.gryff.replica2
