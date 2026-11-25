/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Read.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the participant's `HandleRead2` and `HandleRead1`.
-/
module

public import Dsverify.Proof.gryff.H1.Overwrite
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffParticipant.wp_HandleRead2_int (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (smR owR : Loc) (sm : GMap w64 Loc) (V : w64 → IProp GF)
    (vt : model.ValTag) (gv : src.gryffproto.ValTag) (rid cid : w32) (uid : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ storeRep sm vt.t ∗ ipartiOk ip V ∗ V vt.v }}
      (App (App (App (App (App (Val (pa @!! go.GoType.PointerType
        src.gryffcommon.GryffParticipant.ty @!! go!"HandleRead2")) (Val #(W64 0))) (Val #gv))
        (Val #rid)) (Val #cid)) (Val #uid))
    {{ (rp : Loc), RET #rp; ∃ (sm' : GMap w64 Loc) (gt : src.gryffproto.Tag), smR ↦$ sm' ∗
        storeRep sm' (ovw vt gv.V' (tagOf gv.T')).t ∗ V (ovw vt gv.V' (tagOf gv.T')).v ∗
        rp ↦ (src.gryffproto.Read2Reply.mk rid cid (rid32 k) gt) }} := by
  wp_start as ⟨#Hfix, Hsm, Hst, #Hip, HV⟩
  icases (partiFix_open pa ip k smR owR).1 $$ Hfix with ⟨#Hid, #Hipf, #Hnc, #Hstp, #Howp⟩
  wp_auto
  iStructNamedPrefix vt "vt"
  ipersist vtT
  wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $vtT]
    as ⟨%sm', Hsm, Hst, HV, -⟩
  wp_apply GryffParticipant.wp_GetStoreMetadata_int $$ [$Hfix $Hsm $Hst]
    as %md2 ⟨%tp2, %gt2, %Htag2, #Htp2, Hmd2, Hsm, Hback2, -, -⟩
  icases storeMeta_acc _ _ $$ Hmd2 with ⟨HmdT2, HmdB2⟩
  icases Hback2 $$ [HmdB2 HmdT2] with ⟨Hst, -⟩
  · iapply HmdB2 $$ HmdT2
  iapply HΦ
  iexists sm', gt2
  iframe Hsm Hst HV «$r0»


/-- The store after `HandleRead1`'s dependency overwrite (only when `D.Key >= 0`). -/
def depVt (vt : model.ValTag) (gd : src.gryffproto.Dep) : model.ValTag :=
  if 0 ≤ sint.Z gd.Key' then ovw vt gd.Vt'.V' (tagOf gd.Vt'.T') else vt

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffParticipant.wp_HandleRead1_int (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (smR owR : Loc) (sm : GMap w64 Loc) (V : w64 → IProp GF)
    (vt : model.ValTag) (dp vp : Loc) (gd : src.gryffproto.Dep) (gv : src.gryffproto.ValTag)
    (rid cid coord : w32) (hd : 0 ≤ sint.Z gd.Key' → gd.Key' = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ storeRep sm vt.t ∗ ipartiOk ip V ∗ V vt.v ∗
        dp ↦□ gd ∗ vp ↦□ gv }}
      (App (App (App (App (App (App (App (Val (pa @!! go.GoType.PointerType
        src.gryffcommon.GryffParticipant.ty @!! go!"HandleRead1")) (Val #(W64 0))) (Val #dp))
        (Val #rid)) (Val #cid)) (Val #true)) (Val #vp)) (Val #coord))
    {{ (rp : Loc), RET #rp; ∃ (sm' : GMap w64 Loc) (gt : src.gryffproto.Tag), smR ↦$ sm' ∗
        storeRep sm' (ovw (depVt vt gd) gv.V' (tagOf gv.T')).t ∗
        V (ovw (depVt vt gd) gv.V' (tagOf gv.T')).v ∗
        rp ↦ (src.gryffproto.Read1Reply.mk rid cid (rid32 k)
          (src.gryffproto.ValTag.mk (ovw (depVt vt gd) gv.V' (tagOf gv.T')).v gt)) ∗
        ⌜tagOf gt = (ovw (depVt vt gd) gv.V' (tagOf gv.T')).t⌝ }} := by
  wp_start as ⟨#Hfix, Hsm, Hst, #Hip, HV, #Hdp, #Hvp⟩
  icases (ipartiOk_open ip V).1 $$ Hip with ⟨#HGet, #HSet, #HPr, #HStats, -, -⟩
  icases (partiFix_open pa ip k smR owR).1 $$ Hfix with ⟨#Hid, #Hipf, #Hnc, #Hstp, #Howp⟩
  simp only [specT]
  iStructNamedPrefix Hdp "d"
  iStructNamedPrefix dVt "dv"
  iStructNamedPrefix Hvp "v"
  wp_auto
  wp_printf HPr
  wp_join iprop(∃ sm1 : GMap w64 Loc, smR ↦$ sm1 ∗ storeRep sm1 (depVt vt gd).t ∗
      V (depVt vt gd).v ∗ dep_ptr ↦ dp ∗ r_ptr ↦ pa) with [Hsm Hst HV dep r]
      as ⟨%sm1, Hsm, Hst, HV, dep, r⟩
  · have hk0 := hd (by simpa using Hif)
    rw [hk0]
    wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $dvT]
      as ⟨%sm', Hsm, Hst, HV, -⟩
    isplitl []
    · ipureintro; rfl
    iexists sm'
    have : depVt vt gd = ovw vt gd.Vt'.V' (tagOf gd.Vt'.T') := by
      unfold depVt; rw [if_pos (by simpa using Hif)]
    rw [this]
    iframe Hsm Hst HV dep r
  · have : depVt vt gd = vt := by
      unfold depVt; rw [if_neg (by simpa using Hif)]
    rw [this]
    iexists sm
    iframe Hsm Hst HV dep r
  wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $vT]
    as ⟨%sm', Hsm, Hst, HV, -⟩
  wp_apply GryffParticipant.wp_GetStoreMetadata_int $$ [$Hfix $Hsm $Hst]
    as %md2 ⟨%tp2, %gt2, %Htag2, #Htp2, Hmd2, Hsm, Hback2, -, -⟩
  wp_apply HGet $$ %_ [$HV] as %ret ⟨%Hret, HV⟩
  subst Hret
  wp_auto
  wp_apply HGet $$ %_ [$HV] as %ret ⟨%Hret, HV⟩
  subst Hret
  wp_printf HPr
  icases storeMeta_acc _ _ $$ Hmd2 with ⟨HmdT2, HmdB2⟩
  icases Hback2 $$ [HmdB2 HmdT2] with ⟨Hst, -⟩
  · iapply HmdB2 $$ HmdT2
  iapply HΦ
  iexists sm', gt2
  iframe Hsm Hst HV «$r0»
  ipureintro; exact Htag2


end

end Perennial.gryff.replica2
