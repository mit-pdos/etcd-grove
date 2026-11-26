/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Write2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the participant's `HandleWrite2` (the `OngoingWrites` loop: every entry has
`SentWrite1Reply = true`, so no iteration answers anything, whatever Go's map order).
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

set_option hygiene false in
/-- `HandleWrite2`'s common tail (the reply). -/
local macro "w2_tail" : tactic => `(tactic| (
  wp_apply GryffParticipant.wp_GetStoreMetadata_int $$ [Hsm Hst]
    as %md2 ⟨%tp2, %gt2, %Htag2, #Htp2, Hmd2, Hsm, Hback2, -, -⟩
  · iframe Hfix Hsm Hst
  icases storeMeta_acc _ _ $$ Hmd2 with ⟨HmdT2, HmdB2⟩
  wp_auto
  wp_printf HPr
  icases Hback2 $$ [HmdB2 HmdT2] with ⟨Hst, -⟩
  · iapply HmdB2 $$ HmdT2
  iapply HΦ
  rw [show ∀ c : Bool, W32 (sint.Z (if c = true then W64 1 else W64 0)) =
      (if c = true then W32 1 else W32 0) from fun c => by cases c <;> rfl]
  iexists sm', (GMap.delete cid ow), gt2
  iframe Hsm Hst How HV «$r0»
  rw [owRep_eq]
  iframe Hents
  ipureintro; exact Hdom))

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffParticipant.wp_HandleWrite2_int (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (smR owR : Loc) (sm : GMap w64 Loc) (ow : GMap w32 Loc) (V : w64 → IProp GF)
    (vt : model.ValTag) (ong : AMap 32 w32) (gv : src.gryffproto.ValTag) (rid cid : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ storeRep sm vt.t ∗ owR ↦$ ow ∗ owRep ow ong ∗
        ipartiOk ip V ∗ V vt.v }}
      (App (App (App (App (Val (pa @!! go.GoType.PointerType src.gryffcommon.GryffParticipant.ty @!!
        go!"HandleWrite2")) (Val #(W64 0))) (Val #gv)) (Val #rid)) (Val #cid))
    {{ (rp : Loc), RET #rp; ∃ (sm' : GMap w64 Loc) (ow' : GMap w32 Loc)
        (gt : src.gryffproto.Tag), smR ↦$ sm' ∗
        storeRep sm' (ovw vt gv.V' (tagOf gv.T')).t ∗ owR ↦$ ow' ∗ owRep ow' (ong.del cid) ∗
        V (ovw vt gv.V' (tagOf gv.T')).v ∗
        rp ↦ (src.gryffproto.Write2Reply.mk rid cid (rid32 k) gt
          (if vt.t.lt (tagOf gv.T') then W32 1 else W32 0)) }} := by
  wp_start as ⟨#Hfix, Hsm, Hst, How, Howr, #Hip, HV⟩
  icases (ipartiOk_open ip V).1 $$ Hip with ⟨#HGet, #HSet, #HPr, #HStats, #HW1O, -⟩
  icases (partiFix_open pa ip k smR owR).1 $$ Hfix with ⟨#Hid, #Hipf, #Hnc, #Hstp, #Howp⟩
  simp only [specT]
  wp_auto
  iStructNamedPrefix vt "vt"
  ipersist vtT
  wp_printf HPr
  wp_apply GryffParticipant.wp_GetStoreMetadata_int $$ [$Hfix $Hsm $Hst]
    as %md ⟨%tp0, %gt0, %Htag0, #Htp0, Hmd, Hsm, Hback, -, %Hmd0⟩
  icases storeMeta_acc _ _ $$ Hmd with ⟨HmdT, HmdB⟩
  wp_apply Tag.wp_LessThan $$ [$Htp0] as -
  wp_join iprop(applied_ptr ↦ (if (tagOf gt0).lt (tagOf gv.T') then W64 1 else W64 0)) at next
    with [applied] as applied
  · cases (tagOf gt0).lt (tagOf gv.T') <;> wp_auto <;> wp_join_done
  icases Hback $$ [HmdB HmdT] with ⟨Hst, Halive⟩
  · iapply HmdB $$ HmdT
  rw [Htag0] at *
  wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $vtT]
    as ⟨%sm', Hsm, Hst, HV, %Hsm'⟩
  wp_apply wp_mapDelete $$ How as How
  ihave Howr := owRep_del _ _ cid $$ Howr
  rw [owRep_eq]
  icases Howr with ⟨%Hdom, Hents⟩
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %sl0 ⟨Hsl0, Hcap0⟩
  · ipureintro; word
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  iapply (wp_map_for_range (fun _ _ => iprop(∃ (wv : Loc) (b : Bool),
      write_ptr ↦ wv ∗ ongoingWrite_ptr ↦ b ∗ concurrentWrites_ptr ↦ sl0 ∗ key_ptr ↦ W64 0 ∗
      r_ptr ↦ pa ∗ requestId_ptr ↦ rid ∗ clientId_ptr ↦ cid ∗
      owEntries (GMap.delete cid ow) (ong.del cid)))) $$ How
  iintro %keys %hkeys
  isplitl [write ongoingWrite concurrentWrites key r requestId clientId Hents]
  · iexists _, _; iframe
  isplitl []
  · imodintro
    iintro %i %key %u ⟨%hk1, %hk2⟩ ⟨%wv, %b, Hw, Hog, Hcw, Hkey, Hr, Hrid, Hcid, Hents⟩
    unfold owEntries owEnt
    icases (BigSepM.bigSepM_lookup_acc (M := GMap w32) hk2).1 $$ Hents with
      ⟨⟨%rq, %g, %wm, %Hrq, Hu, Hwm, %Hg⟩, Hents⟩
    obtain ⟨Hsent, Hfast, Hwrid, Hwcid, HwK⟩ := Hg
    wp_auto
    rw [show decide (wm.K' = W64 0) = true by simp [HwK]]
    wp_auto
    wp_printf HPr
    rw [show decide (wm.K' = W64 0) = true by simp [HwK]]
    wp_auto
    repeat (first
      | (rw [show decide (wm.K' = W64 0) = true by simp [HwK]]; wp_auto)
      | (rw [Hsent]; wp_auto))
    unfold forMapPostcondition
    iright; ileft
    isplitl []
    · ipureintro; rfl
    iexists _, _
    iframe
    iapply Hents
    iexists rq, g, wm
    iframe Hu Hwm
    ipureintro; exact ⟨Hrq, Hsent, Hfast, Hwrid, Hwcid, HwK⟩
  iintro ⟨%wv, %b, write, ongoingWrite, concurrentWrites, key, r, requestId, clientId, Hents⟩ How
  wp_auto
  ihave Halive := mdAlive_mono _ _ md Hsm' $$ Halive
  ihave %Hsl0len := ownSlice_len _ _ _ $$ Hsl0
  cases b
  · wp_auto
    icases mdAlive_read _ _ _ $$ [Hst Halive] with ⟨%tp1, %gt1, Hmd1, #Htp1, Hmdb⟩
    · iframe Hst Halive
    icases storeMeta_acc _ _ $$ Hmd1 with ⟨HmdT, HmdB⟩
    wp_auto
    icases Hmdb $$ [HmdB HmdT] with ⟨Hst, Halive⟩
    · iapply HmdB $$ HmdT
    wp_for
    wp_if_destruct
    · exfalso; simp at Hsl0len; word
    w2_tail
  · wp_auto
    w2_tail

end

end Perennial.gryff.replica2
