/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Parti.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the participant's methods (`gryffcommon/participant.go`).
-/
module

public import Dsverify.Proof.gryff.H1.Write2
public import Dsverify.Proof.gryff.H1.Read
public import Dsverify.Proof.gryff.H1.Write1
public import Dsverify.Proof.gryff.H1.Pure
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

theorem GryffParticipant.GetStoreMetadata.wp_proof (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (tag : model.Tag) (ong : AMap 32 w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ partiOwn pa ip k tag ong }}
      (App (partiM pa go!"GetStoreMetadata") (Val #(W64 0)))
    {{ (md : Loc), RET #md; ∃ (tp : Loc) (gt : src.gryffproto.Tag), ⌜tagOf gt = tag⌝ ∗ tp ↦□ gt ∗
        md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp ∗
        (md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp -∗ partiOwn pa ip k tag ong) }} := by
  simp only [partiM]
  wp_start as Hp
  unfold partiOwn
  icases Hp with ⟨%smR, %owR, %sm, %ow, #Hid, #Hip, #Hnc, #Hst, #Howp, Hsm, How, %Hsm0, Hm, %Hdom, Hws⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hsm as Hsm
  cases hm : sm !! W64 0 with
  | none =>
    dsimp only at hm ⊢
    ipure Hm
    wp_pures
    wp_alloc tp as Htp
    ipersist Htp
    wp_auto
    iStructNamed «$r0»
    iapply HΦ
    iexists tp, ⟨W32 0, W32 0, W32 0⟩
    isplitr
    · ipureintro; simp [tagOf, Hm, model.tag0]
    isplitl []
    · iexact Htp
    isplitl [Tag]
    · iexact Tag
    iintro HTag
    iexists smR, owR, sm, ow
    iframe Hid Hip Hnc Hst Howp Hsm How Hws
    simp only [hm]
    ipureintro; exact ⟨Hsm0, Hm, Hdom⟩
  | some md =>
    icases Hm with ⟨%tp, %gt, Hmd, #Htp, %Htag⟩
    rw [show decide ((some md).isSome = true) = true from rfl]
    wp_auto
    icases storeMeta_acc _ _ $$ Hmd with ⟨Tag, Hback⟩
    iapply HΦ
    iexists tp, gt
    isplitr
    · ipureintro; exact Htag
    isplitl []
    · iexact Htp
    isplitl [Tag]
    · iexact Tag
    iintro HTag
    iexists smR, owR, sm, ow
    iframe Hid Hip Hnc Hst Howp Hsm How Hws
    simp only [hm]
    isplitl []
    · ipureintro; exact Hsm0
    isplitl [HTag Hback]
    · iexists tp, gt
      iframe Htp
      isplitl
      · iapply Hback $$ HTag
      ipureintro; exact Htag
    ipureintro; exact Hdom


theorem GryffParticipant.HandleOverwrite.wp_proof (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (vt : model.ValTag) (ong : AMap 32 w32) (v : w64) (tp : Loc)
    (gt : src.gryffproto.Tag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ partiOwn pa ip k vt.t ong ∗
        ipartiOk ip V ∗ V vt.v ∗ tp ↦□ gt }}
      (App (App (App (partiM pa go!"HandleOverwrite") (Val #(W64 0))) (Val #v)) (Val #tp))
    {{ RET #(); partiOwn pa ip k (ovw vt v (tagOf gt)).t ong ∗ V (ovw vt v (tagOf gt)).v }} := by
  simp only [partiM]
  wp_start_folded as ⟨Hp, #Hip, HV, #Htp⟩
  icases (partiOwn_open pa ip k vt.t ong).1 $$ Hp with ⟨%smR, %owR, %sm, %ow, #Hfix, Hsm, How, Hst, Hws⟩
  wp_apply GryffParticipant.wp_HandleOverwrite_int $$ [$Hfix $Hsm $Hst $Hip $HV $Htp]
    as ⟨%sm', Hsm, Hst, HV, -⟩
  iapply HΦ
  iframe HV
  iapply (partiOwn_open pa ip k _ ong).2
  iexists smR, owR, sm', ow
  iframe Hfix Hsm How Hst Hws


theorem GryffParticipant.HandleWrite2.wp_proof (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (o1 : Out) (m : model.Write2ProxiedM)
    (gv : src.gryffproto.ValTag) (hv : vtOf gv = m.vt) (hid : s.id = rid32 k)
    (hstep : model.stepWrite2 s m = .ok (s', [o1])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val }}
      (App (App (App (App (partiM pa go!"HandleWrite2") (Val #m.k)) (Val #gv))
        (Val #m.requestId)) (Val #m.clientId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Write2Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.write2Reply (write2ReplyOf g)) = some o1⌝ }} := by
  obtain ⟨hk, htag, hval, hong, hsend⟩ := stepWrite2_inv s s' m o1 hstep
  have hvt : gv.V' = m.vt.v ∧ tagOf gv.T' = m.vt.t := by rw [← hv]; exact ⟨rfl, rfl⟩
  simp only [partiM]
  rw [hk, show (0 : w64) = W64 0 from rfl]
  wp_start_folded as ⟨Hp, #Hip, HV⟩
  icases (partiOwn_open pa ip k s.tag s.ongoing).1 $$ Hp with
    ⟨%smR, %owR, %sm, %ow, #Hfix, Hsm, How, Hst, Hws⟩
  rw [show s.tag = s.storeVT.t from rfl, show s.val = s.storeVT.v from rfl]
  wp_apply (GryffParticipant.wp_HandleWrite2_int pa ip k smR owR sm ow V s.storeVT s.ongoing gv
    m.requestId m.clientId) $$ [$Hfix $Hsm $Hst $How $Hws $Hip $HV]
    as %rp ⟨%sm', %ow', %gt, Hsm, Hst, How, Hws, HV, Hrp⟩
  iapply HΦ
  rw [hvt.1, hvt.2, htag, hval, hong]
  iframe HV
  isplitl [Hsm Hst How Hws]
  · iapply (partiOwn_open pa ip k _ _).2
    iexists smR, owR, sm', ow'
    iframe Hfix Hsm Hst How Hws
  iexists _
  iframe Hrp
  ipureintro
  rw [← hsend]
  rfl


theorem GryffParticipant.HandleRead2.wp_proof (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (o1 : Out) (m : model.Read2ProxiedM)
    (gv : src.gryffproto.ValTag) (uid : w64) (hv : vtOf gv = m.vt)
    (hstep : model.stepRead2 s m = .ok (s', [o1])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val }}
      (App (App (App (App (App (partiM pa go!"HandleRead2") (Val #m.k)) (Val #gv))
        (Val #m.requestId)) (Val #m.clientId)) (Val #uid))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Read2Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.read2Reply (read2ReplyOf g)) = some o1⌝ }} := by
  obtain ⟨hk, htag, hval, hong, hsend⟩ := stepRead2_inv s s' m o1 hstep
  have hvt : gv.V' = m.vt.v ∧ tagOf gv.T' = m.vt.t := by rw [← hv]; exact ⟨rfl, rfl⟩
  simp only [partiM]
  rw [hk, show (0 : w64) = W64 0 from rfl]
  wp_start_folded as ⟨Hp, #Hip, HV⟩
  icases (partiOwn_open pa ip k s.tag s.ongoing).1 $$ Hp with
    ⟨%smR, %owR, %sm, %ow, #Hfix, Hsm, How, Hst, Hws⟩
  rw [show s.tag = s.storeVT.t from rfl, show s.val = s.storeVT.v from rfl]
  wp_apply (GryffParticipant.wp_HandleRead2_int pa ip k smR owR sm V s.storeVT gv
    m.requestId m.clientId uid) $$ [$Hfix $Hsm $Hst $Hip $HV]
    as %rp ⟨%sm', %gt, Hsm, Hst, HV, Hrp⟩
  iapply HΦ
  rw [hvt.1, hvt.2, htag, hval, hong]
  iframe HV
  isplitl [Hsm Hst How Hws]
  · iapply (partiOwn_open pa ip k _ _).2
    iexists smR, owR, sm', ow
    iframe Hfix Hsm Hst How Hws
  iexists _
  iframe Hrp
  ipureintro
  rw [← hsend]
  rfl


theorem storeVT_overwrite (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).storeVT = ovw s.storeVT v t := by
  obtain ⟨h1, h2, -⟩ := ovw_overwrite s v t
  simp only [RState.storeVT] at *
  rw [h1, h2]

theorem GryffParticipant.HandleRead1.wp_proof (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (o1 : Out) (m : model.Read1ProxiedM) (dp vp : Loc)
    (gd : src.gryffproto.Dep) (gv : src.gryffproto.ValTag) (hd : depOf gd = m.d)
    (hv : vtOf gv = m.vt) (hid : s.id = rid32 k) (hstep : model.stepRead1 s m = .ok (s', [o1])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val ∗ dp ↦□ gd ∗ vp ↦□ gv }}
      (App (App (App (App (App (App (App (partiM pa go!"HandleRead1") (Val #m.k)) (Val #dp))
        (Val #m.requestId)) (Val #m.clientId)) (Val #true)) (Val #vp)) (Val #m.replicaId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Read1Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.read1Reply (read1ReplyOf g)) = some o1⌝ }} := by
  obtain ⟨hk, hd0, hs', hsend⟩ := stepRead1_inv s s' m o1 hstep
  have hdk : m.d.key = gd.Key' := by rw [← hd]; rfl
  have hdvt : m.d.vt = ⟨gd.Vt'.V', tagOf gd.Vt'.T'⟩ := by rw [← hd]; rfl
  have hvt : m.vt = ⟨gv.V', tagOf gv.T'⟩ := by rw [← hv]; rfl
  have hge : model.sge m.d.key 0 = decide (0 ≤ sint.Z gd.Key') := by
    rw [hdk]; simp [model.sge, model.sle]
  have hd' : 0 ≤ sint.Z gd.Key' → gd.Key' = W64 0 := by
    intro h; rw [← hdk]; exact hd0 (by rw [hge]; simpa using h)
  have hs1 : (if model.sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).storeVT =
      depVt s.storeVT gd := by
    unfold depVt; rw [hge, hdvt]
    by_cases h : 0 ≤ sint.Z gd.Key'
    · simp only [h, decide_true, ↓reduceIte]; exact storeVT_overwrite _ _ _
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hs'vt : s'.storeVT = ovw (depVt s.storeVT gd) gv.V' (tagOf gv.T') := by
    rw [hs', storeVT_overwrite, hs1, hvt]
  have hs'id : s'.id = s.id ∧ s'.ongoing = s.ongoing := by
    rw [hs']
    obtain ⟨a1, a2⟩ := overwrite_id (if model.sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s)
      m.vt.v m.vt.t
    rw [a1, a2]
    split
    · exact overwrite_id _ _ _
    · exact ⟨rfl, rfl⟩
  simp only [partiM]
  rw [hk, show (0 : w64) = W64 0 from rfl]
  wp_start_folded as ⟨Hp, #Hip, HV, #Hdp, #Hvp⟩
  icases (partiOwn_open pa ip k s.tag s.ongoing).1 $$ Hp with
    ⟨%smR, %owR, %sm, %ow, #Hfix, Hsm, How, Hst, Hws⟩
  rw [show s.tag = s.storeVT.t from rfl, show s.val = s.storeVT.v from rfl]
  wp_apply (GryffParticipant.wp_HandleRead1_int pa ip k smR owR sm V s.storeVT dp vp gd gv
    m.requestId m.clientId m.replicaId hd') $$ [$Hfix $Hsm $Hst $Hip $HV $Hdp $Hvp]
    as %rp ⟨%sm', %gt, Hsm, Hst, HV, Hrp, %Hgt⟩
  iapply HΦ
  rw [show s'.tag = s'.storeVT.t from rfl, show s'.val = s'.storeVT.v from rfl, hs'vt,
    hs'id.2]
  iframe HV
  isplitl [Hsm Hst How Hws]
  · iapply (partiOwn_open pa ip k _ _).2
    iexists smR, owR, sm', ow
    iframe Hfix Hsm Hst How Hws
  iexists _
  iframe Hrp
  ipureintro
  rw [← hsend, hs'id.1, hid, hs'vt]
  simp only [read1ReplyOf, vtOf, Hgt]


theorem GryffParticipant.HandleWrite1.wp_proof (pa : Loc) (ip : GoInterface) (k : Fin 3)
    (V : w64 → IProp GF) (s s' : RState) (outs : List Out) (m : model.Write1ProxiedM)
    (val : w64) (n : w32) (dp mp : Loc) (gd : src.gryffproto.Dep) (gmt : src.gryffproto.Tag)
    (hd : depOf gd = m.d) (hid : s.id = rid32 k) (hstep : model.stepWrite1 s m = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val ∗ dp ↦□ gd ∗ mp ↦□ gmt }}
      (App (App (App (App (App (App (App (App (App (partiM pa go!"HandleWrite1") (Val #m.k))
        (Val #val)) (Val #n)) (Val #dp)) (Val #m.requestId)) (Val #m.clientId)) (Val #mp))
        (Val #m.forceWrite)) (Val #m.replicaId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ((⌜rp = Loc.null ∧ outs = []⌝) ∨ ∃ (g : src.gryffproto.Write1Reply) (o1 : Out),
          rp ↦ g ∗ ⌜outs = [o1] ∧ model.sendTo m.replicaId (.write1Reply (write1ReplyOf g)) = some o1⌝) }} := by
  obtain ⟨hk, hcase⟩ := stepWrite1_inv s s' m outs hstep
  have hdk : m.d.key = gd.Key' := by rw [← hd]; rfl
  have hdvt : m.d.vt = ⟨gd.Vt'.V', tagOf gd.Vt'.T'⟩ := by rw [← hd]; rfl
  have hge : model.sge m.d.key 0 = decide (0 ≤ sint.Z gd.Key') := by
    rw [hdk]; simp [model.sge, model.sle]
  have hs1 : (if model.sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).storeVT =
      depVt s.storeVT gd := by
    unfold depVt; rw [hge, hdvt]
    by_cases h : 0 ≤ sint.Z gd.Key'
    · simp only [h, decide_true, ↓reduceIte]; exact storeVT_overwrite _ _ _
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hd' : (¬ ∃ r, s.ongoing.get? m.clientId = some r ∧ model.sgt r m.requestId = true) →
      0 ≤ sint.Z gd.Key' → gd.Key' = W64 0 := by
    intro hns h
    rcases hcase with ⟨hst, -⟩ | ⟨-, hd0, -⟩
    · exact absurd hst hns
    · rw [← hdk]; exact hd0 (by rw [hge]; simpa using h)
  have hfw' : (¬ ∃ r, s.ongoing.get? m.clientId = some r ∧ model.sgt r m.requestId = true) →
      0 < sint.Z m.forceWrite := by
    intro hns
    rcases hcase with ⟨hst, -⟩ | ⟨-, -, hfw, -⟩
    · exact absurd hst hns
    · simpa [model.sgt, model.slt] using hfw
  simp only [partiM]
  rw [hk, show (0 : w64) = W64 0 from rfl]
  wp_start_folded as ⟨Hp, #Hip, HV, #Hdp, #Hmp⟩
  icases (partiOwn_open pa ip k s.tag s.ongoing).1 $$ Hp with
    ⟨%smR, %owR, %sm, %ow, #Hfix, Hsm, How, Hst, Hws⟩
  rw [show s.tag = s.storeVT.t from rfl, show s.val = s.storeVT.v from rfl]
  wp_apply (GryffParticipant.wp_HandleWrite1_int pa ip k smR owR sm ow V s.storeVT s.ongoing val n
    dp mp gd gmt m.requestId m.clientId m.forceWrite m.replicaId hd' hfw')
    $$ [$Hfix $Hsm $Hst $How $Hws $Hip $HV $Hdp $Hmp] as %rp Hpost
  iapply HΦ
  icases Hpost with (⟨%Hst', %Hrp, Hsm, Hst, How, Hws, HV⟩ |
    ⟨%Hns, %sm', %ow', %gt, Hsm, Hst, How, Hws, HV, Hrp, %Hgt⟩)
  · rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hns, -⟩
    · iframe HV
      isplitl [Hsm Hst How Hws]
      · iapply (partiOwn_open pa ip k _ _).2
        iexists smR, owR, sm, ow
        iframe Hfix Hsm Hst How Hws
      ileft; ipureintro; exact ⟨Hrp, rfl⟩
    · exact absurd Hst' hns
  · rcases hcase with ⟨hst, -⟩ | ⟨-, -, -, htag, hval, hong, o, rfl, hsend⟩
    · exact absurd hst Hns
    have ht : s'.tag = (depVt s.storeVT gd).t := by rw [htag, ← hs1]; rfl
    have hv : s'.val = (depVt s.storeVT gd).v := by rw [hval, ← hs1]; rfl
    rw [ht, hv, hong]
    iframe HV
    isplitl [Hsm Hst How Hws]
    · iapply (partiOwn_open pa ip k _ _).2
      iexists smR, owR, sm', ow'
      iframe Hfix Hsm Hst How Hws
    iright
    iexists _, o
    iframe Hrp
    ipureintro
    refine ⟨rfl, ?_⟩
    rw [← hsend]
    have : (if model.sge m.d.key 0 then s.overwrite m.d.vt.v m.d.vt.t else s).tag =
        (depVt s.storeVT gd).t := by rw [← hs1]; rfl
    rw [this]
    simp only [write1ReplyOf, vtOf, Hgt]
    rfl

end

end Perennial.gryff.replica2
