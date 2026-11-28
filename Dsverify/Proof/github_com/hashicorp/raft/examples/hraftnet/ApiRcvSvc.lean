/-
The API's receiver over its service spec `apiSvc` (`ApiSvc.lean`): the `API` methods' specs (S5's,
`Spec/.../service/API__*.lean`, taken as hypotheses, a proof's callees) give the receiver's obligations
`ApiRcvLaws` (`CodecApi.lean`) for `apiSvc γ fc`, with `apiP` (the package and `isAPI`) as the
receiver's persistent facts: a deposit's request is the decoded one (`encApplyArgs_inj`, ...), and the
method's reply facts are the deposit's success answer. `Read` (S6) is a hypothesis here. With `apiRcv`, a server's `*API` is a net/rpc receiver of `apiSvc`
(`Server.Register`'s premise): `apiRcv_apiSvc`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecApi
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiCodecDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiSvc
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Apply
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__AddVoter
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__AddNonvoter
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__DemoteVoter
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__RemoveServer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__LeadershipTransfer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Snapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.API__Status

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport service github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [spkg : service.Assumptions]
variable [rpkg : github_com.hashicorp.raft.Assumptions]

/-- The API receiver's persistent facts: the package and `isAPI`. -/
abbrev apiP (a : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (fc : FCtx GF) (alb : GName) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
    isAPI a γ rc i fc alb)

theorem apiMeth_Apply (wp : API.Apply.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"Apply" applyArgsOwn encApplyArgs applyReplyOwn
      encApplyReply (apiSvc γ fc go!"Apply") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  rw [if_pos rfl]
  icases HS with ⟨%v, %n, %Hbs, Htok, Hans⟩
  obtain rfl := encApplyArgs_inj va v (by omega) Hbs
  rcases wa with ⟨sl⟩
  unfold applyArgsOwn
  ipersist Hp
  ipersist Hown
  wp_apply (wp a ap rp γ rc i fc alb sl va.data n (zero_val ApplyReply)) $$ [Hr Htok] as ⟨%rep, Hr, Hout⟩
  · iframe Hr Htok
    iframe #
  iapply HΨ
  iexists rep, (ApplyReplyV.mk rep.Status' rep.Found' rep.V')
  iframe Hr
  isplitr
  · unfold applyReplyOwn; ipureintro; exact ⟨rfl, rfl, rfl⟩
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  isplitr
  · ipureintro; rfl
  iexact Hout

theorem apiMeth_AddVoter (wp : API.AddVoter.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"AddVoter" adminArgsOwn encAdminArgs adminReplyOwn
      encAdminReply (apiSvc γ fc go!"AddVoter") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  unfold adminDep
  icases HS with ⟨%v, %Hbs, HW, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  icases HW with %HW
  unfold addReqW at HW
  wp_apply (wp a ap rp γ rc i fc alb _ _ (zero_val AdminReply)) $$ [Hr] as ⟨%rep, Hr⟩
  · iframe Hr
    iframe #
    ipureintro; exact HW
  iapply HΨ
  iexists rep, (AdminReplyV.mk rep.Ok')
  iframe Hr
  isplitr
  · unfold adminReplyOwn; ipureintro; rfl
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

theorem apiMeth_AddNonvoter (wp : API.AddNonvoter.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"AddNonvoter" adminArgsOwn encAdminArgs adminReplyOwn
      encAdminReply (apiSvc γ fc go!"AddNonvoter") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  unfold adminDep
  icases HS with ⟨%v, %Hbs, HW, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  icases HW with %HW
  unfold addReqW at HW
  wp_apply (wp a ap rp γ rc i fc alb _ _ (zero_val AdminReply)) $$ [Hr] as ⟨%rep, Hr⟩
  · iframe Hr
    iframe #
    ipureintro; exact HW
  iapply HΨ
  iexists rep, (AdminReplyV.mk rep.Ok')
  iframe Hr
  isplitr
  · unfold adminReplyOwn; ipureintro; rfl
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

theorem apiMeth_DemoteVoter (wp : API.DemoteVoter.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"DemoteVoter" adminArgsOwn encAdminArgs adminReplyOwn
      encAdminReply (apiSvc γ fc go!"DemoteVoter") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  unfold adminDep
  icases HS with ⟨%v, %Hbs, HW, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  icases HW with %HW
  unfold srvReqW at HW
  wp_apply (wp a ap rp γ rc i fc alb _ _ (zero_val AdminReply)) $$ [Hr] as ⟨%rep, Hr⟩
  · iframe Hr
    iframe #
    ipureintro; exact HW
  iapply HΨ
  iexists rep, (AdminReplyV.mk rep.Ok')
  iframe Hr
  isplitr
  · unfold adminReplyOwn; ipureintro; rfl
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

theorem apiMeth_RemoveServer (wp : API.RemoveServer.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"RemoveServer" adminArgsOwn encAdminArgs adminReplyOwn
      encAdminReply (apiSvc γ fc go!"RemoveServer") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  unfold adminDep
  icases HS with ⟨%v, %Hbs, HW, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  icases HW with %HW
  unfold srvReqW at HW
  wp_apply (wp a ap rp γ rc i fc alb _ _ (zero_val AdminReply)) $$ [Hr] as ⟨%rep, Hr⟩
  · iframe Hr
    iframe #
    ipureintro; exact HW
  iapply HΨ
  iexists rep, (AdminReplyV.mk rep.Ok')
  iframe Hr
  isplitr
  · unfold adminReplyOwn; ipureintro; rfl
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

theorem apiMeth_LeadershipTransfer (wp : API.LeadershipTransfer.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"LeadershipTransfer" adminArgsOwn encAdminArgs adminReplyOwn
      encAdminReply (apiSvc γ fc go!"LeadershipTransfer") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  unfold adminDep
  icases HS with ⟨%v, %Hbs, HW, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  unfold transferReqW
  wp_apply (wp a ap rp γ rc i fc alb _ _ (zero_val AdminReply)) $$ [Hr HW] as ⟨%rep, Hr⟩
  · iframe Hr HW
    iframe #
  iapply HΨ
  iexists rep, (AdminReplyV.mk rep.Ok')
  iframe Hr
  isplitr
  · unfold adminReplyOwn; ipureintro; rfl
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

theorem apiMeth_Snapshot (wp : API.Snapshot.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"Snapshot" adminArgsOwn encAdminArgs adminReplyOwn
      encAdminReply (apiSvc γ fc go!"Snapshot") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  unfold adminDep
  icases HS with ⟨%v, %Hbs, HW, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  wp_apply (wp a ap rp γ rc i fc alb (zero_val AdminReply)) $$ [Hr] as ⟨%rep, Hr⟩
  · iframe Hr
    iframe #
  iapply HΨ
  iexists rep, (AdminReplyV.mk rep.Ok')
  iframe Hr
  isplitr
  · unfold adminReplyOwn; ipureintro; rfl
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

theorem apiMeth_Status (wp : API.Status.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF)
    (i : SID) (fc : FCtx GF) (alb : GName) :
    apiMeth.spec (apiP a γ rc i fc alb) a go!"Status" adminArgsOwn encAdminArgs statusReplyOwn
      encStatusReply (apiSvc γ fc go!"Status") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hapi⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold apiSvc
  simp only [↓reduceIte]
  (repeat rw [if_neg (by decide)])
  (try rw [if_pos rfl])
  icases HS with ⟨%v, %Hbs, Hans⟩
  obtain rfl := encAdminArgs_inj va v (by omega) Hbs
  rcases wa with ⟨id, addr⟩
  unfold adminArgsOwn
  icases Hown with %Hown
  obtain ⟨rfl, rfl⟩ := Hown
  ipersist Hp
  wp_apply (wp a ap rp γ rc i fc alb (zero_val StatusReply)) $$ [Hr] as ⟨%rep, Hr⟩
  · iframe Hr
    iframe #
  iapply HΨ
  iexists rep, (StatusReplyV.mk rep.Leader' rep.LeaderID' rep.Configured' rep.Servers' rep.Voters')
  iframe Hr
  isplitr
  · unfold statusReplyOwn; ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists _
  ipureintro; rfl

/-- **A server's `*API` `a` meets the receiver's obligations for `apiSvc γ fc`**, from the
methods' specs (`Read`'s receiver obligation a hypothesis). -/
theorem apiRcvLaws_of (wpAp : API.Apply.spec (GF := GF)) (wpAV : API.AddVoter.spec (GF := GF))
    (wpAN : API.AddNonvoter.spec (GF := GF)) (wpDV : API.DemoteVoter.spec (GF := GF))
    (wpRS : API.RemoveServer.spec (GF := GF)) (wpLT : API.LeadershipTransfer.spec (GF := GF))
    (wpSn : API.Snapshot.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF) (i : SID)
    (fc : FCtx GF) (alb : GName)
    (mRead : apiMeth.spec (apiP a γ rc i fc alb) a go!"Read" readArgsOwn encReadArgs readReplyOwn
      encReadReply (apiSvc γ fc go!"Read"))
    (wpSt : API.Status.spec (GF := GF)) :
    ApiRcvLaws (apiP a γ rc i fc alb) a (apiSvc γ fc) where
  enc_AddNonvoter := fun args Φ => apiSvc_admin_enc γ fc _ (by simp) args Φ
  meth_AddNonvoter := apiMeth_AddNonvoter wpAN a γ rc i fc alb
  enc_AddVoter := fun args Φ => apiSvc_admin_enc γ fc _ (by simp) args Φ
  meth_AddVoter := apiMeth_AddVoter wpAV a γ rc i fc alb
  enc_Apply := fun args Φ => apiSvc_Apply_enc γ fc args Φ
  meth_Apply := apiMeth_Apply wpAp a γ rc i fc alb
  enc_DemoteVoter := fun args Φ => apiSvc_admin_enc γ fc _ (by simp) args Φ
  meth_DemoteVoter := apiMeth_DemoteVoter wpDV a γ rc i fc alb
  enc_LeadershipTransfer := fun args Φ => apiSvc_admin_enc γ fc _ (by simp) args Φ
  meth_LeadershipTransfer := apiMeth_LeadershipTransfer wpLT a γ rc i fc alb
  enc_Read := fun args Φ => apiSvc_Read_enc γ fc args Φ
  meth_Read := mRead
  enc_RemoveServer := fun args Φ => apiSvc_admin_enc γ fc _ (by simp) args Φ
  meth_RemoveServer := apiMeth_RemoveServer wpRS a γ rc i fc alb
  enc_Snapshot := fun args Φ => apiSvc_admin_enc γ fc _ (by simp) args Φ
  meth_Snapshot := apiMeth_Snapshot wpSn a γ rc i fc alb
  enc_Status := fun args Φ => apiSvc_Status_enc γ fc args Φ
  meth_Status := apiMeth_Status wpSt a γ rc i fc alb

/-- **A server's `*API` `a` is a net/rpc receiver of `apiSvc γ fc`** (`Server.Register`'s premise),
from the methods' specs. -/
theorem apiRcv_apiSvc (wpAp : API.Apply.spec (GF := GF)) (wpAV : API.AddVoter.spec (GF := GF))
    (wpAN : API.AddNonvoter.spec (GF := GF)) (wpDV : API.DemoteVoter.spec (GF := GF))
    (wpRS : API.RemoveServer.spec (GF := GF)) (wpLT : API.LeadershipTransfer.spec (GF := GF))
    (wpSn : API.Snapshot.spec (GF := GF)) (a : Loc) (γ : GNames) (rc : RCtx GF) (i : SID)
    (fc : FCtx GF) (alb : GName)
    (mRead : apiMeth.spec (apiP a γ rc i fc alb) a go!"Read" readArgsOwn encReadArgs readReplyOwn
      encReadReply (apiSvc γ fc go!"Read"))
    (wpSt : API.Status.spec (GF := GF)) :
    ⌜a ≠ null⌝ ∗ net.rpc.codecSet (hraftCodec (GF := GF)) ∗ apiP a γ rc i fc alb ⊢
    (hraftCodec (GF := GF)).rcv (ptrI service.API.ty a)
      (net.rpc.rcvrIs hraftCodec (ptrI service.API.ty a) (apiSvc γ fc) go!"API" false) :=
  apiRcv _ a _ (apiRcvLaws_of wpAp wpAV wpAN wpDV wpRS wpLT wpSn a γ rc i fc alb mRead wpSt)

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
