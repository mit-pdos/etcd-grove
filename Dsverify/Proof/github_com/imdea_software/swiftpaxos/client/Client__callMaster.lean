/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__callMaster.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`c.callMaster(method)` (client/client.go) for `"GetReplicaList"` and `"GetLeader"`: up to 100
`call`s of the master's method, each with a fresh (zero) reply decoded by the kit codec; the
master's answer is the frozen `masterSpec`'s (`masterSpec_getReplicaList`,
`masterSpec_getLeader`), and the decoded reply is that answer (`grl_inj`: the codec's encoding is
injective).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client.cn

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [examples.swiftnet.Assumptions]

/-- The master's answer to `GetReplicaList`. -/
def rlPhi (γc γm : GName) : List w8 → GoString → IProp netDistGF := fun rep _ =>
  iprop(∃ (nodes : List GoString) (alive : List Bool),
    ⌜rep = (sp.KitVal.getReplicaListReply nodes alive true).encode ∧
      alive.length = nodes.length⌝ ∗ ∃ fr, sp.cfg γc γm nodes.length fr nodes)

/-- The zero `GetReplicaListReply`. -/
abbrev rlX0 : sp.KitVal := .getReplicaListReply [] [] false

/-- What decoding the reply into `rp` gives. -/
def rlTheta (rp : Loc) : List w8 → Bool → IProp netDistGF := fun rep _ =>
  iprop((∃ y : sp.KitVal, ⌜rep = y.encode ∧ y.tag = 6⌝ ∗
      kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.GetReplicaListReply.ty) #rp)
        (DFrac.own 1) (sp.KitVal.merge rlX0 y)) ∨
    ⌜∀ y : sp.KitVal, y.tag = 6 → sp.KitVal.wf y → rep ≠ y.encode⌝)

/-- The master's answer to `GetLeader`. -/
def glPhi : List w8 → GoString → IProp netDistGF := fun rep _ =>
  iprop(⌜∃ id : w64, rep = (sp.KitVal.getLeaderReply id).encode⌝)

/-- The zero `GetLeaderReply`. -/
abbrev glX0 : sp.KitVal := .getLeaderReply 0

/-- What decoding the reply into `rp` gives. -/
def glTheta (rp : Loc) : List w8 → Bool → IProp netDistGF := fun rep _ =>
  iprop((∃ y : sp.KitVal, ⌜rep = y.encode ∧ y.tag = 4⌝ ∗
      kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.GetLeaderReply.ty) #rp)
        (DFrac.own 1) (sp.KitVal.merge glX0 y)) ∨
    ⌜∀ y : sp.KitVal, y.tag = 4 → sp.KitVal.wf y → rep ≠ y.encode⌝)

end defs

end client.cn

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [errors.Assumptions] [replica.defs.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodec` for the frozen statements,
-- `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

set_option goose.wp.extras true

theorem client.Client.callMasterRL.wp_proof (wp_call : client.Client.call.specI (hG := hG)) :
    client.Client.callMasterRL.specI (hG := hG) := by
  intro cl v W γc γm
  wp_start as ⟨Hcl, #Hq, #Hcs, #Hko, #Hmc, %HS⟩
  wp_auto
  ipersist method
  ihave HI : (∃ (k : w64) (a1 a2 a3 a4 : Loc), "Hi" ∷ i_ptr ↦ k ∗ "Hcl" ∷ cl ↦ v ∗
      "rl" ∷ rl_ptr ↦ a1 ∗ "rlArgs" ∷ rlArgs_ptr ↦ a2 ∗ "gl" ∷ gl_ptr ↦ a3 ∗
      "glArgs" ∷ glArgs_ptr ↦ a4 ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 100⌝ : IProp netDistGF) $$ [i Hcl rl rlArgs gl glArgs]
  · iexists _, _, _, _, _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · rename_i rp
    irename : (rp ↦ (Perennial.zero_val replica.defs.GetReplicaListReply :
      replica.defs.GetReplicaListReply)) => Hrp
    ihave %Hrpnn := typedPointsto_not_null $$ Hrp
    ihave %Hapnn := typedPointsto_not_null $$ «$r0»
    ihave HD : kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.GetReplicaListReply.ty)
        #rp) (DFrac.own 1) client.cn.rlX0 $$ [Hrp]
    · unfold kitValOwn structOwn
      iexists replica.defs.GetReplicaListReply.ty, rp
      isplitr
      · ipureintro; exact ⟨rfl, Hrpnn⟩
      isplitr
      · ipureintro; rfl
      iexists slice.nil, slice.nil
      isplitl [Hrp]
      · iexact Hrp
      isplitr
      · iapply ownSlice_nil
      · iapply ownSlice_nil
    wp_apply wp_call cl v v.master' W masterAddr _ go!"Master" go!"GetReplicaList"
      (sp.masterSpec γc γm) _ _ (client.cn.rlPhi γc γm) iprop(True)
      (kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.GetReplicaListReply.ty) #rp)
        (DFrac.own 1) client.cn.rlX0) (client.cn.rlTheta rp)
      $$ [$Hcl $Hq $Hcs $Hko $Hmc HD «$r0»] as %err ⟨Hcl, Hres⟩
    · isplitr
      · ipureintro; exact ⟨rfl, HS⟩
      isplitl [«$r0»]
      · iapply enc_of C
        simp only [net.rpc.RpcCodec.enc]
        iexists DFrac.own 1, sp.KitVal.getReplicaListArgs
        isplitl [«$r0»]
        · unfold kitValOwn structOwn
          iexists replica.defs.GetReplicaListArgs.ty, «$r0_ptr»
          isplitr
          · ipureintro; exact ⟨rfl, Hapnn⟩
          isplitr
          · ipureintro; rfl
          iexists _
          iexact «$r0»
        iintro %x' %Heq -
        simp only [sp.KitVal.equiv] at Heq
        subst Heq
        isplitl
        rotate_left
        · itrivial
        iapply (sp.masterSpec_getReplicaList (γc := γc) (γm := γm) _ _).2
        isplitr
        · ipureintro; rfl
        iintro %nodes %alive Hcfg %Hal
        unfold client.cn.rlPhi
        iexists nodes, alive
        iframe Hcfg
        ipureintro; exact ⟨rfl, Hal⟩
      iframe HD
      iintro !> HD %rep
      iapply KitLike.dec_intro
      unfold decT
      iexists client.cn.rlX0
      iframe HD
      isplitr
      · ipureintro; trivial
      isplit
      · iintro %y %Hy Hown
        unfold client.cn.rlTheta
        ileft; iexists y; iframe Hown; ipureintro; exact ⟨Hy.1, Hy.2.1⟩
      · iintro %Hn %ok -
        unfold client.cn.rlTheta
        iright; ipureintro; intro y hy hw; exact Hn y hy hw
    icases Hres with (⟨%Herr, -, %rep, Hphi, Hth⟩ | %Herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _, _
        iframe
        ipureintro; word
    subst Herr
    unfold client.cn.rlPhi
    icases Hphi with ⟨%nodes, %alive, %Hrep, %fr, #Hcfg⟩
    ihave Hmem := sp.cfg_memIs (γc := γc) (γm := γm) _ _ _ $$ Hcfg
    icases Hmem with ⟨#Hm, %-⟩
    ihave %Hok := memIs_ok γm nodes $$ Hm
    unfold client.cn.rlTheta
    icases Hth with (⟨%y, %Hy, Hown⟩ | %Hn)
    rotate_left
    · exfalso
      exact Hn (.getReplicaListReply nodes alive true) rfl (by simp [sp.KitVal.wf]) Hrep.1
    have hy := client.cn.grl_inj y nodes alive true Hy.2
      (client.cn.nodes_body_bound nodes alive true Hok.1 Hok.2 Hrep.2) (Hy.1.symm.trans Hrep.1)
    subst hy
    rw [client.cn.merge_grl]
    unfold kitValOwn structOwn
    icases Hown with ⟨%ty, %p, %Hv, %Hty, %s1, %s2, Hp, Hs1, Hs2⟩
    subst Hty
    have hp : p = rp := by
      have h := Hv.1
      simp [interface.mkOk] at h
      exact (go.intoVal_inj h).symm
    subst hp
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hcl
    ileft
    isplitr
    · ipureintro; rfl
    iexists p, s1, s2, nodes, alive, fr
    iframe
    isplitr
    · ipureintro; rfl
    iframe Hcfg
    ipureintro; exact Hrep.2
  · wp_apply errors.wp_New_errorString as %x _
    iapply HΦ
    iframe Hcl
    iright
    ipureintro; simp [interface.mkOk]

theorem client.Client.callMasterL.wp_proof (wp_call : client.Client.call.specI (hG := hG)) :
    client.Client.callMasterL.specI (hG := hG) := by
  intro cl v W γc γm
  wp_start as ⟨Hcl, #Hq, #Hcs, #Hko, #Hmc, %HS⟩
  wp_auto
  ipersist method
  ihave HI : (∃ (k : w64) (a1 a2 a3 a4 : Loc), "Hi" ∷ i_ptr ↦ k ∗ "Hcl" ∷ cl ↦ v ∗
      "rl" ∷ rl_ptr ↦ a1 ∗ "rlArgs" ∷ rlArgs_ptr ↦ a2 ∗ "gl" ∷ gl_ptr ↦ a3 ∗
      "glArgs" ∷ glArgs_ptr ↦ a4 ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 100⌝ : IProp netDistGF) $$ [i Hcl rl rlArgs gl glArgs]
  · iexists _, _, _, _, _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · rename_i rp
    irename : (rp ↦ (Perennial.zero_val replica.defs.GetLeaderReply :
      replica.defs.GetLeaderReply)) => Hrp
    ihave %Hrpnn := typedPointsto_not_null $$ Hrp
    ihave %Hapnn := typedPointsto_not_null $$ «$r0»
    ihave HD : kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.GetLeaderReply.ty)
        #rp) (DFrac.own 1) client.cn.glX0 $$ [Hrp]
    · unfold kitValOwn structOwn
      iexists replica.defs.GetLeaderReply.ty, rp
      isplitr
      · ipureintro; exact ⟨rfl, Hrpnn⟩
      isplitr
      · ipureintro; rfl
      iexact Hrp
    wp_apply wp_call cl v v.master' W masterAddr _ go!"Master" go!"GetLeader"
      (sp.masterSpec γc γm) _ _ client.cn.glPhi iprop(True)
      (kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.GetLeaderReply.ty) #rp)
        (DFrac.own 1) client.cn.glX0) (client.cn.glTheta rp)
      $$ [$Hcl $Hq $Hcs $Hko $Hmc HD «$r0»] as %err ⟨Hcl, Hres⟩
    · isplitr
      · ipureintro; exact ⟨rfl, HS⟩
      isplitl [«$r0»]
      · iapply enc_of C
        simp only [net.rpc.RpcCodec.enc]
        iexists DFrac.own 1, sp.KitVal.getLeaderArgs
        isplitl [«$r0»]
        · unfold kitValOwn structOwn
          iexists replica.defs.GetLeaderArgs.ty, «$r0_ptr»
          isplitr
          · ipureintro; exact ⟨rfl, Hapnn⟩
          isplitr
          · ipureintro; rfl
          iexists _
          iexact «$r0»
        iintro %x' %Heq -
        simp only [sp.KitVal.equiv] at Heq
        subst Heq
        isplitl
        rotate_left
        · itrivial
        iapply (sp.masterSpec_getLeader (γc := γc) (γm := γm) _ _).2
        isplitr
        · ipureintro; rfl
        iintro %id
        unfold client.cn.glPhi
        ipureintro; exact ⟨id, rfl⟩
      iframe HD
      iintro !> HD %rep
      iapply KitLike.dec_intro
      unfold decT
      iexists client.cn.glX0
      iframe HD
      isplitr
      · ipureintro; trivial
      isplit
      · iintro %y %Hy Hown
        unfold client.cn.glTheta
        ileft; iexists y; iframe Hown; ipureintro; exact ⟨Hy.1, Hy.2.1⟩
      · iintro %Hn %ok -
        unfold client.cn.glTheta
        iright; ipureintro; intro y hy hw; exact Hn y hy hw
    icases Hres with (⟨%Herr, -, %rep, Hphi, Hth⟩ | %Herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _, _
        iframe
        ipureintro; word
    subst Herr
    unfold client.cn.glPhi
    icases Hphi with %Hrep
    obtain ⟨id, Hrep⟩ := Hrep
    unfold client.cn.glTheta
    icases Hth with (⟨%y, %Hy, Hown⟩ | %Hn)
    rotate_left
    · exfalso
      exact Hn (.getLeaderReply id) rfl (by simp [sp.KitVal.wf]) Hrep
    obtain ⟨i', rfl⟩ : ∃ i', y = .getLeaderReply i' := by
      cases y <;> simp_all [sp.KitVal.tag]
    unfold kitValOwn structOwn
    simp only [sp.KitVal.merge]
    icases Hown with ⟨%ty, %p, %Hv, %Hty, Hp⟩
    subst Hty
    have hp : p = rp := by
      have h := Hv.1
      simp [interface.mkOk] at h
      exact (go.intoVal_inj h).symm
    subst hp
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hcl
    ileft
    isplitr
    · ipureintro; rfl
    iexists p, _
    iframe
    ipureintro; rfl
  · wp_apply errors.wp_New_errorString as %x _
    iapply HΦ
    iframe Hcl
    iright
    ipureintro; simp [interface.mkOk]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
