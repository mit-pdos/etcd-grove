/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__callMaster.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`c.callMaster(method)` (client/client.go) for `"GetReplicaList"` and `"GetLeader"`: up to 100
`call`s of the master's method, each with a fresh (zero) reply decoded by the kit codec; the
master's answer is the frozen `masterSpec`'s, served as `withErr masterSpec` (an error answer
`([], msg)` with `msg ≠ []` is the caller's `Φ`'s left disjunct), (`masterSpec_getReplicaList`,
`masterSpec_getLeader`), and the decoded reply is that answer (the generated codec's lemmas
`dec_GetReplicaListReply`/`dec_GetLeaderReply`, NetRpc/CodecCli.lean: a successful decoding of an
encoding gives back its fields).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.errors.NewVar
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecCliProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecSrvProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitLike

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client.cn

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [examples.swiftnet.Assumptions] [π : NetProtoGS]

/-- The master's answer to `GetReplicaList`. -/
def rlPhi (γc γm : GName) : List w8 → GoString → IProp netDistGF := fun rep _ =>
  iprop(∃ (nodes : List GoString) (alive : List Bool),
    ⌜rep = (sp.KitVal.getReplicaListReply nodes alive true).encode ∧
      alive.length = nodes.length⌝ ∗ ∃ fr, sp.cfg γc γm nodes.length fr nodes)

/-- What decoding the reply into `rp` gives (`dec_GetReplicaListReply`). -/
def rlTheta (rp : Loc) : List w8 → Bool → IProp netDistGF := fun rep ok =>
  if ok then iprop(∃ (s1 s2 : GoSlice) (rl : List GoString) (al : List Bool) (r : Bool),
      rp ↦ replica.defs.GetReplicaListReply.mk s1 s2 r ∗ s1 ↦* rl ∗ s2 ↦* al ∗
      ⌜∀ rl' al' r', rep = netrpcw.encGetReplicaListReply rl' al' r' →
        rl = rl' ∧ al = al' ∧ r = r'⌝)
  else iprop(∃ v : replica.defs.GetReplicaListReply, rp ↦ v)

/-- The master's answer to `GetLeader`. -/
def glPhi : List w8 → GoString → IProp netDistGF := fun rep _ =>
  iprop(⌜∃ id : w64, rep = (sp.KitVal.getLeaderReply id).encode⌝)

/-- What decoding the reply into `rp` gives (`dec_GetLeaderReply`). -/
def glTheta (rp : Loc) : List w8 → Bool → IProp netDistGF := fun rep ok =>
  if ok then iprop(∃ id : w64, rp ↦ replica.defs.GetLeaderReply.mk id ∗
      ⌜∀ id', rep = netrpcw.encGetLeaderReply id' → id = id'⌝)
  else iprop(∃ v : replica.defs.GetLeaderReply, rp ↦ v)

end defs

end client.cn

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [errors.Assumptions] [replica.defs.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodec` for the frozen statements,
-- `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

set_option goose.wp.extras true

/-- A tagged encoding's type tag is its own. -/
theorem client.cn.tagOk_tagged (t body : List w8) (ht : t.length < 2 ^ 64) :
    tagOk t (netrpcw.tagged t body) := by
  intro t' rest h
  rw [getTag_tagged t body ht] at h
  cases h; rfl

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
    ihave HD : rp ↦ replica.defs.GetReplicaListReply.mk slice.nil slice.nil false $$ [Hrp]
    · iexact Hrp
    wp_apply wp_call cl v v.master' W masterAddr _ go!"Master" go!"GetReplicaList"
      (withErr (sp.masterSpec γc γm)) _ _
      (fun rep msg => iprop(⌜msg ≠ []⌝ ∨ (client.cn.rlPhi γc γm) rep msg)) iprop(True)
      (rp ↦ replica.defs.GetReplicaListReply.mk slice.nil slice.nil false)
      (fun rep ok => iprop((client.cn.rlPhi γc γm) rep [] ∗ client.cn.rlTheta rp rep ok))
      $$ [$Hcl $Hq $Hcs $Hko $Hmc HD «$r0»] as %err ⟨Hcl, Hres⟩
    · isplitr
      · ipureintro; exact ⟨rfl, HS, by simp [interface.mkOk]⟩
      isplitr
      · ipureintro; simp [net.rpc.maxFrameN] <;> omega
      isplitl [«$r0»]
      · iapply enc_sw C
        iapply (swiftCliCodecLaws (GF := netDistGF)).enc_GetReplicaListArgs
        isplitl [«$r0»]
        · iexact «$r0»
        iintro -
        isplitr
        · ipureintro
          simp [netrpcw.encGetReplicaListArgs, netrpcw.tagged, netrpcw.encStr, netrpcw.strct,
            netrpcw.tGetReplicaListArgs, u64Le_length, net.rpc.maxFrameN] <;> omega
        isplitl
        rotate_left
        · itrivial
        unfold withErr
        isplit
        rotate_left
        · iintro %msg %Hmsg
          ileft; ipureintro; exact Hmsg
        iapply (sp.masterSpec_getReplicaList (γc := γc) (γm := γm) _ _).2
        isplitr
        · ipureintro; rfl
        iintro %nodes %alive Hcfg %Hal
        iright
        unfold client.cn.rlPhi
        iexists nodes, alive
        iframe Hcfg
        ipureintro; exact ⟨rfl, Hal⟩
      iframe HD
      iintro !> HD %rep HΦr
      icases HΦr with (%Hne | HΦr)
      · exfalso; exact Hne rfl
      iapply dec_sw C
      iunfold client.cn.rlPhi at HΦr
      icases HΦr with ⟨%nodes, %alive, %Hrep, Hc⟩
      iapply (swiftCliCodecLaws (GF := netDistGF)).dec_GetReplicaListReply
      isplitr
      · ipureintro; rw [Hrep.1]; exact client.cn.tagOk_tagged _ _ (by decide)
      iframe HD
      iintro %ok Hok
      isplitl [Hc]
      · unfold client.cn.rlPhi; iexists nodes, alive; iframe Hc; ipureintro; exact Hrep
      unfold client.cn.rlTheta; iexact Hok
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
    simp only [ite_true]
    icases Hth with ⟨%s1, %s2, %rl, %al, %r, Hp, Hs1, Hs2, %Hy⟩
    obtain ⟨h1, h2, h3⟩ := Hy nodes alive true Hrep.1
    subst rl; subst al; subst r
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hcl
    ileft
    isplitr
    · ipureintro; rfl
    iexists rp, s1, s2, nodes, alive, fr
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
    have hz : (Perennial.zero_val replica.defs.GetLeaderReply) =
        replica.defs.GetLeaderReply.mk (W64 0) := rfl
    ihave HD : rp ↦ replica.defs.GetLeaderReply.mk (W64 0) $$ [Hrp]
    · rw [← hz]; iexact Hrp
    wp_apply wp_call cl v v.master' W masterAddr _ go!"Master" go!"GetLeader"
      (withErr (sp.masterSpec γc γm)) _ _
      (fun rep msg => iprop(⌜msg ≠ []⌝ ∨ client.cn.glPhi rep msg)) iprop(True)
      (rp ↦ replica.defs.GetLeaderReply.mk (W64 0))
      (fun rep ok => iprop(client.cn.glPhi rep [] ∗ client.cn.glTheta rp rep ok))
      $$ [$Hcl $Hq $Hcs $Hko $Hmc HD «$r0»] as %err ⟨Hcl, Hres⟩
    · isplitr
      · ipureintro; exact ⟨rfl, HS, by simp [interface.mkOk]⟩
      isplitr
      · ipureintro; simp [net.rpc.maxFrameN] <;> omega
      isplitl [«$r0»]
      · iapply enc_sw C
        iapply (swiftCliCodecLaws (GF := netDistGF)).enc_GetLeaderArgs
        isplitl [«$r0»]
        · iexact «$r0»
        iintro -
        isplitr
        · ipureintro
          simp [netrpcw.encGetLeaderArgs, netrpcw.tagged, netrpcw.encStr, netrpcw.strct,
            netrpcw.tGetLeaderArgs, u64Le_length, net.rpc.maxFrameN] <;> omega
        isplitl
        rotate_left
        · itrivial
        unfold withErr
        isplit
        rotate_left
        · iintro %msg %Hmsg
          ileft; ipureintro; exact Hmsg
        iapply (sp.masterSpec_getLeader (γc := γc) (γm := γm) _ _).2
        isplitr
        · ipureintro; rfl
        iintro %id
        iright
        unfold client.cn.glPhi
        ipureintro; exact ⟨id, rfl⟩
      iframe HD
      iintro !> HD %rep HΦr
      icases HΦr with (%Hne | HΦr)
      · exfalso; exact Hne rfl
      iapply dec_sw C
      iunfold client.cn.glPhi at HΦr
      icases HΦr with %Hrep
      obtain ⟨id0, Hrep⟩ := Hrep
      iapply (swiftCliCodecLaws (GF := netDistGF)).dec_GetLeaderReply
      isplitr
      · ipureintro; rw [Hrep]; exact client.cn.tagOk_tagged _ _ (by decide)
      iframe HD
      iintro %ok Hok
      isplitr
      · unfold client.cn.glPhi; ipureintro; exact ⟨id0, Hrep⟩
      unfold client.cn.glTheta; iexact Hok
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
    simp only [ite_true]
    icases Hth with ⟨%i', Hp, %Hy⟩
    obtain rfl := Hy id Hrep
    wp_auto
    wp_for_post
    iapply HΦ
    iframe Hcl
    ileft
    isplitr
    · ipureintro; rfl
    iexists rp, _
    iframe
    ipureintro; rfl
  · wp_apply errors.wp_New_errorString as %x _
    iapply HΦ
    iframe Hcl
    iright
    ipureintro; simp [interface.mkOk]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
