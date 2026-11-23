/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunArmsDesc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The descriptor side's arms (DescArms.lean: `getDesc`, `slowDesc`, `fastDesc` over
`getCmdDescWith.coreSpecD`) at `x.str = swift.cmdStr` (D22 (1): `runInv` records it in
`runLoopCtx`, `swift.runInv_str`), for ServersLink (round 25, sv-swc).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInvD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescArms

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- The descriptor side's `getDesc` arm (DescArms.lean) at `x.str = cmdStr` (D22 (1): `runInv`
records it). -/
theorem swift.runArm_getDescS (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_core : x.str = swift.cmdStr →
      swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm)
    (xid : swift.CommandId) (s : GoString) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #xid)) (Val #(interface.mkOk go.string #s))) (Val #slice.nil))
    {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, Hinv⟩ HΦ
  ihave ⟨%Hstr, Hinv⟩ := BI.persistent_entails_right (swift.runInv_str rp γ γc γm x) $$ Hinv
  iapply (swift.runArm_getDesc rp γ γc γm x (wp_core Hstr) xid s) $$ [Hinv] HΦ
  iframe Hpkg Hinv

/-- The descriptor side's `slowDesc` arm at `x.str = cmdStr`. -/
theorem swift.runArm_slowDescS (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_core : x.str = swift.cmdStr →
      swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm)
    (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗
        l ↦□ sa ∗ ⌜swift.slowAckRepr sa s⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck s) }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #sa.CmdId')) (Val #(interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)))
        (Val #slice.nil))
    {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, Hinv, #Hl, %Hrepr, #Hok⟩ HΦ
  ihave ⟨%Hstr, Hinv⟩ := BI.persistent_entails_right (swift.runInv_str rp γ γc γm x) $$ Hinv
  iapply (swift.runArm_slowDesc rp γ γc γm x (wp_core Hstr) l sa s) $$ [Hinv] HΦ
  iframe Hpkg Hinv Hl Hok
  ipureintro; exact Hrepr

/-- The descriptor side's `fastDesc` arm at `x.str = cmdStr`. -/
theorem swift.runArm_fastDescS (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_core : x.str = swift.cmdStr →
      swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm)
    (l : Loc) (fa : swift.MFastAck) (f : sp.FastAck) (sq : Bool) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗
        l ↦□ fa ∗ swift.fastAckRepr fa f ∗ swift.runAckW γ γc γm f }}
      (App (App (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDescSeq"))
        (Val #fa.CmdId')) (Val #(interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)))
        (Val #slice.nil)) (Val #slice.nil)) (Val #sq))
    {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, Hinv, #Hl, #Hrepr, #Hw⟩ HΦ
  ihave ⟨%Hstr, Hinv⟩ := BI.persistent_entails_right (swift.runInv_str rp γ γc γm x) $$ Hinv
  iapply (swift.runArm_fastDesc rp γ γc γm x (wp_core Hstr) l fa f sq) $$ [Hinv] HΦ
  iframe Hpkg Hinv Hl Hrepr Hw

end proof

end Perennial.github_com.imdea_software.swiftpaxos
