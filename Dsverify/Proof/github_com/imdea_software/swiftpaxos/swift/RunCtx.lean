/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunCtx.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The run-loop handlers' context after P2-B** (round 13, sv-swc): `swift.runCtxD` replaces
`swift.runCtx` (RunSpecs.lean), which `swift.runInv` cannot provide: its node invariant is the
old `nodeInv` (the replica's half of its state is `nodeInvD`'s), its `delivered` is the old
`isCMap` with the persistent `readerBorrow` (unprovable: finitely many reader bundles), and its
`cntL` invariant is the old `cntLInv` (`cntL`'s lock holds `cntLInvR`, P2-B). Here:

* `swift.cntLInvR` (moved from RunInv.lean): `cntL`'s lock invariant with P2-B's bundles;
* `swift.runCtxD`: the embedded replica, the protocol, `nodeInvD`, `delivered` with its view's
  invariant `delivInv` (some names), `cntL` over `cntLInvR` (some names);
* `swift.runReader rp γdl`: the run loop's own reader bundle of `delivered` (owned, given back
  by each handler).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.CntL

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- `cntL`'s lock invariant with P2-B's reader bundles (`swift.cntLGhost`, CntL.lean); replaces
`swift.cntLInv` (RunSpecs.lean). Change log C22 (round 19): half of `seqnum` (the run loop's
`swift.seqOwn` has the other half and the numbering's `numHi`). -/
def swift.cntLInvR (rp : Loc) (dm : GoSlice) (γdl γn : GName) (d : w64) : IProp netDistGF :=
  iprop(∃ (n c : w64) (T : List Nat), typedPointsto (swift.fld rp go!"seqnum") n (DFrac.own (1 : Qp).half) ∗
    swift.fld rp go!"routineCount" ↦ c ∗ swift.cntLGhost γn dm γdl d c T)

/-- The run-loop handlers' persistent context (see the file header). -/
def swift.runCtxD (γ : sp.Names) (γc γm γl γw γv γe γo : GName) (sn : swift.StN) (γdl : GName)
    (rp : Loc) (N r k : Nat) :
    IProp netDistGF :=
  iprop(∃ (rr : Loc) (me : w32) (fr : Bool) (l : List GoString) (dm : GoSlice),
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    ⌜sp.rid me = r ∧ 0 ≤ sint.Z me ∧ r < N ∧ 1 ≤ N ∧ N ≤ 7 ∧ nodeOf l r = some k⌝ ∗
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
    swift.fld rp go!"delivered" ↦□ dm ∗
    github_com.orcaman.concurrent_map.isCMapV dm γdl swift.deliveredR ∗
    (∃ (γx γxp γxm γa γxe γrm : GName) (str : swift.CommandId → GoString),
      inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str)) ∗
    (∃ (dmc : GoSlice) (γn : GName) (d : w64),
      sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInvR rp dmc γdl γn d)) ∗
    -- L2 (notes/prove-s2-e.md): the node's claimed ghost, for its protocol steps' resolutions
    client.nodeGhostOk γ (sp.PNode.rep k))

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 4000000 in
instance swift.runCtxD_persistent (γ : sp.Names) (γc γm γl γw γv γe γo : GName) (sn : swift.StN)
    (γdl : GName) (rp : Loc)
    (N r k : Nat) : Persistent (swift.runCtxD γ γc γm γl γw γv γe γo sn γdl rp N r k) := by
  unfold swift.runCtxD; infer_instance

/-- The run loop's numbering (change log C22, M3): its half of `seqnum` (`cntLInvR` has the
other: only the run loop writes it) at its node's next number `numHi`. -/
def swift.seqOwn (γ : sp.Names) (rp : Loc) (k : Nat) : IProp netDistGF :=
  iprop(∃ n : w64, typedPointsto (swift.fld rp go!"seqnum") n (DFrac.own (1 : Qp).half) ∗
    sp.numHi γ k n ∗ ⌜0 ≤ sint.Z n⌝)

/-- The run loop's own reader bundle of `delivered` (see the file header). -/
def swift.runReader (rp : Loc) (γdl : GName) : IProp netDistGF :=
  iprop(∃ dm : GoSlice, swift.fld rp go!"delivered" ↦□ dm ∗ swift.delReader dm γdl)

end defs

end Perennial.github_com.imdea_software.swiftpaxos
