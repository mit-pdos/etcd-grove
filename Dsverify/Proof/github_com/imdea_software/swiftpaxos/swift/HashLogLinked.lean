/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HashLogLink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`HashLog`'s linked results (swift/dpath.go): each proof applied to its callees' linked results;
`crypto/sha256.Sum256` through the harness's spec (`Sum256.wp_proof`, the ideal hash: trusted).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLog
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogUpdate
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeaf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [crypto.sha256.Assumptions]

theorem wp_putId : putId.spec := putId.wp_proof
theorem wp_hashStart : hashStart.spec :=
  hashStart.wp_proof wp_putId crypto.sha256.Sum256.wp_proof
theorem wp_hash : hash.spec := hash.wp_proof wp_putId crypto.sha256.Sum256.wp_proof
theorem HashLog.wp_chain : HashLog.chain.spec := HashLog.chain.wp_proof wp_hash wp_hashStart
theorem wp_NewHashLog : hlog.NewHashLog.spec := hlog.NewHashLog.wp_proof
theorem HashLog.wp_update : hlog.HashLog.update.spec := hlog.HashLog.update.wp_proof HashLog.wp_chain
theorem HashLog.wp_Update : hlog.HashLog.Update.spec := hlog.HashLog.Update.wp_proof HashLog.wp_update
theorem HashLog.wp_Append : hlog.HashLog.Append.spec :=
  hlog.HashLog.Append.wp_proof HashLog.wp_update wp_hash HashLog.wp_chain

end link

end swift

end Perennial.github_com.imdea_software.swiftpaxos
