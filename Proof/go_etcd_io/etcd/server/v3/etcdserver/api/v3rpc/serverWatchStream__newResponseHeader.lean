/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__newResponseHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.serverWatchStream.newResponseHeader.wp_proof :
    v3rpc.serverWatchStream.newResponseHeader.spec (GF := GF) (hG := hG) := by
  intro sws r rev
  wp_start as #Hs
  iapply wp_fupd
  iunfold v3rpc.swsIs at Hs
  icases Hs with ⟨%Hnn, -, #Hcid, #Hmid, -, #Hsg, -, -, -, -, -, -, -, -, -, #Hok, -⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨-, -, #Hrs, -⟩
  iunfold v3rpc.raftStatusOk at Hrs
  icases Hrs with ⟨#HT, #HL⟩
  (try wp_auto)
  wp_apply HT as %t _
  (try wp_auto)
  wp_apply HL as %l _
  irename «$r0» => Hh
  generalize «$r0_ptr» = h at *
  ihave %Hhn := typedPointsto_not_null _ _ _ $$ Hh
  iStructNamed Hh
  ipersist ClusterId
  ipersist MemberId
  ipersist Revision
  ipersist RaftTerm
  ipersist LeaderId
  imodintro
  iapply HΦ
  iexists t, l
  iunfold hdrFull
  iframe #
  ipureintro; exact Hhn

end proof

end EtcdGrove
end Perennial
