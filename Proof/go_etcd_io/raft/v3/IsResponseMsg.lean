/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Spec.go_etcd_io.raft.v3.isMsgInArray

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The table `isResponseMsg` from `isInitialized`, as a slice. -/
theorem IsResponseMsg.wp_proof
    (wp_isMsgInArray : isMsgInArray.spec (GF := GF) (hG := hG)) :
    IsResponseMsg.spec (GF := GF) (hG := hG) := by
  intro t Ht
  wp_start
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 23 - W64 0 = W64 23 from rfl]
  ihave #Hsl := array_slice_bool (globalAddr isResponseMsg) responseMsgs DFrac.discard $$ isResponseMsg
  wp_apply wp_isMsgInArray t _ responseMsgs.arr Ht as %b _
  · iexact Hsl
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
