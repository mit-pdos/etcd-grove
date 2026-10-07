/- Port of election_proof/proof_unstable__mustCheckOutOfBounds.v. -/
import EtcdGrove.Raft.ElectionProof.Spec.unstable__mustCheckOutOfBounds

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Two `if`s, both guarding a `Panicf`; the range premise makes both conditions
`false`. `upper = offset + uint64(len(entries))` needs the slice's length, whence
`ownSlice_len`, and the no-wrap premise so that the sum is exact. -/
theorem unstable.mustCheckOutOfBounds.wp_proof :
    unstable.mustCheckOutOfBounds.spec (GF := GF) (hG := hG) := by
  intro u uv uents lo hi Hrange Hnw
  wp_start as H
  iNamed H
  unfold ownUnstable
  iNamed Hun
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hents
  rw [decide_eq_false (show ¬ uint.Z hi < uint.Z lo by omega)]
  wp_auto
  rw [decide_eq_false (show ¬ uint.Z lo < uint.Z uv.offset' by omega)]
  wp_auto
  rw [decide_eq_false (show ¬ uint.Z (uv.offset' + uv.entries'.len) < uint.Z hi by word)]
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
