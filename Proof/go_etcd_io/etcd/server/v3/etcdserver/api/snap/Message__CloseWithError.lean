/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__CloseWithError.lean`, over
`snap/message.go`'s translation (with its body since 2026-11-19; until then a trust-boundary axiom,
rafthttp stage 7d, D42) and `msgIs`'s definition (`Proof/.../snap/Defs.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseWithError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode snap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.Message.CloseWithError.wp_proof :
    snap.Message.CloseWithError.spec (GF := GF) (hG := hG) := by
  intro m ml rc err
  wp_start as #Hm
  unfold msgIs msgRO
  icases Hm with ⟨#Hml, ⟨%tsz, #Htsz, %Htsz⟩, ⟨%rd, %ri, #Hrd, %Hrd, #Hstr, #Hclose⟩, ⟨%c, %γc, #Hc, #Hbag⟩⟩
  subst Hrd
  try wp_auto
  wp_apply Hclose as %cerr -
  -- `cerr != nil`, then `err == nil` (a comparison with nil never panics), then the send
  rcases cerr with _ | ci <;> try wp_auto
  all_goals
    rcases err with _ | ei <;> try wp_auto
  all_goals
    wp_apply (wp_bag_send γc c _ (fun _ : Bool => iprop(True)))
    · iframe Hbag
    try wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
