/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/isConnectedToQuorumSince.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isConnectedToQuorumSince
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.numConnectedSince
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.quorum

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem isConnectedToQuorumSince.wp_proof
    (hN : numConnectedSince.spec (GF := GF) (hG := hG))
    (hQ : quorum.spec (GF := GF) (hG := hG)) :
    isConnectedToQuorumSince.spec (GF := GF) (hG := hG) := by
  intro tr since self members ms
  wp_start as ⟨#Htr, Hms⟩
  wp_auto
  wp_apply hN tr since self members ms $$ [Hms] as %n Hms
  · iframe #; iframe Hms
  (try wp_auto)
  wp_apply hQ as %q -
  (try wp_auto)
  iapply HΦ
  iframe Hms

end proof

end EtcdGrove
end Perennial
