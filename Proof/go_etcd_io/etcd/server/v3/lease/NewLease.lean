/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/NewLease.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.NewLease
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.NewLease.wp_proof : lease.NewLease.spec (GF := GF) (hG := hG) := by
  intro id ttl
  wp_start as -
  (try wp_auto)
  wp_apply wp_map_make1 (K := LeaseItem) (V := Unit) as %sm Hsm
  wp_apply chan.wp_make1 (V := Unit) as %c %γc ⟨-, -, -⟩
  (try wp_auto)
  wp_alloc l as Hl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  iframe

end proof

end EtcdGrove
end Perennial
