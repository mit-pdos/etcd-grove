/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/leaseIDToBytes.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.leaseIDToBytes
public import Spec.encoding.binary.bigEndian__PutUint64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.leaseIDToBytes.wp_proof
    (hP : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG)) :
    schema.leaseIDToBytes.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  wp_apply wp_bePutUint64 hP bs _ n (by simp) $$ [$Hbs] as Hbs
  iapply HΦ
  simp only [u64Be]
  iexact Hbs

end proof

end EtcdGrove
end Perennial
