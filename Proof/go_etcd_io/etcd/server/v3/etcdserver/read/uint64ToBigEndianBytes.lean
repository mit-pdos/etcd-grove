/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/uint64ToBigEndianBytes.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.uint64ToBigEndianBytes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

theorem read.uint64ToBigEndianBytes.wp_proof :
    read.uint64ToBigEndianBytes.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hsl, -⟩
  · ipureintro; word
  (try wp_auto)
  have hl : (List.replicate 8 (zero_val w8)).length = 8 := by simp
  wp_apply encoding.binary.wp_BigEndian_PutUint64 sl _ [] n hl $$ [Hsl] as Hsl
  · simp only [List.append_nil]; iexact Hsl
  (try wp_auto)
  iapply HΦ
  simp only [List.append_nil]
  unfold beBytes
  iexact Hsl

end proof

end EtcdGrove
end Perennial
