/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/encodeState.lean`. Lean-first (no
Rocq counterpart). (2026-10-22: `putMap` of each map, `putMap.lean`.)
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.encodeState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.putMap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem encodeState.wp_proof (wp_putMap : putMap.spec (GF := GF) (hG := hG)) :
    encodeState.spec (GF := GF) (hG := hG) := by
  intro mK mA K A dq1 dq2
  wp_start as ⟨HK, HA⟩
  try wp_auto
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := w8) (GF := GF)
  wp_apply wp_putMap slice.nil [] mK K dq1 $$ [$Hnil $Hncap $HK]
    as %s1 ⟨HK, Hcap1, %kvs, Hs1, %Hkvs⟩
  wp_apply wp_putMap s1 _ mA A dq2 $$ [$Hs1 $Hcap1 $HA] as %s2 ⟨HA, -, %ops, Hs2, %Hops⟩
  iapply HΦ
  iframe HK HA
  iexists kvs, ops
  rw [List.nil_append] at *
  unfold encState
  iframe Hs2
  ipureintro; exact ⟨Hkvs, Hops⟩

end proof

end kv
end EtcdGrove
end Perennial
