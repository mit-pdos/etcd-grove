/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/decodeState.lean`. Lean-first (no
Rocq counterpart). (2026-10-22: `getMap` of each map, `getMap.lean`.)
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.decodeState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.getMap

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

theorem decodeState.wp_proof (wp_getMap : getMap.spec (GF := GF) (hG := hG)) :
    decodeState.spec (GF := GF) (hG := hG) := by
  intro b dq kvs ops Hkvs Hops
  wp_start as Hb
  try wp_auto
  wp_apply wp_getMap b dq kvs (encMap ops) Hkvs $$ [Hb] as %mK %rest ⟨Hrest, Hback, %K, HK, %HKv⟩
  · unfold encState; iexact Hb
  try wp_auto
  ihave Hrest := (show (rest ↦*{dq} encMap ops : IProp GF) ⊣⊢ rest ↦*{dq} (encMap ops ++ []) by
    rw [List.append_nil]; exact .rfl).1 $$ Hrest
  wp_apply wp_getMap rest dq ops [] Hops $$ [$Hrest] as %mA %rest2 ⟨Hr2, Hback2, %A, HA, %HAv⟩
  try wp_auto
  ihave %Hr2l := ownSlice_len _ _ _ $$ Hr2
  have Hz : sint.Z rest2.len = 0 := by have := Hr2l.1; simp at this; word
  rw [decide_eq_true (by word)]
  try wp_auto
  iapply HΦ
  isplitl [Hr2 Hback Hback2]
  · ihave Hr := Hback2 $$ Hr2
    rw [List.append_nil]; unfold encState
    iapply Hback $$ Hr
  iexists K, A
  iframe HK HA
  ipureintro; exact ⟨HKv, HAv⟩

end proof

end kv
end EtcdGrove
end Perennial
