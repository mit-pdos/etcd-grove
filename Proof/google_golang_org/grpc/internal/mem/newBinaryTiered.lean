/-
Proof of `Spec/google_golang_org/grpc/internal/mem/newBinaryTiered.lean` (grpc-mem, 2026-11-26): the
exponents sorted (`slices.Sort` at `uint8`) and compacted (the model's `compactExponents`) stay at most
`62`, so the loop never takes its `fmt.Errorf` branch and indexes the two 63-entry tables
(`slices.Repeat([]int{-1}, 63)`) in range; the two gap-filling loops index them in range too.
-/
module

public import Spec.google_golang_org.grpc.internal.mem.newBinaryTiered
public import Spec.google_golang_org.grpc.internal.mem.compactExponents
public import Perennial.Spec.slices.Repeat
public import Perennial.Proof.slices.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.mem.Assumptions]

theorem grpc.internal.mem.newBinaryTiered.wp_proof
    (wp_compactExponents : grpc.internal.mem.compactExponents.spec (GF := GF) (hG := hG))
    (wp_Repeat : _root_.Perennial.slices.Repeat.spec (GF := GF) (hG := hG)) :
    grpc.internal.mem.newBinaryTiered.spec (GF := GF) (hG := hG) := by
  intro f fb s xs Hxs Hlen
  wp_start as ⟨#Hpkg, Hs, #Hf⟩
  ihave #Hfact : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.mem.internalMemInit
      (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.mem.internalMemInit
  wp_auto
  trace_state
  sorry

end proof

end EtcdGrove
end Perennial
