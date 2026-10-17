/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewWatchFromWatchClientAny.lean` (pr-verify etcd#21714). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewWatchFromWatchClientAny
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem NewWatchFromWatchClientAny.wp_proof
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG)) :
    NewWatchFromWatchClientAny.spec (GF := GF) (hG := hG) := by
  intro wc c
  wp_start as #Hc
  iunfold clientConnAt at Hc
  icases Hc with ⟨%cl, #Hfix, -⟩
  iunfold clientFixed at Hfix
  icases Hfix with ⟨%Hne, #Hlg, -, -, -, -, -, -, -, -, -, -, #Hco, -⟩
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := Loc) as %mS HS
  iStructNamed «$r0»
  simp only [decide_eq_false Hne]
  wp_auto
  wp_apply wp_GetLogger c $$ [] as %lg %Hlg0
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
