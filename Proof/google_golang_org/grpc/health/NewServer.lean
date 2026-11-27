module

public import Spec.google_golang_org.grpc.health.NewServer
public import Perennial.Proof.sync.Results

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
variable [package_sem : google_golang_org.grpc.health.Assumptions]

/-- grpc's `health.NewServer` (`server.go`; until 2026-11-26 a trust-boundary axiom): allocates a
`Server` with its status map (`""` serving), an empty watchers' map and the zero `RWMutex`, whose
writer guard it makes over the status map (`healthLockInv`). -/
theorem health.NewServer.wp_proof : health.NewServer.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w32) go.string _) as %mS HS
  repeat (wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ HS as HS; try wp_auto)
  iapply wp_fupd
  wp_apply (wp_map_make1 (K := GoString) (V := GoMap) go.string _) as %mU HU
  ihave %hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  imod (update_into_persistently (P := ownMap (GF := GF) mU (DFrac.own 1) (∅ : GMap GoString GoMap))) $$ HU
    with #HU
  imod (update_into_persistently (P := structFieldRef google_golang_org.grpc.health.Server
    go!"UnimplementedHealthServer" «$r0_ptr» ↦ (zeroValDef : google_golang_org.grpc.health.grpc_health_v1.UnimplementedHealthServer))) $$ UnimplementedHealthServer with #Huh
  imod (update_into_persistently (P := structFieldRef google_golang_org.grpc.health.Server
    go!"shutdown" «$r0_ptr» ↦ false)) $$ shutdown with #Hsd
  imod (update_into_persistently (P := structFieldRef google_golang_org.grpc.health.Server
    go!"statusMap" «$r0_ptr» ↦ mS)) $$ statusMap with #HfS
  imod (update_into_persistently (P := structFieldRef google_golang_org.grpc.health.Server
    go!"updates" «$r0_ptr» ↦ mU)) $$ updates with #HfU
  imod (sync.init_RWMutex (healthLockInv (GF := GF) mS) (E := ⊤)
      (structFieldRef google_golang_org.grpc.health.Server go!"mu" «$r0_ptr»)) $$ [HS] mu with Hslots
  · inext; unfold healthLockInv; iexists _; iexact HS
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hg⟩
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact hnn
  unfold grpcHealthSrv
  iexists mS, mU, zeroValDef
  iframe #

end proof

end EtcdGrove
end Perennial
