/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__forever.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__forever
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.forever.wp_proof : lease.Lease.forever.spec (GF := GF) (hG := hG) := by
  intro l e
  wp_start as ⟨He, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨-, -, -, #Hforever, -⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold leaseExpiry at HR
  icases HR with ⟨%e2, He2⟩
  icases ptsto_halves_combine _ _ _ $$ [$He $He2] with ⟨%Heq, He⟩
  wp_auto
  icases ptsto_halves_split _ _ $$ He with ⟨He, He2⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk He2]
  · iframe #
    inext
    iunfold leaseExpiry
    iexists _
    iexact He2
  iapply HΦ $$ He

end proof

end EtcdGrove
end Perennial
