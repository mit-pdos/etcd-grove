/- (PR raft#86) The proof of `raft.nextTerm`. -/
module

public import Spec.go_etcd_io.raft.v3.raft__nextTerm
public import Spec.go_etcd_io.raft.v3.lockedRand__Intn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- As `resetRandomizedElectionTimeout`'s: `globalRand` and its `isLockedRand` come from
`isPkgInit` (`isInitialized`). -/
theorem raft.nextTerm.wp_proof
    (wp_lockedRand_Intn : lockedRand.Intn.spec (GF := GF) (hG := hG)) :
    raft.nextTerm.spec (GF := GF) (hG := hG) := by
  intro c V r id s
  wp_start as Hphys
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %e5, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_apply wp_lockedRand_Intn _ _ (by decide) $$ [$HglobalRand] as %v %Hv
  rw [show ((s.term &&& W64 18446744073709486080) >>> W64 16 + W64 1) <<< W64 16 |||
      v &&& W64 65535 = nextTermOf s.term v from rfl]
  iapply HΦ $$ %v
  iexact Hphys

end proof

end EtcdGrove
end Perennial
