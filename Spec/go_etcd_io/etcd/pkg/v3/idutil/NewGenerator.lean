/-
`idutil.NewGenerator(memberID, now)` (`id.go`): a new request id generator. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewGenerator(memberID, now)` returns a generator (`idGen`; until D17, 2026-10-17, with its
`2 ^ 48 - 1` id credits, now the lifetime bound `idCred` is the caller's premise): its prefix
`memberID << 48`, its suffix the 40 low bits of `now`'s milliseconds, shifted by 8. The ghost
names `γi` are the caller's (2026-10-16, D13a: the server chooses them before `newRaftNode` fixes
the raft contract's environment over them): since D21e (A) (stage M4, 2026-10-19) the cluster's
claims (`idClusterInv`, with the claimers' facts `Φs` per prefix, the cluster's choice; unit V2)
and the member's share at its prefix (`idShare`: its prefix's entry, its slots), both from the
cluster's allocation (`idCluster_alloc`); the generator's facts are its prefix's, `Φs γi.pfx`.
(Until M4 it took fresh names, `idNamesFresh`, and gave the reserved id `0`, `idNoZero`, which
the cluster's allocation now gives.) -/
abbrev idutil.NewGenerator.spec : Prop :=
  ∀ (γi : IdNames) (memberID : w16) (now : time.Time)
    (Φs : w64 → w64 → List w8 → GName → IProp GF),
  γi.pfx = idPfxOf memberID →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idShare γi ∗
      idClusterInv γi.issued γi.cnt Φs }}
    (App (App (Val (@! idutil.NewGenerator)) (Val #memberID)) (Val #now))
  {{ (g : Loc), RET #g; idGen γi g (Φs γi.pfx) }}

end spec

end EtcdGrove
end Perennial
