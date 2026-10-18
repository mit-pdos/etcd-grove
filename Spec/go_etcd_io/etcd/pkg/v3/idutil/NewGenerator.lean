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
`2 ^ 48 - 1` id credits, now the lifetime bound `idCred` is the caller's premise): its prefix `memberID << 48`, its suffix the 40 low bits of `now`'s milliseconds, shifted
by 8; with the claimers' facts `Φ` the caller chooses (unit V2). The ghost names `γi` are the
caller's, fresh (`idNamesFresh`, `idNamesFresh_alloc`; 2026-10-16, D13a: the server chooses them
before `newRaftNode` fixes the raft contract's environment over them). For a member id that is
not `0` (its prefix is not), the id `0` reserved (`idNoZero`; D19c, 2026-10-18: a generator of
prefix `0` does issue `0` after a wrap of its suffix,
`issues/etcd-request-id-zero-bootstrap-confchange.md`). -/
abbrev idutil.NewGenerator.spec : Prop :=
  ∀ (γi : IdNames) (memberID : w16) (now : time.Time) (Φ : w64 → List w8 → GName → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idNamesFresh γi }}
    (App (App (Val (@! idutil.NewGenerator)) (Val #memberID)) (Val #now))
  {{ (g : Loc), RET #g; idGen γi g Φ ∗ (⌜memberID ≠ W16 0⌝ -∗ idNoZero γi) }}

end spec

end EtcdGrove
end Perennial
