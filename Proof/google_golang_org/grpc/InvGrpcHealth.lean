/-
**grpc's health server** (split out of `InvGrpcServer.lean`, 2026-11-25, `notes/phase7-endstate.md`
§4): `grpcHealthSrv hs`, persistent: grpc's `*health.Server` `hs` (`health.NewServer()`), whose
`SetServingStatus` is safe from any goroutine. Until 2026-11-26 (grpc-health) an axiomatized predicate,
with the specs of `health.NewServer`, `Server.SetServingStatus` and
`grpc_health_v1.RegisterHealthServer` trust-boundary axioms; now defined over the translated
`server.go`, and those three proved over the real code.

**The definition.** The server's lock `mu` (a `sync.RWMutex`, through Perennial's writer guard
`isRWMutexGuard`: `SetServingStatus` takes it for writing) guards its status map `statusMap`
(`healthLockInv`); the fields themselves are read-only after `NewServer`, the embedded
`UnimplementedHealthServer` (an empty struct `RegisterHealthServer`'s `testEmbeddedByValue` loads)
too. Two facts are of the code this repository verifies, not of every `health.Server`:
- `shutdown` is `false`: only `Shutdown` sets it, and etcd never calls it (`v3rpc` calls `NewServer`,
  `SetServingStatus` and `RegisterHealthServer` only, `grpc.go`, `health.go`);
- the watchers' map `updates` is empty, read-only: only the `Watch` handler adds to it, and no proved
  execution runs grpc's health handlers (the service's entries of etcd's service table are
  `grpcNoCall`, `examples/etcd/dist/S2Interim.lean`'s `etcdSvc`). When a handler of the health
  service gets a spec (`Watch`, `Check`), this predicate grows: `updates` owned under the lock, each
  watcher's channel with the lock holder as its only sender (`setServingStatusLocked`'s drain-then-send
  cannot block then), and `Check`'s readers through the `RWMutex`'s reader tokens.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.RWMutexGuard
public import GeneratedProof.google_golang_org.grpc.health

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The health server's lock predicate at fraction `q`** (`mu`'s; a writer holds it at 1): its
status map `statusMap` (at `mS`), any statuses. -/
def healthLockInv (mS : Loc) (q : Qp) : IProp GF :=
  iprop(∃ S : GMap GoString w32, ownMap mS (DFrac.own q) S)

instance healthLockInv_fractional (mS : Loc) : Fractional (healthLockInv (GF := GF) mS) where
  fractional q1 q2 := by
    have hS := fun (S : GMap GoString w32) => (ownMap_fractional (GF := GF) mS S).fractional q1 q2
    unfold healthLockInv
    refine ⟨?_, ?_⟩
    · iintro ⟨%S, HS⟩
      icases (hS S).1 $$ HS with ⟨HS1, HS2⟩
      isplitl [HS1]
      · iexists S; iexact HS1
      · iexists S; iexact HS2
    · iintro ⟨⟨%S, HS⟩, ⟨%S2, HS2⟩⟩
      ihave %h := ownMap_agree mS _ _ S S2 $$ [HS HS2]
      · iframe
      subst h
      iexists S
      iapply (hS S).2; iframe

/-- **grpc's health server `hs`** (persistent; see the file header): its read-only fields (the
embedded `UnimplementedHealthServer`, `shutdown` false, the maps `statusMap` at `mS` and `updates`
at `mU`, the latter empty and read-only) and the writer guard of its lock `mu`, whose predicate is
`healthLockInv mS`. -/
def grpcHealthSrv (hs : Loc) : IProp GF :=
  iprop(∃ (mS mU : Loc) (uh : google_golang_org.grpc.health.grpc_health_v1.UnimplementedHealthServer),
    structFieldRef google_golang_org.grpc.health.Server go!"UnimplementedHealthServer" hs ↦□ uh ∗
    structFieldRef google_golang_org.grpc.health.Server go!"shutdown" hs ↦□ false ∗
    structFieldRef google_golang_org.grpc.health.Server go!"statusMap" hs ↦□ mS ∗
    structFieldRef google_golang_org.grpc.health.Server go!"updates" hs ↦□ mU ∗
    ownMap mU DFrac.discard (∅ : GMap GoString GoMap) ∗
    sync.isRWMutexGuard (structFieldRef google_golang_org.grpc.health.Server go!"mu" hs)
      (healthLockInv mS))

instance grpcHealthSrv_persistent (hs : Loc) : Persistent (grpcHealthSrv (GF := GF) hs) := by
  unfold grpcHealthSrv; infer_instance

end defs

end EtcdGrove
end Perennial
