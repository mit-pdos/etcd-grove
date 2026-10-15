/-
`(*EtcdServer).Start()` (`server.go`), translated with its body: `start`, then ten goroutines
through `GoAttach`. Lean-first (the request path's unit 4c, 2026-10-13); see `InvStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Start()`** from the construction premise, the caller's thread token and two reader
slots of `s.lgMu` (one for its `GoAttach`es, given back; one for `monitorFileDescriptor`'s
goroutine, which calls `Logger()`): `start`, then the read loop (`LinearizableReadLoop`, verified)
and nine names-only monitors (trust-boundary contracts) attached; it returns the server's views and
the slots left for request goroutines. -/
abbrev EtcdServer.Start.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat),
  2 ^ 64 ≤ N →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ threadTok ∗
      srvLgReader s ∗ srvLgReader s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
  {{ RET #(); ∃ γw : GName, isServerReq s E { ρ with wait := γw } ∗ isServerRead s E γr ∗
      srvGoRes s ∗ srvLgReader s ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        srvReadReader s γr) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
        srvWgReader s) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
        ∃ n : Loc, srvLeaderChangedAddr s ↦□ n ∗ notifyReader n) }}

end spec

end EtcdGrove
end Perennial
