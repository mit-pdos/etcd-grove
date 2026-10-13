/-
`(*EtcdServer).start()` (`server.go`), translated with its body: it sets the fields the server's
goroutines share and starts `run`. Lean-first (the request path's unit 4c, 2026-10-13); see
`InvStart.lean`.
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

/-- **`s.start()`** from the construction premise (`isServerBuilt`): it sets the snapshot
defaults, the wait registries (`w`, `applyWait`), the channels `done`, `stop`, `stopping`, the
server's context, the read loop's `*Read` and the leader-change notifier, sets up `GoAttach`'s
protocol, and starts `run` (`isServerRun`, with the write budget `WB N`); it returns the server's
persistent views (`isServerReq`, at the wait's fresh names, and `isServerRead`) and what `Start`'s
goroutines and the request path's get (`srvStarted`). -/
abbrev EtcdServer.start.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (WB : Nat → IProp GF) (N : Nat),
  (∀ a b : Nat, WB (a + b) ⊣⊢ WB a ∗ WB b) → 2 ^ 64 ≤ N →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ WB N }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"start")) (Val #()))
  {{ RET #(); ∃ γw : GName, isServerReq s E { ρ with wait := γw } ∗ isServerRead s E γr ∗
      srvStarted s γr ρ Er.RQ }}

end spec

end EtcdGrove
end Perennial
