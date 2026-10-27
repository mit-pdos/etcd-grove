/-
`(*EtcdServer).start()` (`server.go`), translated with its body: it sets the fields the server's
goroutines share and starts `run`. Lean-first (the request path's unit 4c, 2026-10-13); see
`InvStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.start()`** from the construction premise (`isServerBuilt`): it sets the snapshot
defaults, the wait registries (`w`, `applyWait`), the channels `done`, `stop`, `stopping`, the
server's context, the read loop's `*Read` and the leader-change notifier, sets up `GoAttach`'s
protocol, and starts `run` (`isServerRun`, with the write budget `srvWTPool E` made of the `N` write
tokens, D19b: under the pure premise `receiptBound GF ≤ N + 1`, until then `srvLifeBound`); it returns the server's
persistent views (`isServerReq`, at the wait's fresh names, and `isServerRead`) and what `Start`'s
goroutines and the request path's get (`srvStarted`). -/
abbrev EtcdServer.start.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat),
  receiptBound GF ≤ N + 1 →
  -- (2026-10-19, D21 M3) a new server: the apply thread from index `0` (each applied entry takes a
  -- write token, which bounds the applied index, `srvWTPool_bound`)
  ai₀ = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"start")) (Val #()))
  {{ RET #(); ∃ γw : GName, isServerReq s E { ρ with wait := γw } ∗ isServerRead s E γr ∗
      srvStarted s γr ρ Er.RQ ∗
      -- (D19i part 2) the write budget, shared with the storage version monitor
      ∃ γp : GName, srvWTPool E γp }}

/-- **`spec` with auth on** (the auth plan's E3r, 2026-10-27): from the mode-`on` construction
premise (`isServerBuiltOn`) and the lessor finding no lease (`srvLessorNil`, `run.specOn`'s), in an
environment with auth on, `run` started with auth on (`isServerRunOn`); the request view and the
read view in the mode (`isServerReqM true`, `isServerReadM true`) and the read loop's precondition
at the mode-`on` model's state (`srvStarted` at `kvStM true`: its update fired at `kvInvOn`);
(E3s, 2026-10-27) the store's range check at a reader's lower bound, as the server keeps it
(`srvAuthLb`, what `Range.specOn` takes). -/
abbrev EtcdServer.start.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) (γa : auth.AuthNames),
  E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
  receiptBound GF ≤ N + 1 →
  ai₀ = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerBuiltOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ srvLessorNil s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"start")) (Val #()))
  {{ RET #(); ∃ γw : GName, isServerReqM true s E { ρ with wait := γw } ∗
      isServerReadM true s E γr ∗ srvAuthLb s E ∗ srvStarted s γr ρ Er.RQ (kvStM true γr.kv) ∗
      ∃ γp : GName, srvWTPool E γp }}

end spec

end EtcdGrove
end Perennial
