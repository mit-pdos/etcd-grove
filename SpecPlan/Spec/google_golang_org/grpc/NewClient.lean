/-
`grpc.NewClient(target, opts...)` (grpc-go, assumed: `clientconn.go`).

Users: the client's `dial` (`client.go:328`, 1c), through `dialWithBalancer`.

Why true: `NewClient` parses the target, applies the options in order (`DialCfg`'s functions),
builds the connection without connecting (connections are made on the first call, to the
resolver's addresses); it fails with an error on an unknown scheme or an invalid option combination,
never a panic. The workload premise `msgsFit` is taken here, the connection's only producer
(Grpc/Api.lean's header), so no call takes a size premise.

Changes: from `specs-ref/Spec/google_golang_org/grpc/NewClient.lean`: the options as `dialOptAt`,
the connection `connAt` (the old `grpcConn` with its address list), the size premise moved from
every call (`opSizeOk`, `notes/invoke-size.md`) to here.

Margin: the code accepts messages over the limits too (refusing them below `2 ^ 48`, panicking
above).
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The configuration of a dial with no option: grpc's own invoker and streamer, no address
guaranteed anything, no per-RPC metadata. -/
def DialCfg.default : DialCfg (GF := GF) :=
  { ui := none, si := none, A := fun _ => iprop(True), R := fun md => iprop(⌜md = []⌝) }

/-- `grpc.NewClient(target, opts...)` with options acting as `fs`: a connection configured by them,
or an error. -/
def NewClient.spec : Prop :=
  ∀ (target : GoString) (opts : GoSlice) (vs : List GoInterface)
    (fs : List (DialCfg (GF := GF) → DialCfg (GF := GF))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ ⌜msgsFit⌝ ∗ opts ↦*□ vs ∗ ([∗list] v; f ∈ vs; fs, dialOptAt v f) }}
    (App (App (Val (@! google_golang_org.grpc.NewClient)) (Val #target)) (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      (⌜err = GoInterface.nil⌝ ∗
        let cfg := fs.foldl (fun c f => f c) DialCfg.default
        connAt cc cfg.A cfg.ui cfg.si cfg.R) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Grpc
end EtcdGrove
end Perennial
