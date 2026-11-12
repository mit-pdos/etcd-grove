/-
`grpc.model.acceptRunConns(s)` (per-type stage B, B1a, 2026-11-11; Scope r5 §2.2): a leaf of the trusted `Serve` model
(`TrustedCode/google_golang_org/grpc.lean`), a model-only name with no Go body of its
own. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **acceptRunConns** -- the same composite as `acceptRun` after `Serve` returned for a listener
failure: `handleRawConn`'s goroutines of the connections already open keep running `serveStreams`
(test T5b). It returns the next call one of them delivered (`true`), or `false` once none is left
open or the server is stopped. -/
abbrev grpc.model.acceptRunConns.spec : Prop :=
  ∀ (gs : Loc) (γ : GName) (c : GrpcSrvCfg GF),
  {{ grpcConnsLink gs γ ∗ grpcSrvCfg γ c ∗ ⌜grpcRepliesFit⌝ }}
    (App (Val (@! google_golang_org.grpc.model.acceptRunConnsName)) (Val #gs))
  {{ (r : val) (ok : Bool), RET (PairV r #ok);
      (⌜ok = true⌝ ∗ grpcConnsLink gs γ ∗ grpcAccepted γ c r) ∨ ⌜ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
