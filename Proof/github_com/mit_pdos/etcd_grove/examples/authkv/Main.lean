/-
`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b): **not proved** (a `sorry`). Lean-first
(no Rocq counterpart).

What the proof needs (`notes/decisions.md`, "E2b of the auth plan", "What is left"): the server's
start with auth's authority (E2a: `NewAuthStore` in the mode `on γa`, the simple provider's
`tokenProviderOkCtx`, the admin side's authority in the server's environment, `srvAuthBound`);
`SetUp`'s admin calls through the client's `Auth` methods to the apply layer's admin steps
(`apply.isAuthSteps`), the history after them `setupSt` at every later position (no later admin
request is sent); `AuthInfoFromCtx`'s binding naming the context's token (today `ctxBound` says
only "some token issued to its user"); the client's auth contract (`ClientAuth.lean`); the
client's write path without refusal-freedom (D29's `noRefusalAt` is false of an auth-enabled
member: a refused write is retried, every attempt refused); and the checks' proofs over the
workload, with `Permitted`'s (`Permitted.lean`) and the model's verdicts (`Model.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Main

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Main.wp_proof : Main.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authkv
end EtcdGrove
end Perennial
