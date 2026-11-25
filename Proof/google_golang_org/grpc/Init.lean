/-
Package initialization of `google_golang_org.grpc`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`grpcInit`, `cache/v3/Base.lean`): `EnableTracing` holds `false` for good. Its
initializer initializes its imports, allocates `EnableTracing` (`var EnableTracing bool`,
`trace.go:33` at v1.84.0: translated, no initializer, so its cell holds `false`), runs the
untranslated initializers of its other variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its three translated `init`
functions (`dialoptions.go`, `rpc_util.go`, `server.go`; phase7-inits, 2026-11-25, until then the
trust-boundary axiom `initFuncsOk`), which store function values and closures in `internal`'s hook
variables, through `internal`'s invariants (`grpc/internal/Hooks.lean`); it allocates the slices the
closures append to (`globalDialOptions`, `globalPerTargetDialOptions`, `globalServerOptions`). (Until 2026-11-19 the cell
came from the trust-boundary axiom `DefaultBackoffConfig_init`.) No translated code writes
`EnableTracing`; a program that writes it (etcd's `embed` at log level debug, grpc-proxy `--debug`)
gets no proof: it would need the cell, which `finish` makes persistent; it runs its translated initializer of `logger`, `grpclog.Component(...)` (phase7-inits batch 2,
2026-11-25, until then the trust-boundary axiom `opaqueInitsOk`; `Component`'s proof, through
`grpclog`'s fact).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.time.Link
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.google_golang_org.grpc.grpclog.Init
public import Proof.google_golang_org.grpc.internal.Init
public import Proof.google_golang_org.grpc.keepalive.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.peer.Init
public import Proof.google_golang_org.grpc.resolver.Init
public import Proof.google_golang_org.grpc.stats.Init
public import Proof.net.Init
public import Proof.google_golang_org.grpc.internal.Hooks

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial
