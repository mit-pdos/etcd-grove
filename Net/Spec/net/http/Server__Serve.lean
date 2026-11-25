/-
`s.Serve(lis)` (the model's `server.go`) on the server `s` as `http.Serve` makes it (`srvConst`,
`srvDflt`, `srvServe`, `srvServeRest`: no TLS, no hooks, no `BaseContext`/`ConnContext`, no error
log, never shut down), on this node's listener `l` at `la` (`isListener`, `netLisOn`; shared,
`lisInv`), whose every address `a` it takes serves net/rpc's `CONNECT path` handshake
(`srvAddr s a (P a) (Q a) path`, `path` a `reqPath` of at most `2^20` bytes): it accepts
connections and serves each with `conn.serve` in a goroutine of its own (with the fresh thread token
of its `go` statement), retrying after a temporary `Accept` error (logged, then a sleep), until an
`Accept` fails otherwise; then it closes the listener (through its `onceCloseListener`) and returns
the error. It never panics. Proved in `Net/Proof/net/http/Server__Serve.lean`.
-/
module

public import Net.Proof.net.http.ServeLoopDefs
public import Perennial.Proof.log.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.Serve.spec : Prop :=
  ∀ (s : Loc) (lis : GoInterface) (l : w64) (la : GoString) (P Q : GoString → Proto GF)
    (path : List w8),
  reqPath path → path.length ≤ 2 ^ 20 →
  {{ httpEnv ∗ readEnv ∗ serveEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      isPkgInit (PROP := IProp GF) pkg_id.log ∗ srvConst s ∗ srvDflt s ∗ srvServe s ∗
      srvServeRest s ∗ ctxKeys ∗ wPools ∗ rPool ∗
      (∃ tm : time.Time, globalAddr net.http.aLongTimeAgo ↦□ tm) ∗
      (□ ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ → srvAddr s a (P a) (Q a) path) ∗
      net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
    (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"Serve")) (Val #lis))
  {{ (err : GoInterface), RET #err; True }}

end spec

end net.http
end Perennial
