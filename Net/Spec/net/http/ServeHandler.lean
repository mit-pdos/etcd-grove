/-
`http.Serve(lis, h)` (the model's `server.go`: `&Server{Handler: h}`, then `Server.Serve`) on this
node's listener `l` at `la` (`isListener`, `netLisOn`; shared, `lisInv`), whose every address `a` it
takes serves net/rpc's `CONNECT path` handshake with the handler `h` (`srvAddrH h a (P a) (Q a)
path`: `h`'s `ServeHTTP` contract, or `DefaultServeMux`'s for a `nil` `h`, `effHandler`): it serves
the connections the listener accepts until an `Accept` fails otherwise than temporarily, then returns
the error. It never panics. The handler's contract is a premise: `Serve.spec_rpc` (`http.Serve(l,
nil)` over `DefaultServeMux`'s routes) follows from it and the mux's dispatch. Proved in
`Net/Proof/net/http/ServeHandler.lean`.
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
abbrev Serve.specHandler : Prop :=
  ∀ (h lis : GoInterface) (l : w64) (la : GoString) (P Q : GoString → Proto GF) (path : List w8),
  reqPath path → path.length ≤ 2 ^ 20 →
  {{ httpEnv ∗ readEnv ∗ serveEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      isPkgInit (PROP := IProp GF) pkg_id.log ∗ isPkgInit (PROP := IProp GF) pkg_id.time ∗
      isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
      ctxKeys ∗ wPools ∗ rPool ∗ (∃ tm : time.Time, globalAddr net.http.aLongTimeAgo ↦□ tm) ∗
      (□ ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ → srvAddrH h a (P a) (Q a) path) ∗
      net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
    (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #h))
  {{ (err : GoInterface), RET #err; True }}

end spec

end net.http
end Perennial
