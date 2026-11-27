/-
`s.checkLeaseTimeToLiveKeys(ctx, keys)` (`v3_server.go`, the fork `d26dd5da6`, F7 fork, SPECULATIVE): the check
of the keys `LeaseTimeToLive` returns. Lean-first (no Rocq counterpart); vocabulary `LeaseCheck.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck
public import Proof.context.LibKeys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.checkLeaseTimeToLiveKeys(ctx, keys)`** (F7 fork, 2026-11-26, SPECULATIVE: the fork's fix of
`issues/etcd-lease-timetolive-keys-toctou.md`), any goroutine, with the server's auth store at the lease checks'
lower bounds (`srvAuthLeaseLb`) and its request side (`srvAuthAt`), a lower bound `n` of the auth store's
published index, a reader of the store (`E.RD`), and the keys (`keys ↦* kbs`, each key's bytes, of a length below
`2 ^ 63 - 1`, as `IsRangePermitted` takes them), which it gives back as the byte lists `ks`: on `nil`, auth
disabled at a state no older than `n`, or the request's principal (bound to the token `tok`) an admin at one or
allowed to read (`IsRangePermitted(k, [])`) every key of `ks` at one; on an error, one of the auth package's error
variables (`authApplyErrIs`). The principal is the one `AuthInfoFromCtx` returns now, as `checkLeaseTimeToLive`'s
is: both are bound to `tok`. -/
abbrev EtcdServer.checkLeaseTimeToLiveKeys.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (keys : GoSlice) (kbs : List GoSlice) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ auth.authPubLbM E.authMode n ∗
      mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗
      keys ↦* kbs ∗ [∗list] kb ∈ kbs, ∃ k : List w8, kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"checkLeaseTimeToLiveKeys"))
      (Val #(GoInterface.ok ctx))) (Val #keys))
  {{ (err : GoInterface), RET #err; E.RD ∗ keys ↦* kbs ∗
      ∃ ks : List (List w8), ([∗list] kb;k ∈ kbs;ks, kb ↦* k) ∗ authApplyErrIs err ∗
        (∀ _ : err = GoInterface.nil, leaseCheckFrom (srvTLSId s) E tok n
          (fun info => [∗list] k ∈ ks, auth.permVerdictFrom E.authMode n info k [] .read GoInterface.nil)) }}

end spec

end EtcdGrove
end Perennial
