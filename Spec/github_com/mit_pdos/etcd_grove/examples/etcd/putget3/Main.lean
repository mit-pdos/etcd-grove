/-
`Main()` (`examples/etcd/putget3/etcd_putget3.go`; D21 stage M5, 2026-10-19): three etcd members started in
process, each serving its raft handler on its own peer listener, a client connected to the first, a
`Put` of `k` with value `v`, a `Get` of `k`, and a panic unless the `Get` returned `v`. Lean-first
(no Rocq counterpart). putget's `Main.spec` for three members.

**The triple:** from the package's `isPkgInit`, the right to listen on the three peer addresses and
the first member's client address (`netAddrFree`, which program start gives once each: D19d), the
main thread's token and `Main`'s named premises (`etcd_putget3.premises`), `Main()` returns: it does not
panic, so the `Get` that returned `nil` returned the `Put`'s value.

**The pure premises:** putget's, with the three members' ids and bootstrap log Go computes
(`etcd_putget3.BootFacts`: the ids' 16 low bits distinct and not `0`, D21e (A)); the method-set
classes `ErrorStringLeaf` and `context.ErrorStringIsError`, which make `io.EOF`'s package fact the
server's `eofVar`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry),
  BootFacts id₁ id₂ id₃ ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the server's gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.putget3 ∗
      -- (2026-11-05, hub step 7) the members' start bundles: each member's WAL directory fresh,
      -- the right to listen on its peer address with its HTTP protocol unregistered, and member 1's
      -- on its client address
      etcdstart.memberStartRes (GF := GF) name₁ ⟨some peerAddr₁, some clientAddr₁⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₂ ⟨some peerAddr₂, none⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₃ ⟨some peerAddr₃, none⟩ ∗
      threadTok ∗ premises N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_putget3
end EtcdGrove
end Perennial
