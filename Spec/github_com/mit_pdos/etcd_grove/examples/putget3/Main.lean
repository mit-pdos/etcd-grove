/-
`Main()` (`examples/putget3/putget3.go`; D21 stage M5, 2026-10-19): three etcd members started in
process, each serving its raft handler on its own peer listener, a client connected to the first, a
`Put` of `k` with value `v`, a `Get` of `k`, and a panic unless the `Get` returned `v`. Lean-first
(no Rocq counterpart). putget's `Main.spec` for three members.

**The triple:** from the package's `isPkgInit`, the right to listen on the three peer addresses and
the first member's client address (`netAddrFree`, which program start gives once each: D19d), the
main thread's token and `Main`'s named premises (`putget3.premises`), `Main()` returns: it does not
panic, so the `Get` that returned `nil` returned the `Put`'s value.

**The pure premises:** putget's, with the three members' ids and bootstrap log Go computes
(`putget3.BootFacts`: the ids' 16 low bits distinct and not `0`, D21e (A)); the method-set
classes `ErrorStringLeaf` and `context.ErrorStringIsError`, which make `io.EOF`'s package fact the
server's `eofVar`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry),
  BootFacts id₁ id₂ id₃ ctxs boot →
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.putget3 ∗
      netAddrFree (GF := GF) peerAddr₁ ∗ netAddrFree (GF := GF) peerAddr₂ ∗
      netAddrFree (GF := GF) peerAddr₃ ∗ netAddrFree (GF := GF) clientAddr₁ ∗
      httpProtoFree (GF := GF) peerAddr₁ ∗ httpProtoFree (GF := GF) peerAddr₂ ∗
      httpProtoFree (GF := GF) peerAddr₃ ∗ threadTok ∗ premises N id₁ id₂ id₃ ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.putget3.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end putget3
end EtcdGrove
end Perennial
