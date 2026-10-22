/-
`Main(clients, ops)` (`examples/linkv3/linkv3.go`; D20, D21, 2026-10-19): three etcd members
started in process as putget3's (`startMember`, on linkv3's names and ports), a client connected
to the first, with etcd's default configuration (its default retries; D29), and linkv's
`Check(cli, clients, ops, 0)`, with a panic if porcupine reports the history `Illegal`.
Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the three peer addresses and
the first member's client address (`netAddrFree`, D19d), the main thread's token and `Main`'s named
premises (`linkv3.premises`: putget3's at linkv3's configuration, `Proof/.../linkv3/Defs.lean`),
`Main(clients, ops)` does not panic and returns `Ok` (the check ran: the history is linearizable)
or `Unknown` (a step before the check failed).

**The pure premises:** putget3's (`putget3.Main.spec`), with the member ids in `bootstrap`'s order
(`linkv3.BootFacts`), and `Run`'s bounds on `clients` and `ops` (linkv's `Main.spec`). Stated
under the cache package's assumptions, as putget3's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ErrorStringLeaf] [context.ErrorStringIsError]
    (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM)
    (clients ops : w64),
  BootFacts id₁ id₂ id₃ bootLog →
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  mvcc.backendNoCompaction → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3 ∗
      netAddrFree (GF := GF) peerAddr₁ ∗ netAddrFree (GF := GF) peerAddr₂ ∗
      netAddrFree (GF := GF) peerAddr₃ ∗ netAddrFree (GF := GF) clientAddr₁ ∗
      threadTok ∗ premises N id₁ id₂ id₃ bootLog }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3.Main)) (Val #clients))
      (Val #ops))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end linkv3
end EtcdGrove
end Perennial
