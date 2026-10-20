/-
`Main(clients, ops, sched)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3b, 2026-10-20):
three etcd members started in process and served (`startMember`, on linkv3p's names and ports), a
one-attempt client connected to each (`newClient`), the partitioner forked on the schedule
`sched` (`go partitioner(srvs, sched)`: the links between members cut and mended as its steps say,
any steps), and `Check(clis, clients, ops, 0)` (linkv's workload, each operation through a random
member), with a panic if porcupine reports the history `Illegal`. Lean-first (no Rocq
counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the six addresses
(`netAddrFree`, D19d), the schedule read-only (`sched ↦*□ steps`, for *every* list of steps), the
main thread's token and `Main`'s named premises (`linkv3p.premises`: putget3's at linkv3p's
configuration, `Proof/.../linkv3p/Defs.lean`), `Main(clients, ops, sched)` does not panic and
returns `Ok` (the check ran: the history is linearizable) or `Unknown` (a step before the check
failed).

**The pure premises:** linkv3's (`linkv3.Main.spec`: putget3's with the member ids in `bootstrap`'s
order, `linkv3p.BootFacts`, and `Run`'s bounds on `clients` and `ops`) plus v3rpc's method sets
(`v3rpc.ServerMethodSets`, which serving every member takes). Stated under the cache package's
assumptions, as putget3's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ErrorStringLeaf] [context.ErrorStringIsError]
    (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM)
    (clients ops : w64) (sched : GoSlice)
    (steps : List github_com.mit_pdos.etcd_grove.examples.linkv3p.Step),
  BootFacts id₁ id₂ id₃ bootLog →
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  mvcc.backendNoCompaction → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      netAddrFree (GF := GF) peerAddr₁ ∗ netAddrFree (GF := GF) peerAddr₂ ∗
      netAddrFree (GF := GF) peerAddr₃ ∗ netAddrFree (GF := GF) clientAddr₁ ∗
      netAddrFree (GF := GF) clientAddr₂ ∗ netAddrFree (GF := GF) clientAddr₃ ∗
      sched ↦*□ steps ∗ threadTok ∗ premises N id₁ id₂ id₃ bootLog }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.Main)) (Val #clients))
      (Val #ops)) (Val #sched))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end linkv3p
end EtcdGrove
end Perennial
