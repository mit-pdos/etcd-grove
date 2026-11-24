/-
`Check(addrs, voters)` (kvcheck.go): the checking client's process, as the top-level theorem runs it.
The addresses split (`SplitAddrs`) and checked (`ValidAddrs`: else it returns at once, so every
configuration is allowed and the store's resources below are needed only if the check passes); the
checker built; one to three proposers of configuration changes (`reconfigure`) and a
disruptor of leadership (`disrupt`) in goroutines until the clients are done; the clients are
`lintest.Run`'s, 4 of 100 operations of `Gen`'s traffic (`do`'s Put and Get, `read`'s Read), traced
with a counter clock, and porcupine checks the trace against `Model` with no timeout: it answers `Ok`
(`lintest.Run`'s theorem, from `do`/`read` logically atomic over the store), so `Check` does not panic
and returns.

At kvnet's store `γ` (`Store.lean`; decision B: the store's invariant is global), if the addresses are
valid: its invariant, the
client half of its state at the empty map (no operation has run), its operation counter half at `0`
and every replica's read sequence number at `0` (`kvCnt`), each replica's address carrying kvnet's
protocols at the store's facts (`addrsProto (kvFacts γ _)`, any configuration change allowed: the
store's conf policy decides at the commit); in every case the globals a request reads (`connGlobals`), and the
counter clock's bound (`receiptBound GF ≤ 2^63`: fewer readings than the clock's range).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.StoreDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Net raft_kvnet go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions] [go.IntoValInj GoString]
variable [kvnet_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ (γ : KdNames) (addrs : GoString) (voters : w64),
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗
      context.isClosedchanInit ∗ connGlobals ∗
      (⌜validAddrs (splitAddrs addrs) (uint.nat voters) = true⌝ -∗
        rkvInv γ ∗ rkvVal γ raft_kvreconf.kvEmpty ∗
        kvCnt γ (splitAddrs addrs).length false (W64 0) ∗
        kvCnt γ (splitAddrs addrs).length true (W64 0) ∗
        addrsProto (kvFacts γ (fun _ => True)) (splitAddrs addrs)) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Check))
      (Val #addrs)) (Val #voters))
  {{ RET #(); True }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
