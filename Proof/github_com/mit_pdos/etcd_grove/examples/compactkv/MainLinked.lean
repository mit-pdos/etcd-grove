/-
**`compactkv`** (the client's `kv.Compact`, 2026-11-01): putgetc's file, for putgetc under
compaction pressure (`common.StartCompactingServer`, revision mode, retention 1; five rounds of a
put of the round's key, a client compaction at the revision before it, a get of the key);
putgetc's and putget's history below is the originals'.

`Main`'s callees linked (item 9, 2026-10-18), by hand: `compactkv.Main.wp_proof` applied to their
linked results in the examples' shared start's `Link.lean` (`common`'s, over the server's, v3rpc's
and the client's, since 2026-10-22, D33), `context`'s, and to the trust-boundary axiom of
`zap.NewNop`, which no `Link.lean` links yet. `etc/gen-link.py` has no
mode combining several packages' Links (each mode links one package, with `@` callees of the
Links it imports under one namespace); a `--compactkv` mode is the follow-up if more of the example
is linked. `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.StartCompactingServer
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.client.v3.WithRev

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]

/-- `StartCompactingServer`, over `newServer`'s compacting variant (`specCompact`) and `NewServer`'s
linked result (`wp_NewServer`: `NewServer.spec` in either compaction mode, M2's item 14). -/
theorem compactkv.wp_StartCompactingServer [go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] :
    common.StartCompactingServer.spec (GF := GF) (hG := hG) :=
  common.StartCompactingServer.wp_proof
    (common.newServer.wp_proofCompact common.features.wp_NewDefaultServerFeatureGate
      wp_NewServer)
    EtcdServer.wp_Start

/-- **The adequacy example's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/compactkv/Main.lean`), under the semantic premises of
its callees' linked results: `int64(f)` of a `float64` (`Float64ToInt64Semantics`, the server's)
and the client's `dialWithBalancer` body (`DialWithBalancerBody`). -/
theorem compactkv.wp_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    compactkv.Main.spec (GF := GF) (hG := hG) :=
  compactkv.Main.wp_proof zap.NewNop.wp_proof compactkv.wp_StartCompactingServer common.wp_Serve
    common.wp_NewClient context.wp_Background context.WithTimeoutBackground.wp_proof
    context.wp_ErrAny WithRev.wp_proof

end results


end EtcdGrove
end Perennial
