/- Lean-first (no Rocq counterpart).

# PLACEHOLDER: phase 7 S5's names, for `etcd_safe_nocrash`'s skeleton (`notes/etcd-dist-plan.md`, D9)

**Not S5's definitions.** A deployment of `k > 1` members needs rafthttp across machines: each member's raft
handler served by Go's `http.Server.Serve` on its peer listener, and the other members' round trips to it.
S5 (phase 7, net/http over the net extension: proving session 2's server half, the client half) is to give
that; until its names are agreed (on #24/#18, before any field is fixed), this module carries the fields the
start needs as one structure, `S5Draft`, which the skeleton takes as a hypothesis (`S5Holds`), adding no
axiom and no `opaque`:
* `httpAddrAt a`: the peer address `a` serves rafthttp's protocol for the deployment's cluster (persistent,
  global ghost state: no heap), the counterpart of S2's `grpcAddrAt`;
* `http_addr_set`: the start law, spending `addrUnset a` (the net library's), which replaces the
  single-process `http.reserve` from `httpProtoFree` (whose only source is the one-process start axiom; since
  2026-11-25 `http.reserve` spends the address's pending set too, so the two are exclusive per address).
To be added with S5's agreement: the member's side (`Serve_s5`: the raft handler served at a peer address
set by `http_addr_set`) and the peers' round trips over it. When S5 lands, each field becomes its
definition or theorem and the structure goes.
-/
module

public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **PLACEHOLDER for phase 7 S5's names** (see the file header), at a global ghost state `G` with the net
protocol library's names `π`. -/
structure S5Draft (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [GoGlobalContext] [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS] where
  /-- The peer address `a` serves rafthttp's protocol for the deployment's cluster (persistent). -/
  httpAddrAt : GoString → IProp GF
  httpAddrAt_persistent : ∀ a, Persistent (httpAddrAt a)
  /-- The start law, spending `addrUnset a`. -/
  http_addr_set : ∀ (E : CoPset) (a : GoString), ⊢ regCtx -∗ addrUnset a ={E}=∗ httpAddrAt a

attribute [instance] S5Draft.httpAddrAt_persistent

/-- **S5's names hold** (what S5 proves, at every global ghost state and net protocol names). -/
def S5Holds (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [GoGlobalContext] : Prop :=
  ∀ [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS], Nonempty (S5Draft GF)

end etcd_dist
end EtcdGrove
end Perennial

end
