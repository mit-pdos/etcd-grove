/-
# `github.com/xiang90/probing`: the trust boundary (batch 4b)

probing is translated types and names only: **assumed**, true of its code at the pin. rafthttp
keeps two probers (`Transport.pipelineProber`, `streamProber`: `NewProber(rt)`), adds each peer
(`addPeerToProber`: `AddHTTP(id, interval, urls)`, which starts a goroutine sending `GET` probes to
`<url>/raft/probing` through `rt` every interval, and `Status(id)`, read by a monitor goroutine that
only logs and records metrics), removes them (`Remove`, `RemoveAll`), and serves the probes
(`NewHandler()`: a JSON health reply).

* `proberOk p` (transparent, persistent: an interface value's bundle): `p` is a `Prober` whose
  `AddHTTP`, `Remove` and `RemoveAll` return (`AddHTTP`, `Remove`: some error). The prober takes
  its mutex: safe for concurrent use. `AddHTTP(id, interval, urls)` needs a positive interval
  (`time.NewTicker` panics otherwise), a non-empty list (its goroutine indexes `urls[pinned]` and
  takes `% len`), every URL parsing (`http.NewRequest`'s error is a `panic` in that goroutine), and
  the slice read-only for good (the goroutine reads it while the target lives): its premises;
  rafthttp meets them (`nonissues/probing-addhttp-preconditions.md`).
* `urlParses u` (opaque, pure): `http.NewRequest("GET", u, nil)` succeeds (`url.Parse` accepts `u`).
  rafthttp's probing URLs are a parsed peer URL followed by `/raft/probing`: a law of 2f's
  (`req/net_http.md`).

**The probes and the HTTP boundary's closed world.** The probing goroutines are not among the
program's threads, and their `GET`s are requests the program's clients did not prove anything of.
A handler that receives one learns nothing beyond what the protocol allows of every request on the
probing path: the protocol of a peer address (2f's `raftProto`) must allow any `GET /raft/probing`
with any knowledge (it does: the probing handler answers anything), which is the condition under
which `AddHTTP`'s triple is true. That is 2f's to state on its protocol (`req/net_http.md`).

Users: `rafthttp/transport.go:146-147,166,221-222,349-350,385-387`, `probing_status.go:41-57`.
Snippet: `examples/specreq/pkgleaves/leaves.go` (`ReqProberLifecycle`).
-/
module

public import GeneratedProof.github_com.xiang90.probing
public import Spec.PkgInit.github_com.xiang90.probing
public import Spec.net.http.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Probing

open Iris Iris.BI

/-- **`http.NewRequest("GET", u, nil)` succeeds** (opaque, pure; see the header). -/
opaque urlParses : GoString → Prop

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A prober** (persistent bundle; see the header). -/
def proberOk (p : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜p = GoInterface.ok i⌝ ∗
    (□ ∀ (id : GoString) (interval : w64) (urls : GoSlice) (us : List GoString)
        (Φ : val → IProp GF),
      ⌜0 < sint.Z interval ∧ us ≠ [] ∧ ∀ u ∈ us, urlParses u⌝ -∗ urls ↦*□ us -∗
      ▷ (∀ e : GoInterface, Φ #e) -∗
      WP (App (App (App (Val #(methods i.ty go!"AddHTTP" i.v)) (Val #id)) (Val #interval))
        (Val #urls)) {{ Φ }}) ∗
    (□ ∀ (id : GoString) (Φ : val → IProp GF), ▷ (∀ e : GoInterface, Φ #e) -∗
      WP (App (Val #(methods i.ty go!"Remove" i.v)) (Val #id)) {{ Φ }}) ∗
    (□ ∀ Φ : val → IProp GF, ▷ Φ #() -∗
      WP (App (Val #(methods i.ty go!"RemoveAll" i.v)) (Val #())) {{ Φ }}))

end vocab

end Probing
end EtcdGrove
end Perennial
