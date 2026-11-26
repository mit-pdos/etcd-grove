/-
`RequestVia(dial, addr, kind, timeout, total, payload)` (`examples/raft/kvraft/client.go`): dials
`addr` with `dial` (once), writes `helloClient` then the request frame (`putB (reqBytes kind
timeout payload)`), reads one frame, and answers its body after a first byte `1`; the connection is
closed on the way out (`defer c.Close()`) and by a timer after `total` (`closeAfter`, disarmed on
the way out). At the byte level, as the frame specs: the caller's dialer, called once, gives either
an error with `Fl`, or a connection end with `connRes cn s T W Rd` (`T` the request's stream) (`Client.lean`: nothing written or
read yet, the caller's write, read and close accessors); the post says what the call wrote and read
on it. On `(b, true)`: it wrote `helloClient :: putB req` and read `putB (1 :: b')`, `b` holding `b'`.
On `false`: the dial failed (`Fl`), or what it wrote and read so far.

The payload's length is below `2^63 - 17` (the request frame's length, `8 + 1 + 8 + len(payload)`,
is a Go `int`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev RequestVia.spec : Prop :=
  ∀ (dial : GoFunc) (addr : GoString) (kind : w8) (tmo total : _root_.Perennial.time.Duration)
    (payload : GoSlice) (pl : List w8) (dqp : DFrac) (W Rd : Nat → Bool → List w8 → IProp GF)
    (Fl : IProp GF) (eof ed : GoInterface),
  (pl.length : Int) + 17 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      payload ↦*{dqp} pl ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (∀ (d : _root_.Perennial.time.Duration) (Φ : val → IProp GF),
        (∀ (c err : GoInterface),
          ((⌜err = interface.nil⌝ ∗ ∃ (cn : Nat) (s : Bool) (a : GoString),
              net.isConn (GF := GF) c cn s a ∗
                connRes cn s (helloClientB :: putB (reqBytes kind tmo pl)) W Rd) ∨
            (⌜err ≠ interface.nil⌝ ∗ Fl)) -∗ Φ (PairV #c #err)) -∗
        WP (App (App (Val #dial) (Val #addr)) (Val #d)) {{ Φ }}) }}
    (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RequestVia))
      (Val #dial)) (Val #addr)) (Val #kind)) (Val #tmo)) (Val #total)) (Val #payload))
  {{ (b : GoSlice) (ok : Bool), RET (PairV #b #ok); payload ↦*{dqp} pl ∗
      ((⌜ok = true⌝ ∗ ∃ (b' : List w8) (cn : Nat) (s : Bool), b ↦* b' ∗
          W cn s (helloClientB :: putB (reqBytes kind tmo pl)) ∗ Rd cn s (putB (W8 1 :: b'))) ∨
        (⌜ok = false⌝ ∗ (Fl ∨ ∃ (cn : Nat) (s : Bool) (w got : List w8), W cn s w ∗ Rd cn s got))) }}

end spec

end kvraft
end EtcdGrove
end Perennial
