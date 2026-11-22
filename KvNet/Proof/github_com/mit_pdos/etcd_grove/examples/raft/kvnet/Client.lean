/-
The vocabulary of kvnet's client request path (`examples/raft/kvnet/client.go`: `RequestVia`,
`RequestWithin`, `Request`), at the byte level, as the frame specs (`writeAll`, `writeFrame`,
`readFrame`, `closeAfter`): what a connection a client dialed carries for the caller's reasoning.

* `reqBytes kind timeout pl`: the request frame's body `RequestVia` writes: the kind (1 byte), the
  timeout in milliseconds (8 bytes, little-endian: Go's `uint64(timeout / time.Millisecond)`, a
  signed division), then the payload.
* `wAcc`, `rAcc`, `cAcc`: the caller's persistent accessors for the writes (`W w`: this call has
  written `w` on the connection), the reads (`Rd got`: it has read `got`) and the closes of the end
  `s` of the connection `cn` (the deferred `c.Close()` and `closeAfter`'s timer); the accessors open
  the end's and the direction's state (`netEnd`, `netDir`) for one call, as the frame specs' do.
* `connRes cn s T W Rd`: what a dialer gives with a connection, for a call that writes the stream
  `T`: nothing written or read, and the three accessors (the writes' within `T`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net

/-- The request frame's body: the kind, the timeout in milliseconds, the payload. -/
def reqBytes (kind : w8) (timeout : w64) (pl : List w8) : List w8 :=
  kind :: (u64Le (timeout.sdiv (W64 1000000)) ++ pl)

/-- The first byte of a client's connection (`helloClient`, `'C'`). -/
def helloClientB : w8 := W8 67

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The caller's accessor for the writes on the end `s` of `cn`: from `W w` (this call has written
`w`), one `Write` of `rs`, of which the first `k` bytes go through, for writes within the stream `T`
the call will write (`w ++ rs <+: T`: a protocol over the connection's bytes, `Proto.lean`'s
`write_acc`, only allows the bytes it means). -/
def wAcc (cn : Nat) (s : Bool) (T : List w8) (W : List w8 → IProp GF) : IProp GF :=
  iprop(□ (∀ (w rs : List w8), ⌜w ++ rs <+: T⌝ -∗ W w -∗
    |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
      netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
      ∀ k res d', ⌜WriteOutcome st d rs k res d'⌝ -∗
        netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ W (w ++ rs.take k)))

/-- The caller's accessor for the reads on the end `s` of `cn`: from `Rd got` (this call has read
`got`), one `Read` of at most `m` bytes. -/
def rAcc (cn : Nat) (s : Bool) (Rd : List w8 → IProp GF) : IProp GF :=
  iprop(□ (∀ (got : List w8) (m : Nat), Rd got -∗
    |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
      netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
      ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
        netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗ Rd (got ++ r.got)))

/-- The caller's accessor for a `Close` of the end `s` of `cn` (any number of them: the deferred
`c.Close()` and `closeAfter`'s timer may both close it). -/
def cAcc (cn : Nat) (s : Bool) : IProp GF :=
  iprop(□ (|={⊤,∅}=> ∃ st dd, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
      netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s dd ∗
      ∀ res st' d', ⌜CloseOutcome st dd res st' d'⌝ -∗
        netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ True))

instance wAcc_persistent (cn : Nat) (s : Bool) (T : List w8) (W : List w8 → IProp GF) :
    Persistent (wAcc cn s T W) := by unfold wAcc; infer_instance
instance rAcc_persistent (cn : Nat) (s : Bool) (Rd : List w8 → IProp GF) :
    Persistent (rAcc cn s Rd) := by unfold rAcc; infer_instance
instance cAcc_persistent (cn : Nat) (s : Bool) : Persistent (cAcc (GF := GF) cn s) := by
  unfold cAcc; infer_instance

/-- What a dialer gives with the end `s` of a new connection `cn`, for a call that will write the
stream `T`: nothing written or read, and the caller's accessors. -/
def connRes (cn : Nat) (s : Bool) (T : List w8) (W Rd : Nat → Bool → List w8 → IProp GF) : IProp GF :=
  iprop(W cn s [] ∗ Rd cn s [] ∗ wAcc cn s T (W cn s) ∗ rAcc cn s (Rd cn s) ∗ cAcc cn s)

end defs

end raft_kvnet
end EtcdGrove
end Perennial
