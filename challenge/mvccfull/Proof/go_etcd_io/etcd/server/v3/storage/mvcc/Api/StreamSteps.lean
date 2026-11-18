/-
**The API part of a stream's channel invariant and its steps** (stage 2 of the mvcc API proof,
the watch chain: `notes/mvcc-api-invariants.md`, "Hand-off: stage 2, the watch chain", item 1;
2026-11-05). Lean-first (no Rocq counterpart).

`chanApiAt ι l dec recv`: the history's authority at `l` (well formed, decoded by `dec`), its
filters' saved names and its sends' bounds, the channel invariant's half of the consumer's view
(`recv`, a prefix of the sends), and a lower bound of the client's event count. The channel
invariant (`watchChanInv`) is to hold it with its sent list projecting to `sendsOf l`.

The steps, each what a frozen contract's post needs of the stream's ghost state:
- `chanApi_alloc` (`NewWatchStream`): a new stream's names, `wsState ι wsStart`, `wsRecv ι []`;
- `chanApiAt_send` (every send): a send's event appended, its premises (`stepOk`) proved by the
  sender;
- `chanApiAt_reg` (`Watch`'s update): the registration at the exact sent count, the client's
  `wsState` moved to `S.register id ⟨rg, fs, lo, k, true⟩` with `wsSentLb ι k`;
- `chanApiAt_cancel` (`Cancel`'s update): `wsState ι (S.cancel id)`;
- a receive: `WatchRecv.chanApi_recv` (the channel's received prefix moves with it);
- `chanApiAt_sentLb` (the non-blocking receive's empty case): `wsSentLb ι n` is at most the sends.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamGhost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc sent

/-! ## Well-formedness depends on the decoding only at the history's names -/

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- **The API part of a stream's channel invariant** (see the file header). -/
def chanApiAt (ι : WsAbs) (l : List SEv) (dec : GName → List (EvM → Bool)) (recv : List WResp) :
    IProp GF :=
  iprop(monoListAuthOwn ι.ev 1 l ∗ ⌜LogWF dec l ∧ recv <+: sendsOf l⌝ ∗
    ([∗list] fg ∈ fgsOf l, savedFilters fg (dec fg)) ∗ ([∗list] e ∈ l, evTok ι.st e) ∗
    ghostVar ι.rcv (1 : Qp).half recv ∗ monoNatLbOwn ι.ns (nsCount l))

/-! ## The senders' tokens -/

end ghost

end api
end mvcc
end EtcdGrove
end Perennial
