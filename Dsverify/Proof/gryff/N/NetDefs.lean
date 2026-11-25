/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/NetDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the network resources of a replica (bodies of `Replica2/State.lean`'s slots)

* `peerWriterB γ k q w ms` (`peerWriterAt`'s body): replica id `k`'s `*bufio.Writer` `w` of its
  connection with peer `q` has been handed the encodings `W` of `ms` (`msgsWire`), after the
  connection's header `hdr` (the dialer's handshake, or nothing for the acceptor): what it has
  sent and buffered (`sent ++ pend`) is a prefix of `hdr ++ W`, all of it sent when the writer is
  healthy (a failed writer accepts nothing more: its error is sticky). The writer's protocol
  `Q` allows `hdr` followed by any bytes of `k`'s stream to `q` (`peerStreamOk`), and `k`'s
  prediction is known (what `peerStream_send` needs).
* `clientWriterB γ hs w`: the acceptor's `*bufio.Writer` `w` of client `hs`'s connection has been
  handed whole replies `X` (`msgsOk (clientReplyOk γ hs) X`), sent when healthy; its protocol
  allows any whole replies.
* `statsOkB st`: a `*stats.StatsMap` (its mutex, with the map under it).
-/
module

public import Dsverify.Proof.gryff.Proto2.Replica
public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.Proof.gryff.src.stats.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg)

attribute [local instance] GooseGlobalGS.gooseInvGS

section net
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics]

/-- `peerWriterAt`'s body: see the module header. -/
def peerWriterB (γ : GryffNames GF) (k q : Fin 3) (w : Loc) (ms : List Msg) : IProp GF :=
  iprop(∃ (wr : wire.WSt GF) (J Q : List w8 → IProp GF) (hdr W sent pend : List w8)
      (err : GoInterface),
    wire.writerOk wr J Q ∗ wire.ownWriter w wr J Q sent pend err ∗
    ⌜msgsWire ms W ∧ sent ++ pend <+: hdr ++ W ∧
      (err = interface.nil → pend = [] ∧ sent = hdr ++ W)⌝ ∗
    □ (∀ X, peerStreamOk γ.proto k q X -∗ □ Q (hdr ++ X)) ∗ (∃ ws, predIdIs γ.proto k ws))

/-- A client connection's writer: see the module header. -/
def clientWriterB (γ : GryffNames GF) (hs : w32) (w : Loc) : IProp GF :=
  iprop(∃ (wr : wire.WSt GF) (J Q : List w8 → IProp GF) (X sent pend : List w8)
      (err : GoInterface),
    wire.writerOk wr J Q ∗ wire.ownWriter w wr J Q sent pend err ∗
    ⌜sent ++ pend <+: X ∧ (err = interface.nil → pend = [] ∧ sent = X)⌝ ∗
    □ msgsOk (clientReplyOk γ hs) X ∗
    □ (∀ Y, msgsOk (clientReplyOk γ hs) Y -∗ □ Q Y))

/-- The `StatsMap` keys `IncrementStrInt` uses (the coordinator's); every other key holds an
`int` (`Max`, `Add`, `Increment`). -/
def strIntKeys : List GoString :=
  [go!"read_1_quorum", go!"read_2_sent", go!"read_2_quorum", go!"write_1_quorum",
    go!"write_2_sent", go!"write_2_quorum"]

/-- A value of a `StatsMap` at key `k`: a `map[string]int` for `strIntKeys`, an `int` otherwise. -/
def statValB (k : GoString) (v : GoInterface) : IProp GF :=
  if k ∈ strIntKeys then
    iprop(∃ cm : Loc, ⌜v = interface.mkOk (go.GoType.MapType go.string go.int) #cm⌝ ∗
      ∃ CM : GMap GoString w64, cm ↦$ CM)
  else iprop(⌜∃ n : w64, v = interface.mkOk go.int #n⌝)

/-- `statsOk`'s body: a `*stats.StatsMap`, its mutex guarding its map. -/
def statsOkB (st : Loc) : IProp GF :=
  iprop(□ ∃ sm : src.stats.StatsMap, st ↦□ sm ∗
    sync.isMutex sm.mtx' iprop(∃ M : GMap GoString GoInterface, sm.stats' ↦$ M ∗
      [∗map] k ↦ v ∈ M, statValB k v))

/-- The namespace of the client writers' escrow (`genericOk`). -/
def escrowN : Namespace := ndot nroot "gryff_client_writers"

end net

end Perennial.gryff.netN
