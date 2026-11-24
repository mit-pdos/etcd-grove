/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/Ghost.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2's node prophecies (notes/l2-design.md §5, notes/prove-s2-e.md; notes/proph-swiftpaxos.md): the
prophecy patch's `nodeProph` of the client package (a client node's events) and of the swift package (a
replica node's), each made by its package's prophecy-only initializer. Each event resolves its node's
prophecy once (`Resolve(any)`), with `sp.encE e`: the string of the event's words (`sp.encP e`, each word
as its ten 7-bit chunks, `sp.strW1`). The prophecy's values, as words (`sp.valWs`), decode to the node's
predicted events (Spec/swift/L2Words.lean's `decodeP`). Once claimed for the predicted node `n`
(`client.claimGhost.spec`, Spec/client/NodeGhost.lean), an invariant holds `client.nodeLockR`: the
prophecy and the node's half of its future words in `sp.inv` (`γ.pred`), which agree. The node's handle
on it is `client.nodeGhostB` (the body of `client.nodeGhostOk`).

Stage 1's node-wide history ghost (`lockR`, `LockOk`, `ghostR`, `ghostOk`) is gone, and so is the
fork's ghost mutex (one resolution per event is atomic).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Perennial.Proof.github_com.mit_pdos.perennial.proph.Link

-- PORT: lab imports dropped: Harness.Proof.bufio.Net, Harness.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

section vals
variable [GoGlobalContext]

/-- A word's string (the patch's `s += string(byte(w&127)) + string(byte(w>>7&127)) + ... +
string(byte(w>>63&127))`): its ten 7-bit chunks, from the lowest, each a byte below 128 (so
`string(byte(.))` is that one byte). -/
def strW1 (w : w64) : List w8 :=
  [0, 7, 14, 21, 28, 35, 42, 49, 56, 63].map (fun n : Nat => W8 ((w.toNat / 2 ^ n % 128 : Nat) : Int))

/-- Words' string. -/
def strW (ws : List w64) : List w8 := ws.flatMap strW1

/-- **An event's prophecy value**: the string of its words, as the `any` `Resolve` gets. -/
noncomputable def encE (e : PEv) : val := #(interface.mkOk go.string #(strW (encP e)))

open Classical in
/-- A prophecy value's words: a well-formed event's words if it is that event's value, else `[0]`
(0 starts no event, so `decodeP` stops there). -/
noncomputable def valWs (v : val) : List w64 :=
  if h : ∃ e, PEvWf e ∧ v = encE e then encP (Classical.choose h) else [W64 0]

end vals

end sp

namespace client

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- The package variable holding the prophecy of a node of `n`'s kind (the prophecy patch's
`nodeProph`): the client package's for a client node, the swift package's for a replica node. -/
def nodeVar : sp.PNode → GoString
  | .cl _ => client.nodeProph
  | .rep _ => swift.nodeProph

/-- **The node prophecy's invariant's resource** once claimed for the predicted node `n`: the
prophecy `p`'s values, as words, are the node's half of its future words in `sp.inv`. -/
def nodeLockR (γ : sp.Names) (n : sp.PNode) (p : proph_id) : IProp netDistGF :=
  iprop(∃ pvs : List val, proph p pvs ∗
    ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) (pvs.flatMap sp.valWs))

/-- **This node's prophecy is claimed for `n`** (the body of `client.nodeGhostOk`): `n` is
registered, and the package variable `nodeVar n` holds a prophecy `p` whose invariant holds
`nodeLockR γ n p`. -/
def nodeGhostB (γ : sp.Names) (n : sp.PNode) : IProp netDistGF :=
  iprop(sp.predReg γ n ∗ ∃ p : proph_id, globalAddr (nodeVar n) ↦□ p ∗
    inv nodeProphN (nodeLockR γ n p))

instance nodeGhostB_persistent γ n : Persistent (nodeGhostB γ n) := by
  unfold nodeGhostB; infer_instance

/-- **A package's node prophecy, unclaimed** (heap-local, exclusive): the package variable `x`
holds a prophecy `p`, with its values. -/
def prophFresh (x : GoString) : IProp netDistGF :=
  iprop(∃ (p : proph_id) (pvs : List val), globalAddr x ↦□ p ∗ proph p pvs)

/-- The client package's node prophecy, unclaimed (a client node claims it). -/
def ghostFresh : IProp netDistGF := prophFresh client.nodeProph

/-- The prophecy a node of `n`'s kind claims, unclaimed. -/
def freshOf (n : sp.PNode) : IProp netDistGF := prophFresh (nodeVar n)

end defs

end client

end Perennial.github_com.imdea_software.swiftpaxos

end
