/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/Ghost.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2's node ghost (notes/l2-design.md §5, notes/prove-s2-e.md; the fork's client/ghost.go): every
node's `client.Ghost` (a mutex and a prophecy, the client package's `nodeGhost`, made at the
package's initialization). Its prophecy's values decode to the node's predicted events
(`decodeV`, over Spec/swift/L2Words.lean's `decodeP`). Once claimed for the predicted node `n`
(`client.claimGhost.spec`, Spec/client/NodeGhost.lean), the mutex guards `client.nodeLockR`: the
prophecy and the node's half of its future words in `sp.inv` (`γ.pred`), which agree. The
node's handle on it is `client.nodeGhostB` (the body of `client.nodeGhostOk`).

Stage 1's node-wide history ghost (`lockR`, `LockOk`, `ghostR`, `ghostOk`) is gone.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Perennial.Proof.github_com.goose_lang.primitive.Link

-- PORT: lab imports dropped: Harness.Proof.bufio.Net, Harness.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

section vals
variable [GoGlobalContext] [go.IntoValInj w64]

/-- A prophecy value's word (`#w`; anything else: 0, never a well-formed event's start). -/
noncomputable def valW (v : val) : w64 :=
  if h : ∃ w : w64, v = #w then Classical.choose h else 0

/-- The predicted events of a prophecy's values. -/
noncomputable def decodeV (vs : List val) : List PEv := decodeP (vs.map valW)

/-- An event's resolutions, as the prophecy's values. -/
def encV (e : PEv) : List val := (encP e).map (fun w => #w)

end vals

end sp

namespace client

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- **The node's ghost lock's resource** once claimed for the predicted node `n`: the prophecy
`p`'s values and the node's half of its future words in `sp.inv`, the same. -/
def nodeLockR (γ : sp.Names) (n : sp.PNode) (p : proph_id) : IProp netDistGF :=
  iprop(∃ pvs : List val, proph p pvs ∗
    ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) (pvs.map sp.valW))

/-- The ghost `g` is claimed for `n`: its prophecy `p`, its mutex guarding `nodeLockR`. -/
def isNodeGhost (γ : sp.Names) (n : sp.PNode) (g : Loc) : IProp netDistGF :=
  iprop(∃ p : proph_id, ⌜g ≠ null⌝ ∗ structFieldRef client.Ghost go!"p" g ↦□ p ∗
    sync.isMutex (structFieldRef client.Ghost go!"mu" g) (nodeLockR γ n p))

instance isNodeGhost_persistent γ n g : Persistent (isNodeGhost γ n g) := by
  unfold isNodeGhost; infer_instance

/-- **This node's ghost is claimed for `n`** (the body of `client.nodeGhostOk`): `n` is
registered, and the package's `nodeGhost` is a ghost claimed for `n`. -/
def nodeGhostB (γ : sp.Names) (n : sp.PNode) : IProp netDistGF :=
  iprop(sp.predReg γ n ∗ ∃ g : Loc, globalAddr client.nodeGhost ↦□ g ∗ isNodeGhost γ n g)

instance nodeGhostB_persistent γ n : Persistent (nodeGhostB γ n) := by
  unfold nodeGhostB; infer_instance

/-- **This node's ghost, unclaimed** (heap-local, exclusive): the package's `nodeGhost` is `g`,
its prophecy `p` with its values, its mutex at its zero value. -/
def ghostFresh : IProp netDistGF :=
  iprop(∃ (g : Loc) (p : proph_id) (pvs : List val), globalAddr client.nodeGhost ↦□ g ∗
    ⌜g ≠ null⌝ ∗ structFieldRef client.Ghost go!"p" g ↦□ p ∗ proph p pvs ∗
    structFieldRef client.Ghost go!"mu" g ↦ (zero_val sync.Mutex))

end defs

end client

end Perennial.github_com.imdea_software.swiftpaxos

end
