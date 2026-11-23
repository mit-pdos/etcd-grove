/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Pkg.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client package's package-level state (L2, notes/prove-s2-e.md, decision D90 R-E1; the run's
choice for `SwiftNetPkgState.client`): the package's `nodeGhost` (made at the package's
initialization on every node, fork e968d22) is `g`, its prophecy `p`. The node's right to claim
it once, `client.ghostFresh` (its prophecy's ownership and its mutex at its zero value), is
handed out in one of two ways:

* in the lab: on a replica node, by the package's first initialization to the node's boot thread;
  on any other node, by an invariant holding it until the node's own address token (exclusive in
  the lab's model) took it.

**Port change** (notes/dsv-swiftpaxos.md): `Net/` has no node IP and its address tokens are
persistent, so neither the node test nor the exclusive token exists. On every node the package's
first initialization hands `client.ghostFresh` to the boot thread (`client.freshAt`), and the
package state keeps nothing (`client.pkgSt := True`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Ghost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Pkg

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The node ghost's claim invariant's namespace. -/
def client.ghostInitN : Namespace := ndot nroot "swiftpaxos.client.ghostInit"

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The node ghost `g`, unclaimed: its prophecy `p`'s ownership, its mutex at its zero value. -/
def client.ghostUnclaimed (g : Loc) (p : proph_id) : IProp GF :=
  iprop(∃ pvs : List val, proph p pvs ∗
    structFieldRef client.Ghost go!"mu" g ↦ (zero_val sync.Mutex))

/-- **The client package's state** (see the file header): nothing. -/
def client.pkgSt : IProp GF := iprop(True)

instance client.pkgSt_persistent : Persistent (client.pkgSt (GF := GF)) := by
  unfold client.pkgSt; infer_instance

end defs

section fresh
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- What the client package's first initialization hands to a node's boot thread: the node's
right to claim its ghost (see the file header). -/
def client.freshAt (_ip : GoString) : IProp netDistGF := client.ghostFresh

end fresh

end Perennial.github_com.imdea_software.swiftpaxos
