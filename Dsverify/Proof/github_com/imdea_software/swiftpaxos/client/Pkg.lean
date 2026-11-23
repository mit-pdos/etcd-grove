/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Pkg.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client package's package-level state (L2, notes/prove-s2-e.md, decision D90 R-E1; the run's
choice for `SwiftNetPkgState.client`): the package's `nodeGhost` (made at the package's
initialization on every node, fork e968d22) is `g`, its prophecy `p`. The node's right to claim
it once, `client.ghostFresh` (its prophecy's ownership and its mutex at its zero value), is
handed out in one of two ways:

* on a replica node (`swift.replicaNode netIp`), by the client package's first initialization to
  the node's boot thread (InitFirst's `Q`, decision D9 (a'); `client.freshAt`,
  Proof/swiftnet/SrvInit.lean), the package state keeping nothing;
* on any other node, by an invariant holding it until the node's own address `netIp:7000`'s
  token (`client.keyAddr`, exclusive, held only by a client node's share, which does not use it
  otherwise) takes it (`client.ghostFresh_take`, Proof/client/Claim.lean); a second taking
  needs a second token.
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

/-- The node's own first address, `ip:7000` (a client node's `clientNodeAddrs` entry). -/
def client.keyAddr (ip : GoString) : GoString := ip ++ go!":7000"

open Classical in
/-- **The client package's state** (see the file header): off a replica node, the package's
`nodeGhost` is `g` (not nil), its prophecy `p`, and `g` is unclaimed or its claim was taken with
the node's address token. -/
def client.pkgSt : IProp GF :=
  if swift.replicaNode (netIp (L := hG.goose_localGS) (GF := GF)) then iprop(True)
  else iprop(∃ (g : Loc) (p : proph_id), globalAddr client.nodeGhost ↦□ g ∗ ⌜g ≠ null⌝ ∗
    structFieldRef client.Ghost go!"p" g ↦□ p ∗
    inv client.ghostInitN iprop(client.ghostUnclaimed g p ∨
      addrTokG (extGlobalGS netExt (hlc := .hasLC))
        (client.keyAddr (netIp (L := hG.goose_localGS) (GF := GF)))))

instance client.pkgSt_persistent : Persistent (client.pkgSt (GF := GF)) := by
  unfold client.pkgSt; split <;> infer_instance

end defs

section fresh
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

open Classical in
/-- What the client package's first initialization hands to a node's boot thread: on a replica
node, the node's right to claim its ghost (see the file header). -/
def client.freshAt (ip : GoString) : IProp netDistGF :=
  if swift.replicaNode ip then client.ghostFresh else iprop(True)

end fresh

/-- An address token is unique. -/
theorem client.addrTokG_excl {GF : BundledGFunctors} (hN : NetConnGS GF) (a : GoString) :
    addrTokG hN a ∗ addrTokG hN a ⊢ (iprop(False) : IProp GF) := by
  unfold addrTokG
  letI := hN.allG
  iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
  iapply token_exclusive $$ H1 H2

end Perennial.github_com.imdea_software.swiftpaxos
