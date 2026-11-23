/-
The lab's `net` vocabulary the replica's and the master's transport specs name (dsverify-lab
`harness/lean/Harness/Proof/net/Base.lean`, `GooseLang/Ext/NetConn/Specs.lean`), restated over
`Net/`'s (`Net/Proof/net/Base.lean`, `GooseLang/Ext/Net/Proto.lean`):

* `net.ownListener l lid a` (persistent): the `*TCPListener` `l` is this node's listener `lid`, shared
  between threads at `a` (`lisAt` and `lisInv`, what `accept_shared_au` takes; the lab's persistent
  listener).
* `nodeIp ip`: the lab's node-IP fact (its harness gave each node an IP and wildcard `Listen`s took
  it). **Port change**: `Net/` has no node IP (any machine may listen at any valid address, D6,
  D20, D21; every node here is on loopback), so it is `True`; what the lab derived from it (the
  address a wildcard listener serves) is the wildcard-listen hypothesis's (notes/dsv-swiftpaxos.md,
  "Wildcard `Listen`").
-/
module

public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- See the file header. -/
def net.ownListener (l : Loc) (lid : w64) (a : GoString) : IProp GF :=
  iprop(∃ x : GoInterface, net.lisAt l lid x ∗
    lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) lid a)

instance net.ownListener_persistent (l : Loc) (lid : w64) (a : GoString) :
    Persistent (net.ownListener (GF := GF) l lid a) := by
  unfold net.ownListener; infer_instance

/-- See the file header. -/
def nodeIp (_ip : GoString) : IProp GF := iprop(True)

instance nodeIp_persistent (ip : GoString) : Persistent (nodeIp (GF := GF) ip) := by
  unfold nodeIp; infer_instance

theorem nodeIp_intro (ip : GoString) : ⊢ nodeIp (GF := GF) ip := by
  unfold nodeIp; iintro; ipureintro; trivial

end defs

end Perennial
