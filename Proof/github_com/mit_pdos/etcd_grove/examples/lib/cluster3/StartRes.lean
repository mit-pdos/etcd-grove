/- Lean-first (no Rocq counterpart).

# The cluster's start bundle (hub plan step 7's E2 and D1, 2026-11-05)

`startRes cfg` (sealed, `@[no_expose]`; `etc/import-all.txt`): what a three-member cluster's start
(`StartCluster`) takes of program start's resources, for the cluster's configuration `cfg`: each
member's start bundle (`etcdstart.memberStartRes`, at its name, its peer address and its client
address) and the right to listen on each bridge's address (`netAddrFree`; the bridges are no
member's resource).

**The laws.** The introduction from the members' bundles and the bridges' tokens in list form
(`startRes_intro`, at `members cfg` and `bridges cfg`: what `etcd_adequate_members` gives an
example's closed theorem), and the unfolding into what `StartCluster` takes
(`startRes_members`: the three members' bundles, for `etcdstart.alloc3`, and the three bridges'
listen rights, for `StartBridge`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode

section startRes
variable [GooseExts] {GF : BundledGFunctors}

/-- **The cluster's members**: each member's name and the addresses the program listens on for it
(its peer address and its client address). -/
def members (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) :
    List (GoString × etcdstart.MemberAddrs) :=
  [(cfg.Name1', ⟨some cfg.Peer1', some cfg.Client1'⟩),
    (cfg.Name2', ⟨some cfg.Peer2', some cfg.Client2'⟩),
    (cfg.Name3', ⟨some cfg.Peer3', some cfg.Client3'⟩)]

/-- **What a three-member cluster's start takes** (see the file header). -/
@[no_expose] def startRes (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) :
    IProp GF :=
  iprop(etcdstart.memberStartRes cfg.Name1' ⟨some cfg.Peer1', some cfg.Client1'⟩ ∗
    etcdstart.memberStartRes cfg.Name2' ⟨some cfg.Peer2', some cfg.Client2'⟩ ∗
    etcdstart.memberStartRes cfg.Name3' ⟨some cfg.Peer3', some cfg.Client3'⟩ ∗
    netAddrFree cfg.Bridge1' ∗ netAddrFree cfg.Bridge2' ∗ netAddrFree cfg.Bridge3')

/-- **The cluster's start bundle, from the members' bundles and the bridges' listen rights** (what
`etcd_adequate_members` gives at `members cfg` and `bridges cfg`). -/
theorem startRes_intro (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) :
    ([∗list] m ∈ members cfg, etcdstart.memberStartRes (GF := GF) m.1 m.2) ∗
        ([∗list] b ∈ bridges cfg, netAddrFree (GF := GF) b) ⊢
      startRes cfg := by
  unfold startRes members bridges
  iintro ⟨⟨H₁, H₂, H₃, -⟩, ⟨Hb₁, Hb₂, Hb₃, -⟩⟩
  iframe

/-- **What `StartCluster` takes of the cluster's start bundle**: the three members' start bundles
(to `etcdstart.alloc3`) and the three bridges' listen rights (to `StartBridge`). -/
theorem startRes_members (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) :
    startRes (GF := GF) cfg ⊢
      (etcdstart.memberStartRes cfg.Name1' ⟨some cfg.Peer1', some cfg.Client1'⟩ ∗
        etcdstart.memberStartRes cfg.Name2' ⟨some cfg.Peer2', some cfg.Client2'⟩ ∗
        etcdstart.memberStartRes cfg.Name3' ⟨some cfg.Peer3', some cfg.Client3'⟩) ∗
      (netAddrFree cfg.Bridge1' ∗ netAddrFree cfg.Bridge2' ∗ netAddrFree cfg.Bridge3') := by
  unfold startRes
  iintro ⟨H₁, H₂, H₃, Hb₁, Hb₂, Hb₃⟩
  iframe

end startRes

end cluster3
end EtcdGrove
end Perennial
