/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: the members' vocabulary (plan item 4, `notes/putget-dist-plan.md` §13)

What `Member.spec` (`Spec/.../examples/etcd/dist/putgetk/Member.lean`) is written in, beside the cluster's
start (`etcd_dist.etcdClusterStart`, `dist/ClusterStart.lean`) and the in-process `putgetN`'s audited
per-member premises (`etcdstart.bootPremise` at `etcd_putgetN.dirN` and `etcdstart.urlsN`):
* `nameOf j`: member `j`'s name as `putgetk.Name(j)` computes it;
* `cmsOf ms ids`: the start's members (`etcd_dist.ClusterMember`: peer address, client address, member id)
  from the deployment's members and their ids, in the members' order;
* `kvAgree ρ γk`: what `memberBoot_of_slice` says of the member's request names `ρ` against the cluster's
  KV names;
* `memberPubOkK γk Pub`: the member's publication obligation: its view, at any request names agreeing
  with the cluster's KV names, satisfies `Pub` (the start's to provide, as putget's `memberPubOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClusterStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

/-- **Member `j`'s name**, as `putgetk.Name(j)` computes it: `"putgetk-"` and `j` in decimal. -/
def nameOf [GooseExts] (j : Nat) : GoString := go!"putgetk-" ++ fmtUint (W64 j) (W64 10)

/-- **The start's members** (`etcd_dist.ClusterMember`) of the deployment's members `ms` with the ids `ids`,
in the members' order. -/
def cmsOf [GooseExts] (ms : List GMember) (ids : List w64) : List etcd_dist.ClusterMember :=
  (ms.zip ids).map (fun p => ⟨p.1.Peer', p.1.Client', p.2⟩)

/-- **The member's request names agree with the cluster's KV names** (`memberBoot_of_slice`'s pure post). -/
def kvAgree [GooseExts] (ρ : ReqNames) (γk : KVNames) : Prop :=
  ρ.rd.kv.st = γk.st ∧ ρ.rd.kv.c0 = γk.c0 ∧ ρ.rd.kv.ch0 = γk.ch0 ∧ ρ.rd.kv.log0 = γk.log0 ∧
    kvSame ρ.rd.kv γk

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- **The member's publication obligation** (persistent): its view, at any request names agreeing with the
cluster's KV names `γk`, satisfies `Pub` (`etcd_dist.memberView`; the start's to provide: putget's
`memberPubOk`, with the client's invariant allocated by the start, not the member, now that the KV state
is the cluster's). -/
def memberPubOkK (γk : KVNames) (Pub : etcd_dist.EnvView → IProp GF) : IProp GF :=
  iprop(□ ∀ ρ : ReqNames, ⌜kvAgree ρ γk⌝ -∗ Pub (etcd_dist.memberView ρ))

instance memberPubOkK_persistent (γk : KVNames) (Pub : etcd_dist.EnvView → IProp GF) :
    Persistent (memberPubOkK γk Pub) := by
  unfold memberPubOkK; infer_instance

end defs

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
