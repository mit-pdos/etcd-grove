/-
**What the leadership check reads of the server** (srvloops2, 2026-11-21): `ensureLeadership`
(`server.go`) reads the raft wrapper's latest tick under `tickMu`'s read lock (`isActive` →
`getLatestTickTs`), raft's status through the wrapper's node (`raftStatus` → `Node.Status()`), and
derives its read's context from `s.ctx` (`context.WithTimeout(s.ctx, …)`). `srvLeadCheckOk s` holds
those facts, persistent, in the reader's view of the server (`srvReadFieldsAt`), so that every caller
of `ensureLeadership` (`LeaseRenew`, the revocation) has them; `start` makes it from the wrapper
(`isRaftNode`, `srvLeadCheckOk_of`) and the context it makes. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Spec.go_etcd_io.raft.v3.node__Status

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What the leadership check reads of the server `s`** (persistent): its raft wrapper's `tickMu`
with the lock's pools of reader slots (`rnTickPool`: `isActive` borrows one around
`getLatestTickTs`); the wrapper's node, whose `Status()` returns (`raftStatus`; raft's node API's
`node.Status`); and `s.ctx`, a context (`ensureLeadership`'s `WithTimeout` parent). -/
def srvLeadCheckOk (s : Loc) : IProp GF :=
  iprop((∃ mu : Loc, rnTickMuAddr (srvRAddr s) ↦□ mu ∗ rnTickPool (srvRAddr s) mu) ∗
    (∃ (n : GoInterface) (ni : GoInterfaceOk), rnNodeAddr (srvRAddr s) ↦□ n ∗ ⌜n = GoInterface.ok ni⌝ ∗
      □ ({{ True }} (App (Val #(methods ni.ty go!"Status" ni.v)) (Val #()))
        {{ (st : go_etcd_io.raft.v3.Status), RET #st; True }})) ∗
    (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      structFieldRef EtcdServer go!"ctx" s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd))

instance srvLeadCheckOk_persistent (s : Loc) : Persistent (srvLeadCheckOk (GF := GF) s) := by
  unfold srvLeadCheckOk; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`srvLeadCheckOk` from the wrapper and the context** (`start`): the wrapper at `s.r`
(`isRaftNode`: its `tickMu` and pools; its node, raft's `*node`, whose contract ends in raft's
`isNode`, with which raft's `node.Status` returns) and `s.ctx`'s contract. -/
theorem srvLeadCheckOk_of
    (wp_Status : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      node.Status.spec (GF := GF) (hG := hG))
    (s : Loc) (E : RNEnv GF) (γ : RNNames GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isRaftNode E γ (srvRAddr s) ∗
      structFieldRef EtcdServer go!"ctx" s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd ⊢
      srvLeadCheckOk s := by
  iintro ⟨#Hpkg, #Hr, #Hc, #Hci⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, -, -, -, -, -, -, -, #Hisn⟩
  iunfold srvLeadCheckOk
  isplitr
  · iexists mu
    iframe Hmu Htp
  isplitr
  · iexists n, ⟨go.GoType.PointerType go_etcd_io.raft.v3.node.ty, #γ.nl.loc⟩
    iframe Hn
    isplitr
    · ipureintro; rw [Hnif]
    iintro !> %Φ !> - HΦ
    letI := srvStor (GF := GF) γ.node
    wp_apply wp_Status γ.node γ.nl γ.node.cl srvClusterN γ.id $$ [] as %st -
    · iframe #
    iapply HΦ
    itrivial
  · iexists ctx, cd
    iframe Hc Hci

end lemmas

end EtcdGrove
end Perennial
