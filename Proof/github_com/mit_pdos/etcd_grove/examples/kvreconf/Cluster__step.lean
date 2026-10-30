/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__step.lean`. Lean-first (no
Rocq counterpart).

The message's type and target are read first; then it is made the target's `stepIn`
(`stepIn_intro`: `To` is the target's id) and stepped under a timeout context
(`context.WithTimeoutBackground`, `nodeCtx`); its fate is reported to the sender's node, which
takes only `isNode`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__step
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Spec.context.WithTimeoutBackground
public import Proof.go_etcd_io.raft.v3.InvNodeCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- **The gap** (`sorry`, the one of this file): `err == context.DeadlineExceeded` (`cluster.go`'s
`step`) does not panic when `err` and `DeadlineExceeded`'s value `e2` have the same dynamic type
(the other cases, `err` `nil` or of another type, are `false` and proved below). `err` is what
`Node.Step` returns (`nodeErrS`: `nil`, raft's `ErrStopped`, or the done context's `Err()`, the
value of `context.Canceled` or of `DeadlineExceeded`). Go's `==` on two interfaces of the same
dynamic type compares their values, which panics for an incomparable type (`CheckComparable`);
`context`'s package fact (`context.isInit`) keeps only that `Canceled`'s and `DeadlineExceeded`'s
values are typed errors, not their dynamic types (Go's `*errorString` and `deadlineExceededError`,
both comparable), so with `err = e2` the check cannot be discharged. Either the comparison becomes
`err != nil` (a Go change) or kvreconf takes the read package's premise
`EtcdGrove.ContextReadErrs` (which states `DeadlineExceeded`'s value a `SafeMapKey`). -/
theorem step_errCmp (n : Loc) (γ : Cluster) (N : Namespace) (cd : context.ContextDesc (IProp GF))
    (e1 e2 : GoInterfaceOk) (Φ : val → IProp GF) (_h : e1.ty = e2.ty) :
    (nodeErrS n γ N cd (GoInterface.ok e1) ∗
      globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ GoInterface.ok e2 ∗
      (∀ b : Bool, Φ #b) : IProp GF) ⊢
    WP gl(CheckComparable e1.ty ;; GoOp GoEquals e1.ty glv((e1.v, e2.v))) {{ Φ }} := by
  sorry

theorem Cluster.step.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG))
    (wp_ReportUnreachable : node.ReportUnreachable.spec (GF := GF) (hG := hG))
    (wp_ReportSnapshot : node.ReportSnapshot.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    Cluster.step.spec (GF := GF) (hG := hG) := by
  intro γr vs c sid src dst ml st
  wp_start as ⟨#Hcc, #Hsrc, #Hdst, Hm, #Hsent, Hcred⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  ihave #HctrD := isStats_field (c.[RCluster, go!"Stats"]) go!"Dropped" (by decide) $$ Hstats
  ihave #HctrS := isStats_field (c.[RCluster, go!"Stats"]) go!"SnapshotsSent" (by decide) $$ Hstats
  iclear Hstats
  iunfold isRep at Hdst
  icases Hdst with ⟨%dn, %dstl, %dsts, %dρ, #HD⟩
  iunfold isReplicaR at HD
  icases HD with ⟨#HDrep, -⟩
  iunfold isReplica at HDrep
  icases HDrep with ⟨-, -, #HDnode, -, -, -, #HDisNode, -⟩
  iunfold isRep at Hsrc
  icases Hsrc with ⟨%n, %rst, %sts, %ρ, #HR⟩
  iunfold isReplicaR at HR
  icases HR with ⟨#HSrep, -⟩
  iunfold isReplica at HSrep
  icases HSrep with ⟨-, -, #HSnode, -, -, -, #HSisNode, -⟩
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hctxinit : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hpbinit $Hm] as Hm
  wp_apply wp_GetTo.1 ml _ _ _ _ $$ [$Hpbinit $Hm] as Hm
  try wp_auto
  wp_apply context.wp_Background
  try wp_auto
  wp_apply hWT _ $$ [$Hctxinit $Hcci] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx⟩
  try wp_auto
  ihave #Hnc : nodeCtx ctx' cd $$ []
  · unfold nodeCtx; iright; iexact Hctx
  imod stepIn_intro γr.cluster kvrRaftN st.msg.To' ml sid st rfl $$ [$Hsent $Hm $Hcred] with Hin
  wp_apply wp_node_Step dn γr.cluster kvrRaftN st.msg.To' ml ctx' cd
    $$ [$Hraftinit $HDisNode $Hnc $Hin] as %err #Herr
  try wp_auto
  wp_apply Hcancel
  ihave Hci : (context.isInit : IProp GF) $$ []
  · iapply context.isInit_access $$ Hctxinit
  iNamed Hci
  icases HDeadlineExceeded with ⟨%eD, #HeD, %HeDt⟩
  obtain ⟨e2, rfl⟩ : ∃ e2, eD = GoInterface.ok e2 := by
    cases eD with
    | nil => exact absurd HeDt (by simp [context.isTypedErr])
    | ok e2 => exact ⟨e2, rfl⟩
  try wp_auto
  cases err with
  | nil =>
    try wp_auto
    wp_if_destruct
    · wp_apply wp_add _ _ $$ [$Hpkg $HctrS]
      wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b8 -
      cases b8
      all_goals
        try wp_auto
        wp_apply wp_ReportSnapshot n γr.cluster kvrRaftN sid st.msg.To' _ $$ [$Hraftinit $HSisNode]
        try wp_auto
        iapply HΦ
        itrivial
    · try wp_auto
      iapply HΦ
      itrivial
  | ok e1 =>
    by_cases hty : e1.ty = e2.ty
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true hty)]
      wp_bind gl(CheckComparable e1.ty ;; GoOp GoEquals e1.ty glv((e1.v, e2.v)))
      iapply step_errCmp dn γr.cluster kvrRaftN cd e1 e2 _ hty
      iframe Herr HeD
      iintro %b
      cases b
      · -- not the timeout
        try wp_auto
        wp_if_destruct
        · wp_apply wp_add _ _ $$ [$Hpkg $HctrS]
          wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b8 -
          cases b8
          all_goals
            try wp_auto
            wp_apply wp_ReportSnapshot n γr.cluster kvrRaftN sid st.msg.To' _ $$ [$Hraftinit $HSisNode]
            try wp_auto
            iapply HΦ
            itrivial
        · try wp_auto
          iapply HΦ
          itrivial
      · -- the timeout: dropped
        try wp_auto
        wp_apply wp_add _ _ $$ [$Hpkg $HctrD]
        wp_apply wp_ReportUnreachable n γr.cluster kvrRaftN sid st.msg.To' $$ [$Hraftinit $HSisNode]
        try wp_auto
        wp_if_destruct
        · wp_apply wp_ReportSnapshot n γr.cluster kvrRaftN sid st.msg.To' _ $$ [$Hraftinit $HSisNode]
          try wp_auto
          iapply HΦ
          itrivial
        · try wp_auto
          iapply HΦ
          itrivial
    · simp only [hty, ↓reduceIte]
      try wp_auto
      wp_if_destruct
      · wp_apply wp_add _ _ $$ [$Hpkg $HctrS]
        wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b8 -
        cases b8
        all_goals
          try wp_auto
          wp_apply wp_ReportSnapshot n γr.cluster kvrRaftN sid st.msg.To' _ $$ [$Hraftinit $HSisNode]
          try wp_auto
          iapply HΦ
          itrivial
      · try wp_auto
        iapply HΦ
        itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
