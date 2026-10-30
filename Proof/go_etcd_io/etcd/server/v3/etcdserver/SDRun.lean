/-
**The apply side's half of the running token, named** (stage P, track S-D, 2026-10-30): the specs of
`apply`, `applyEntries`, `applyAll` and `dvView_cc` each write it as their own `match dv with …`
(`(1 : Qp).half` of `nodeRunning` with a view, `True` without), which Lean compiles to a matcher
of each declaration's own: the proofs rewrite each to `srvRunH` so that the hypotheses and goals
agree. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__apply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section run
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The apply side's half of the running token with a view `dv`, `True` without. -/
def srvRunH (γs : ServerRaftNames) (dv : Option Loc) : IProp GF :=
  match dv with
  | none => iprop(True)
  | some n => (letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half)

theorem srvRunH_none (γs : ServerRaftNames) : srvRunH (GF := GF) γs none = iprop(True) := rfl

theorem srvRunH_some (γs : ServerRaftNames) (n : Loc) :
    srvRunH (GF := GF) γs (some n) =
      (letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) := rfl

theorem srvRunH_apply_spec (γs : ServerRaftNames) (dv : Option Loc) :
    _root_.Perennial.EtcdGrove.EtcdServer.apply.spec.match_1 (fun _ => IProp GF) dv (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH γs dv := by
  cases dv <;> rfl

theorem srvRunH_applyEntries_spec (γs : ServerRaftNames) (dv : Option Loc) :
    _root_.Perennial.EtcdGrove.EtcdServer.applyEntries.spec.match_1 (fun _ => IProp GF) dv (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH γs dv := by
  cases dv <;> rfl

theorem srvRunH_applyAll_spec (γs : ServerRaftNames) (dv : Option Loc) :
    _root_.Perennial.EtcdGrove.EtcdServer.applyAll.spec.match_1 (fun _ => IProp GF) dv (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH γs dv := by
  cases dv <;> rfl

/-- `dvView_cc` over `srvRunH`. -/
theorem dvView_ccR (s : Loc) (γs : ServerRaftNames) (dv : Option Loc) (kc0 lid : w64)
    (L rest : List EntryModel) (m : EntryModel) (cm : ConfChangeM)
    (Hty : m.typ = W32 1) (Hdec : ccDecodeV1 m.data = some cm)
    (Hdyn : ∀ n, dv = some n → ccApplyOkR γs.raft cm ∧ lid ∈ γs.raft.cfg ∧
      withIdx ((γs.pre ++ L).map EntryModel.toLE) = γs.pre ++ L ∧
      (∀ x, ¬ RemovedIn (γs.pre ++ L) x)) :
    dvView (GF := GF) γs dv L ∗ dvRes s γs dv (L ++ m :: rest) ∗ srvRunH γs dv ⊢
      ∃ (v : ConfigView) (m' : Membership),
        dvCCPre s γs dv v (srvLE γs (L ++ m :: rest)) ∗
        ⌜∀ n, dv = some n →
          srvCCPre (srvRule kc0 γs.raft.boot) (srvLE γs (L ++ m :: rest)) v
            (.v1 (membership.ccRaftEff (restModel kc0 γs.raft.boot (γs.pre ++ L)).bk cm))
            (γs.pre ++ L).length m.toLE m'⌝ ∗
        (dvCCPost γs dv (γs.pre ++ L).length m' -∗ dvView γs dv (L ++ [m]) ∗ srvRunH γs dv) := by
  have h := dvView_cc (GF := GF) s γs dv kc0 lid L rest m cm Hty Hdec Hdyn
  cases dv <;> exact h

end run

end EtcdGrove
end Perennial
