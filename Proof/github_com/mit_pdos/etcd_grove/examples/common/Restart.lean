/-
**The examples' shared start, for a member stopped and started again** (the restart plan's R2a,
2026-11-02, `notes/restart-plan.md`; DRAFT). Lean-first (no Rocq counterpart).

* `bootPremiseR`: `bootPremise`'s restart case, `bootstrap`'s contract on the stopped member's data
  directory (`bootstrapRestartContract`, R2c), at the same cluster.
* `memberBuiltR`: `memberBuilt` (unserved) at any index the construction starts from: a restarted
  member's apply thread starts at its image's consistent index, a first start's at `0`. R2d gives
  its content.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`bootstrap`'s contract on member `name`'s stopped data directory** (DRAFT; `bootPremise`'s
restart case, see the file header). -/
def bootPremiseR (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64) :
    IProp GF :=
  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk token name cfg ∧ Uok U ∧ γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧ γ.boot = bootLog⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapRestartContract cfg U γ id ctxs N dir)

instance bootPremiseR_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString) (token name : GoString)
    (Uok : BootURLs → Prop) (id : w64) :
    Persistent (bootPremiseR (GF := GF) N ps bootLog ctxs dir token name Uok id) := by
  unfold bootPremiseR; infer_instance

/-- **A member built, at any starting index** (DRAFT; `memberBuilt`'s, unserved, with the apply
thread's starting state `ai₀ at₀ c₀ x₀` any: see the file header). -/
def memberBuiltR (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) : IProp GF :=
  iprop(∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
      (γrn : RNNames) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    srvWatchBuilt s E ∗
    isServerBuilt s γA ci TM E ρ ρ.rd (srvEr ρ E₀ ai₀ c₀ x₀ id (srvTrKey γn γk)) γrn b ai₀
      at₀ c₀ x₀ N ∗
    srvServeBuilt s E cfg 64 ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvLgReader s ∗
    srvReadyCloser s ∗ srvNetMember γn s id τ ∗ srvTrTok γn τ ∗
    ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) ∗
    srvWatchReaders s E 64)

end defs

end common
end EtcdGrove
end Perennial
