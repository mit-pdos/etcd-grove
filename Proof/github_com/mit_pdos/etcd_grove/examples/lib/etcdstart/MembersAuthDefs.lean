/-
**The auth-on start of a cluster of any size: its vocabulary** (authN, 2026-11-15,
`notes/authN-plan.md`). Lean-first (no Rocq counterpart). `MembersDefs`' for `StartMembersAuth`
(`examples/lib/etcdstart/auth.go`): the members' configuration is authkv's (the simple token
provider), each member's ghost state the mode-`on` one (`memberBootOn`).

* `cfgOkOn`: `cfgOk` and the simple token provider (auth3's `cfgOk` at any token);
* `bootPremiseOn`: `bootPremise` at `cfgOkOn` (auth3's `bootPremise`, at any token and URLs);
* `memberPreOn`: what `StartMembersAuth` takes of each member (`memberPre`, auth on).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The configuration `StartMemberAuth` passes to `NewServer`**, by its scalar fields: `cfgOk`'s
and the simple token provider. -/
def cfgOkOn (token name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfgOk token name cfg ∧ cfg.AuthToken' = go!"simple"

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`bootstrap`'s contract for member `name`, with auth on**: `bootPremise` at `cfgOkOn`. -/
def bootPremiseOn (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64) :
    IProp GF :=
  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOkOn token name cfg ∧ Uok U ∧
        γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧ γ.boot = bootLog⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir)

instance bootPremiseOn_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString) (token name : GoString)
    (Uok : BootURLs → Prop) (id : w64) :
    Persistent (bootPremiseOn (GF := GF) N ps bootLog ctxs dir token name Uok id) := by
  unfold bootPremiseOn; infer_instance

/-- **What `StartMembersAuth` takes of each member** (`memberPre` with auth on). -/
def memberPreOn (N : Nat) (token : GoString) (ms : List GMember) (ps : List w64)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    (x : GMember × MemberG GF) (m : lease.Mode := .none) : IProp GF :=
  iprop(bootPremiseOn N ps bootLog ctxs dir token x.1.Name' (urlsN ms x.1) x.2.id ∗
    memberBootOn x.2.γ ctxs x.2.ρ x.2.E Φs x.2.id false m ∗ netHttpOk γn x.2.id ∗
    memberFreshRes x.1.Name' ⟨some x.1.Peer', none⟩ γn)

/-- A started member's thread token, out of its `memberUpOn` (its `srvGoRes`), and back (auth3's). -/
theorem memberUpOn_tok (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) (m : lease.Mode := .none) :
    memberUpOn s ρ E₀ lg γn id γa m ⊢
      threadTok ∗ (threadTok -∗ memberUpOn s ρ E₀ lg γn id γa m) := by
  iintro H
  iunfold memberUpOn at H
  icases H with ⟨%E, %cfg, %γw, %HE, H1, H2, #H3, #H4, #H5, Hgo, H7, H8, #H9, #H10, H11, H12,
    #H13, #H14⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  iframe Htok
  iintro Htok
  iunfold memberUpOn
  iexists E, cfg, γw
  iframe
  iframe #
  isplitr
  · ipureintro; exact HE
  iunfold srvGoRes
  iframe

end defs

end etcdstart
end EtcdGrove
end Perennial
