/-
transport/netrpc's client side: internal definitions.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace netrpcP

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]


/-- The shared facts a connected client's methods use (persistent). -/
def env (cfg : Cfg GF) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc ∗
    rpcReady ∗ craqCtx cfg)

instance env_persistent (cfg : Cfg GF) : Persistent (env (hG := hG) cfg) := by
  unfold env rpcReady; infer_instance

/-- The embedded `*Client` `cl` is connected to `a`: its `rpc` field holds a client of `a`. -/
def connected (cfg : Cfg GF) (cl : Loc) (a : GoString) : IProp GF :=
  iprop(∃ r : Loc, structFieldRef transport.netrpc.Client go!"rpc" cl ↦□ r ∗
    net.rpc.isClient r cfg.W a)

instance connected_persistent (cfg : Cfg GF) (cl : Loc) (a : GoString) :
    Persistent (connected (hG := hG) cfg cl a) := by
  unfold connected; infer_instance

theorem ss_node (cfg : Cfg GF) (a : GoString) (h : cfg.W.SS = craqSS cfg.γ cfg.cAddr cfg.chain)
    (hc : cfg.cAddr ∉ cfg.chain) (ha : a ∈ cfg.chain) :
    cfg.W.SS a go!"RPC" = some (nodeSpec cfg.γ cfg.chain a) := by
  rw [h]; unfold craqSS
  have : a ≠ cfg.cAddr := fun e => hc (e ▸ ha)
  simp [this, ha]

theorem ss_coord (cfg : Cfg GF) (h : cfg.W.SS = craqSS cfg.γ cfg.cAddr cfg.chain) :
    cfg.W.SS cfg.cAddr go!"RPC" = some (coordSpec cfg.γ cfg.chain) := by
  rw [h]; unfold craqSS; simp

omit hG sem in
theorem serverErr_inj [go.IntoValInj GoString] {m1 m2 : GoString} (h : net.rpc.serverErr m1 = net.rpc.serverErr m2) :
    m1 = m2 := by
  unfold net.rpc.serverErr interface.mkOk at h
  simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact go.intoVal_inj h

end defs

section specs
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp]
  [G : GooseGlobalGS HasLC.hasLC GF]
variable (γ : CraqNames) (ch : List GoString) (a : GoString) (args : List w8)
  (Φ : List w8 → GoString → IProp GF)

theorem nodeSpec_Ping :
    nodeSpec γ ch a go!"Ping" args Φ = iprop(⌜args = encEmptyArgs⌝ ∗ (Φ encEmptyReply [] ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Update :
    nodeSpec γ ch a go!"Update" args Φ =
      iprop(∃ (md : MetaV) (r : Role), ⌜args = encMeta md ∧ metaAddrsOk ch md⌝ ∗ roleHalf γ a r ∗
        updDep γ r md ∗ ((updPost γ a r md -∗ Φ encEmptyReply []) ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Write :
    nodeSpec γ ch a go!"Write" args Φ =
      iprop(∃ (k x : GoString) (v : w64), ⌜args = encWriteArgs k x v⌝ ∗ valsElem γ v k x ∗
        ((cvLb γ k v -∗ Φ encEmptyReply []) ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Commit :
    nodeSpec γ ch a go!"Commit" args Φ =
      iprop(∃ (k : GoString) (v : w64), ⌜args = encCommitArgs k v⌝ ∗ cvLb γ k v ∗
        (Φ encEmptyReply [] ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_LatestVersion :
    nodeSpec γ ch a go!"LatestVersion" args Φ =
      iprop(∃ (k : GoString) (Q : KvM.Output → IProp GF),
        ⌜args = encString k⌝ ∗ opAU γ (.get k) Q ∗
        ((∀ (v : w64) (σ : KvM.State), Q (.got (σ k)) -∗ readFacts γ k v (σ k) -∗
            Φ (encVersionResp k v) []) ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Read :
    nodeSpec γ ch a go!"Read" args Φ =
      iprop(∃ (k : GoString) (Q : KvM.Output → IProp GF),
        ⌜args = encString k⌝ ∗ opAU γ (.get k) Q ∗ readCont γ k Q Φ) := by
  unfold nodeSpec; simp

theorem nodeSpec_Fwd :
    nodeSpec γ ch a go!"FwdPropagate" args Φ =
      iprop(∃ req : GMap GoString w64, ⌜encPropReq req args⌝ ∗
        ((∀ (resp : GMap GoString (List (GoString × w64))) (rbs : List w8), ⌜encPropResp resp rbs⌝ -∗
          respItems γ resp -∗ Φ rbs []) ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Back :
    nodeSpec γ ch a go!"BackPropagate" args Φ =
      iprop(∃ (req : GMap GoString w64) (L : CLog), ⌜encPropReq req args⌝ ∗ covers γ a L ∗
        ((∀ (resp : GMap GoString (List (GoString × w64))) (rbs : List w8), ⌜encPropResp resp rbs⌝ -∗
          respItems γ resp -∗ respCommitted γ resp -∗ ⌜respCovers req resp L⌝ -∗ Φ rbs []) ∧
        errOk Φ)) := by
  unfold nodeSpec; simp

theorem coordSpec_AddNode :
    coordSpec γ ch go!"AddNode" args Φ =
      iprop(∃ a : GoString, ⌜args = encString a ∧ a ∈ ch⌝ ∗ joinTicket γ a ∗
        ((∀ md : MetaV, Φ (encMeta md) []) ∧ errOk Φ)) := by
  unfold coordSpec; simp

theorem coordSpec_Write :
    coordSpec γ ch go!"Write" args Φ =
      iprop(∃ (k x : GoString) (Q : KvM.Output → IProp GF),
        ⌜args = encClientWriteArgs k x⌝ ∗ opAU γ (.put k x) Q ∗
        ((putReceipt k x Q -∗ Φ encEmptyReply []) ∧ errOk Φ)) := by
  unfold coordSpec; simp

theorem coordSpec_RemoveNode :
    coordSpec γ ch go!"RemoveNode" args Φ =
      iprop(∃ a : GoString, ⌜args = encString a⌝ ∗
        (Φ encEmptyReply [] ∧ ∀ msg : GoString, Φ [] msg)) := by
  unfold coordSpec; simp

end specs

end netrpcP

end github_com.despreston.go_craq

end Perennial
