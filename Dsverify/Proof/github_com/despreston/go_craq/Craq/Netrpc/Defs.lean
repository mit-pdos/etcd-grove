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

/-! ## The call (H5)

`wp_Call_tag`: Net's `Client.Call` (`models-rpc-server` 2a6b4e5d12: decoding owed only of the
method's answers, `Φ rep []` in hand) for the kit's codec, where the method's answers (`msg = []`)
are the replies with property `T` (the client shows it of each answer it asks for, along with
`Φ`), so the decoding is asked for only of replies with `T` (`T rep := tagOk t rep`: the reply's
type tag is the target's). -/

section call
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- The codec's decoding keeps a frame on success. -/
theorem craqCodec_dec_frame (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF) (R : IProp GF) :
    craqCodec.dec bs ptr Ψ ∗ R ⊢ craqCodec.dec bs ptr (fun ok => if ok then iprop(R ∗ Ψ true) else Ψ false) := by
  unfold craqCodec
  iintro ⟨Hd, HR⟩ %data %dq %Φ Hdata HΦ
  ispecialize Hd $$ %data %dq %Φ Hdata
  iapply Hd
  inext
  iintro %err %ok Hdata %Hok HΨ Herr
  cases ok
  · ispecialize HΦ $$ %err %false Hdata %Hok
    isimp only [Bool.false_eq_true, ite_false] at HΦ Herr
    ispecialize HΦ $$ HΨ Herr
    iexact HΦ
  · ihave HΨ' : iprop(R ∗ Ψ true) $$ [HR HΨ]
    · iframe
    ispecialize HΦ $$ %err %true Hdata %Hok
    isimp only [ite_true] at HΦ Herr
    ispecialize HΦ $$ HΨ' Herr
    iexact HΦ

theorem wp_Call_tag [rcs : RpcClientSpecs GF] (T : List w8 → Prop) (c : Loc) (W : net.rpc.RpcWorld GF)
    (a sm svc M : GoString) (S : net.rpc.MethodSpec GF) (args reply : GoInterface)
    (Φ : List w8 → GoString → IProp GF) (Rargs D : IProp GF) (Θ : List w8 → Bool → IProp GF)
    (HT : ∀ rep, Φ rep [] ⊢ ⌜T rep⌝) :
  {{ net.rpc.isClient c W a ∗ ⌜net.rpc.splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧
        reply ≠ interface.nil⌝ ∗
      net.rpc.codecSet craqCodec ∗
      craqCodec.enc args (fun bs => iprop(S M bs Φ ∗ Rargs)) ∗ D ∗
      □ (D -∗ ∀ rep, ⌜T rep⌝ -∗ craqCodec.dec rep reply (Θ rep)) }}
    (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #sm)) (Val #args)) (Val #reply))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ Rargs ∗ ∃ rep, Φ rep [] ∗ Θ rep true) ∨
      (∃ msg : GoString, ⌜msg ≠ [] ∧ err = net.rpc.serverErr msg⌝ ∗ net.rpc.errMsg err msg ∗ Rargs ∗
        (∃ rep, Φ rep msg) ∗ D) ∨
      (⌜err ≠ interface.nil ∧ net.rpc.notServerErr err⌝ ∗ models_lab.errAny err ∗
        ((Rargs ∗ (D ∨ ∃ rep, Θ rep false)) ∨
          (craqCodec.enc args (fun bs => iprop(S M bs Φ ∗ Rargs)) ∗ D))) }} := by
  have HT2 : ∀ rep, Φ rep [] ⊢ ⌜T rep⌝ ∗ Φ rep [] := fun rep =>
    (BI.and_intro (HT rep) .rfl).trans BI.persistent_and_sep_mp
  iintro %Ψ ⟨#Hc, %Hs, #Hcs, Henc, HD, #Hdec⟩ HΨ
  wp_apply (rcs.call (C := craqCodec) c W a sm svc M S args reply Φ
    Rargs D (fun rep ok => if ok then iprop(Φ rep [] ∗ Θ rep true) else Θ rep false))
    $$ [Henc HD]
  · isplitr
    · iexact Hc
    isplitr
    · ipureintro; exact Hs
    isplitr
    · iexact Hcs
    isplitl [Henc]
    · iexact Henc
    isplitl [HD]
    · iexact HD
    imodintro
    iintro HD %rep HΦ
    ihave HΦ := (HT2 rep) $$ HΦ
    icases HΦ with ⟨%Hrep, HΦ⟩
    iapply craqCodec_dec_frame
    isplitr [HΦ]
    · iapply Hdec $$ HD
      ipureintro; exact Hrep
    · iexact HΦ
  iintro %err Hpost
  iapply HΨ
  icases Hpost with (⟨%Herr, HR, %rep, Hok⟩ | ⟨%msg, %Hm, #Hmsg, HR, ⟨%rep, HΦ⟩, HD⟩ |
    ⟨%Herr, #Hany, (⟨HR, (HD | ⟨%rep, Hf⟩)⟩ | Hrest)⟩)
  · ileft
    simp only [ite_true]
    isplitr
    · ipureintro; exact Herr
    iframe
  · iright; ileft
    iexists msg
    isplitr
    · ipureintro; exact Hm
    isplitr
    · iexact Hmsg
    iframe
  · iright; iright
    isplitr
    · ipureintro; exact Herr
    isplitr
    · iexact Hany
    ileft; iframe
  · iright; iright
    simp only [Bool.false_eq_true, ite_false]
    isplitr
    · ipureintro; exact Herr
    isplitr
    · iexact Hany
    ileft; iframe
  · iright; iright
    isplitr
    · ipureintro; exact Herr
    isplitr
    · iexact Hany
    iright; iexact Hrest

/-- The replies' type tags (an empty reply has none). -/
theorem tagOk_nil (t : GoString) : tagOk t [] := by
  intro _ _ h; simp [getTag, getU64] at h

theorem tagOk_EmptyReply :
    tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply" encEmptyReply :=
  tagOk_tagged _ _ (by decide)

theorem tagOk_VersionResp (k : GoString) (v : w64) :
    tagOk go!"github.com/despreston/go-craq/transport/netrpc.VersionResponse" (encVersionResp k v) :=
  tagOk_tagged _ _ (by decide)

theorem tagOk_Item (k x : GoString) :
    tagOk go!"github.com/despreston/go-craq/transport.Item" (encItem k x) :=
  tagOk_tagged _ _ (by decide)

theorem tagOk_Meta (m : MetaV) :
    tagOk go!"github.com/despreston/go-craq/transport.NodeMeta" (encMeta m) :=
  tagOk_tagged _ _ (by decide)

theorem tagOk_PropResp (r : GMap GoString (List (GoString × w64))) (bs : List w8)
    (h : encPropResp r bs) :
    tagOk go!"github.com/despreston/go-craq/transport.PropagateResponse" bs := by
  obtain ⟨es, -, rfl⟩ := h
  exact tagOk_tagged _ _ (by decide)

end call

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
