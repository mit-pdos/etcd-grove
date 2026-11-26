/-
transport/netrpc's client side: internal definitions.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Hyps
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.WireLen

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
variable [net.rpc.Assumptions] [π : NetProtoGS]


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
variable [net.rpc.Assumptions] [π : NetProtoGS]

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

/-- The codec's encoding is monotone in its continuation. -/
theorem craqCodec_enc_mono (v : GoInterface) (Ψ Ψ' : List w8 → IProp GF) :
    craqCodec.enc v Ψ ∗ (∀ bs, Ψ bs -∗ Ψ' bs) ⊢ craqCodec.enc v Ψ' := by
  unfold craqCodec
  iintro ⟨He, Hw⟩ %Φ HΦ
  iapply He
  inext
  iintro %sl %bs Hsl Hcap HΨ
  iapply HΦ $$ Hsl Hcap
  iapply Hw $$ HΨ

theorem wp_Call_tag [rcs : RpcClientSpecs GF] (T : List w8 → Prop) (c : Loc) (W : net.rpc.RpcWorld GF)
    (a sm svc M : GoString) (S : net.rpc.MethodSpec GF) (args reply : GoInterface)
    (Φ : List w8 → GoString → IProp GF) (Rargs D : IProp GF) (Θ : List w8 → Bool → IProp GF)
    (HT : ∀ rep, Φ rep [] ⊢ ⌜T rep⌝)
    (HS : ∀ bs, S M bs Φ ⊢ ⌜bs.length ≤ net.rpc.maxFrameN⌝)
    (Hsm : sm.length + 16 ≤ net.rpc.maxFrameN := by simp [net.rpc.maxFrameN]) :
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
      (⌜err ≠ interface.nil ∧ net.rpc.notServerErr err⌝ ∗ models_lab.errPlain err ∗
        ((Rargs ∗ (D ∨ ∃ rep, Θ rep false)) ∨
          (craqCodec.enc args (fun bs => iprop(S M bs Φ ∗ Rargs)) ∗ D))) }} := by
  have HT2 : ∀ rep, Φ rep [] ⊢ ⌜T rep⌝ ∗ Φ rep [] := fun rep =>
    (BI.and_intro (HT rep) .rfl).trans BI.persistent_and_sep_mp
  have HS2 : ∀ bs, S M bs Φ ⊢ ⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗ S M bs Φ := fun bs =>
    (BI.and_intro (HS bs) .rfl).trans BI.persistent_and_sep_mp
  iintro %Ψ ⟨#Hc, %Hs, #Hcs, Henc, HD, #Hdec⟩ HΨ
  wp_apply (rcs.call (C := craqCodec) c W a sm svc M S args reply Φ
    Rargs D (fun rep ok => if ok then iprop(Φ rep [] ∗ Θ rep true) else Θ rep false))
    $$ [Henc HD]
  · isplitr
    · iexact Hc
    isplitr
    · ipureintro; exact Hs
    isplitr
    · ipureintro; exact Hsm
    isplitr
    · iexact Hcs
    isplitl [Henc]
    · iapply craqCodec_enc_mono
      iframe Henc
      iintro %bs ⟨HSM, HR⟩
      ihave HSM := HS2 bs $$ HSM
      icases HSM with ⟨%Hl, HSM⟩
      isplitr
      · ipureintro; exact Hl
      iframe
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
    iright
    icases Hrest with ⟨Henc, HD⟩
    iframe HD
    iapply craqCodec_enc_mono
    iframe Henc
    iintro %bs ⟨-, HSM⟩
    iexact HSM

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
      iprop(∃ (k : GoString) (v : w64), ⌜args = encCommitArgs k v ∧ keyOk k⌝ ∗ cvLb γ k v ∗
        (Φ encEmptyReply [] ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_LatestVersion :
    nodeSpec γ ch a go!"LatestVersion" args Φ =
      iprop(∃ (k : GoString) (Q : KvM.Output → IProp GF),
        ⌜args = encString k ∧ keyOk k⌝ ∗ opAU γ (.get k) Q ∗
        ((∀ (v : w64) (σ : KvM.State), Q (.got (σ k)) -∗ readFacts γ k v (σ k) -∗
            Φ (encVersionResp k v) []) ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Read :
    nodeSpec γ ch a go!"Read" args Φ =
      iprop(∃ (k : GoString) (Q : KvM.Output → IProp GF),
        ⌜args = encString k ∧ keyOk k⌝ ∗ opAU γ (.get k) Q ∗ readCont γ k Q Φ) := by
  unfold nodeSpec; simp

theorem nodeSpec_Fwd :
    nodeSpec γ ch a go!"FwdPropagate" args Φ =
      iprop(∃ req : GMap GoString w64, ⌜encPropReq req args ∧ reqKeysOk req⌝ ∗
        ((∀ (resp : GMap GoString (List (GoString × w64))) (rbs : List w8), ⌜encPropResp resp rbs⌝ -∗
          respItems γ resp -∗ Φ rbs []) ∧ errOk Φ)) := by
  unfold nodeSpec; simp

theorem nodeSpec_Back :
    nodeSpec γ ch a go!"BackPropagate" args Φ =
      iprop(∃ (req : GMap GoString w64) (L : CLog), ⌜encPropReq req args ∧ reqKeysOk req⌝ ∗
        covers γ a L ∗
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
        ⌜args = encClientWriteArgs k x ∧ kvOk k x⌝ ∗ opAU γ (.put k x) Q ∗
        ((putReceipt k x Q -∗ Φ encEmptyReply []) ∧ errOk Φ)) := by
  unfold coordSpec; simp

theorem coordSpec_RemoveNode :
    coordSpec γ ch go!"RemoveNode" args Φ =
      iprop(∃ a : GoString, ⌜args = encString a ∧ a.length < 256⌝ ∗
        (Φ encEmptyReply [] ∧ ∀ msg : GoString, Φ [] msg)) := by
  unfold coordSpec; simp

/-! The deposits bound the arguments' encoding (`WireLen.lean`): what `wp_Call_tag` asks. -/

theorem nodeSpec_frame (hch : ∀ b ∈ ch, b.length < 256) (m : GoString) :
    nodeSpec γ ch a m args Φ ⊢ ⌜args.length ≤ net.rpc.maxFrameN⌝ := by
  have hm : ∀ md : MetaV, metaAddrsOk ch md →
      md.prev.length < 256 ∧ md.next.length < 256 ∧ md.tail.length < 256 := by
    intro md hmd
    unfold metaAddrsOk at hmd
    obtain ⟨h1, h2, h3⟩ := hmd
    have hb : ∀ b, b ∈ go!"" :: ch → b.length < 256 := by
      intro b hb; rcases List.mem_cons.1 hb with rfl | hb
      · decide
      · exact hch b hb
    exact ⟨hb _ h1, hb _ h2, hb _ h3⟩
  unfold nodeSpec
  split
  · iintro ⟨%h, -⟩; subst h; ipureintro; exact encEmptyArgs_frame
  split
  · iintro ⟨%md, %r, %h, -⟩; obtain ⟨rfl, hmd⟩ := h; ipureintro; exact encMeta_frame md (hm md hmd)
  split
  · iintro ⟨%k, %x, %v, %h, #Hve, -⟩; subst h
    ihave %hkx := valsElem_kvOk γ v k x $$ Hve
    ipureintro; exact encWriteArgs_frame k x v hkx
  split
  · iintro ⟨%k, %v, %h, -⟩; obtain ⟨rfl, hk⟩ := h; ipureintro; exact encCommitArgs_frame k v hk
  split
  · iintro ⟨%k, %Q, %h, -⟩; obtain ⟨rfl, hk⟩ := h; ipureintro
    exact encString_frame k (by unfold keyOk at hk; omega)
  split
  · iintro ⟨%k, %Q, %h, -⟩; obtain ⟨rfl, hk⟩ := h; ipureintro
    exact encString_frame k (by unfold keyOk at hk; omega)
  split
  · iintro ⟨%req, %h, -⟩; ipureintro; exact encPropReq_frame req args h.1 h.2
  split
  · iintro ⟨%req, %L, %h, -⟩; ipureintro; exact encPropReq_frame req args h.1 h.2
  · exact BI.false_elim

theorem coordSpec_frame (hch : ∀ b ∈ ch, b.length < 256) (m : GoString) :
    coordSpec γ ch m args Φ ⊢ ⌜args.length ≤ net.rpc.maxFrameN⌝ := by
  unfold coordSpec
  split
  · iintro ⟨%a', %h, -⟩; obtain ⟨rfl, ha⟩ := h; ipureintro; exact encString_frame a' (hch a' ha)
  split
  · iintro ⟨%k, %x, %Q, %h, -⟩; obtain ⟨rfl, hkx⟩ := h; ipureintro
    exact encClientWriteArgs_frame k x hkx
  split
  · iintro ⟨%a', %h, -⟩; obtain ⟨rfl, ha⟩ := h; ipureintro; exact encString_frame a' ha
  · exact BI.false_elim

end specs

end netrpcP

end github_com.despreston.go_craq

end Perennial
