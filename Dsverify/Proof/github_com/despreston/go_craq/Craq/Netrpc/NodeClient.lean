/-
transport/netrpc: the methods of a connected `*NodeClient` (each a `Client.Call` with the
address's method spec, the codec's encode lemma for the argument and decode lemma for the
reply).

`LatestVersion`, `Update`, `FwdPropagate` and `BackPropagate` are proved in the corrected forms
of hub requests H1/H2 (`notes/hub-requests.md`): `wp_*_fixed`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace netrpcP

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [rcs : RpcClientSpecs GF]


theorem wp_Ping (Henc : enc_EmptyArgs.spec (GF := GF)) (Hdec : dec_EmptyReply.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗
        Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Ping" #c)) (Val #())) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %Φ HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_alloc pa as Hpa
  wp_auto
  wp_alloc pr as Hpr
  wp_auto
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => BI.pure_mono (fun h => by rw [h rfl]; exact tagOk_EmptyReply)) (tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply") r cfg.W a go!"RPC.Ping" go!"RPC" go!"Ping"
    (nodeSpec cfg.γ cfg.chain a) _ _ (fun rep msg => iprop(⌜msg = [] → rep = encEmptyReply⌝)) iprop(True)
    (pr ↦ transport.netrpc.EmptyReply.mk) (fun _ _ => pr ↦ transport.netrpc.EmptyReply.mk)) $$ [Hpa Hpr]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Hpa]
    · iapply Henc pa (DFrac.own 1)
      iframe
      iintro _
      rw [nodeSpec_Ping]
      isplitl
      · isplitr
        · ipureintro; rfl
        isplit
        · ipureintro; intro _; rfl
        · unfold errOk; iintro %_ %Hm; ipureintro; intro h; exact absurd h Hm
      · ipureintro; trivial
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hpr
      iexact Hpr
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact Herr
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

theorem wp_Write (Henc : enc_WriteArgs.spec (GF := GF)) (Hdec : dec_EmptyReply.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (k : GoString) (sl : GoSlice) (x : GoString) (v : w64) (Φ : val → IProp GF),
      sl ↦*□ x -∗ valsElem cfg.γ v k x -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∗ cvLb cfg.γ k v ∨ models_lab.errAny err) -∗
        Φ #err) -∗
      WP (App (App (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Write" #c)) (Val #k)) (Val #sl)) (Val #v)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %k %sl %x %v %Φ #Hsl Hve HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_alloc pa as Hpa
  wp_auto
  wp_alloc pr as Hpr
  wp_auto
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => by iintro ⟨%h, -⟩; ipureintro; rw [h rfl]; exact tagOk_EmptyReply) (tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply") r cfg.W a go!"RPC.Write" go!"RPC" go!"Write"
    (nodeSpec cfg.γ cfg.chain a) _ _
    (fun rep msg => iprop(⌜msg = [] → rep = encEmptyReply⌝ ∗ (⌜msg = []⌝ -∗ cvLb cfg.γ k v))) iprop(True)
    (pr ↦ transport.netrpc.EmptyReply.mk) (fun _ _ => pr ↦ transport.netrpc.EmptyReply.mk))
    $$ [Hpa Hpr Hve]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Hpa Hve]
    · iapply Henc pa (DFrac.own 1) k sl DFrac.discard x v
      iframe
      isplitr
      · iexact Hsl
      iintro _ _
      rw [nodeSpec_Write]
      isplitl
      · iexists k, x, v
        iframe
        isplitr
        · ipureintro; rfl
        isplit
        · iintro Hlb
          isplitr
          · ipureintro; intro _; rfl
          iintro %_; iexact Hlb
        · unfold errOk; iintro %_ %Hne
          isplitr
          · ipureintro; intro h; exact absurd h Hne
          iintro %Heq; exact absurd Heq Hne
      · ipureintro; trivial
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hpr
      iexact Hpr
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -, %rep, ⟨-, Hlb⟩, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft
    isplitr
    · ipureintro; exact Herr
    iapply Hlb; ipureintro; rfl
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

theorem wp_Commit (Henc : enc_CommitArgs.spec (GF := GF)) (Hdec : dec_EmptyReply.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (k : GoString) (v : w64) (Φ : val → IProp GF), ⌜keyOk k⌝ -∗ cvLb cfg.γ k v -∗
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Commit" #c)) (Val #k)) (Val #v)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %k %v %Φ %hk Hlb HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_alloc pa as Hpa
  wp_auto
  wp_alloc pr as Hpr
  wp_auto
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => BI.pure_mono (fun h => by rw [h rfl]; exact tagOk_EmptyReply)) (tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply") r cfg.W a go!"RPC.Commit" go!"RPC" go!"Commit"
    (nodeSpec cfg.γ cfg.chain a) _ _ (fun rep msg => iprop(⌜msg = [] → rep = encEmptyReply⌝)) iprop(True)
    (pr ↦ transport.netrpc.EmptyReply.mk) (fun _ _ => pr ↦ transport.netrpc.EmptyReply.mk))
    $$ [Hpa Hpr Hlb]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Hpa Hlb]
    · iapply Henc pa (DFrac.own 1) k v
      iframe
      iintro _
      rw [nodeSpec_Commit]
      isplitl
      · iexists k, v
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hk⟩
        isplit
        · ipureintro; intro _; rfl
        · unfold errOk; iintro %_ %Hm; ipureintro; intro h; exact absurd h Hm
      · ipureintro; trivial
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hpr
      iexact Hpr
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact Herr
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

/-- `LatestVersion`, H1's form. -/
theorem wp_LatestVersion_fixed (Henc : enc_string.spec (GF := GF))
    (Hdec : dec_VersionResponse.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      ⌜keyOk k⌝ -∗ opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (v : w64) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ (∃ σ : KvM.State, Q (.got (σ k)) ∗ readFacts cfg.γ k v (σ k)) ∨
            models_lab.errAny err) -∗
          Φ (PairV (PairV #k' #v) #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"LatestVersion" #c)) (Val #k)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %k %Q %Φ %hk HAU HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  rw [show zero_val transport.netrpc.VersionResponse =
    transport.netrpc.VersionResponse.mk go!"" (W64 0) from rfl]
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => by
      iintro H; ispecialize H $$ %rfl; icases H with ⟨%v, %σ, %Hrep, -⟩
      ipureintro; rw [Hrep]; exact tagOk_VersionResp k v)
    (tagOk go!"github.com/despreston/go-craq/transport/netrpc.VersionResponse") r cfg.W a go!"RPC.LatestVersion" go!"RPC" go!"LatestVersion"
    (nodeSpec cfg.γ cfg.chain a) _ _
    (fun rep msg => iprop(⌜msg = []⌝ -∗ ∃ (v : w64) (σ : KvM.State), ⌜rep = encVersionResp k v⌝ ∗
      Q (.got (σ k)) ∗ readFacts cfg.γ k v (σ k))) iprop(True)
    (reply_ptr ↦ transport.netrpc.VersionResponse.mk go!"" (W64 0))
    (fun rep ok => if ok then iprop(∃ (k0 : GoString) (v0 : w64),
        reply_ptr ↦ transport.netrpc.VersionResponse.mk k0 v0 ∗
        ⌜∀ k' v', rep = encVersionResp k' v' → k0 = k' ∧ v0 = v'⌝)
      else iprop(∃ (k0 : GoString) (v0 : w64), reply_ptr ↦ transport.netrpc.VersionResponse.mk k0 v0)))
    $$ [reply HAU]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [HAU]
    · iapply Henc k
      rw [nodeSpec_LatestVersion]
      isplitl
      · iexists k, Q
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hk⟩
        isplit
        · iintro %v %σ HQ Hrf %_
          iexists v, σ
          iframe
          ipureintro; rfl
        · unfold errOk; iintro %_ %Hne %Heq; exact absurd Heq Hne
      · ipureintro; trivial
    isplitl [reply]
    · iexact reply
    · imodintro
      iintro Hrp %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hok
      iexact Hok
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -, %rep, HΦ', Hok⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -, -, Hrp⟩ |
    ⟨%Herr, #Hany, Hrest⟩)
  · ispecialize HΦ' $$ %rfl
    icases HΦ' with ⟨%v, %σ, %Hrep, HQ, Hrf⟩
    simp only [ite_true]
    icases Hok with ⟨%k0, %v0, Hrp, %Hkv⟩
    obtain ⟨-, rfl⟩ := Hkv k v Hrep
    subst Herr
    iStructNamed Hrp
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists σ
    iframe
  · subst Herr
    unfold net.rpc.serverErr
    iStructNamed Hrp
    wp_auto
    iapply HΦ
    iright; iapply errMsg_errAny; iexact Hmsg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrest with (⟨-, (Hrp | ⟨%rep, %k0, %v0, Hrp⟩)⟩ | ⟨-, Hrp⟩)
    all_goals
      iStructNamed Hrp
      wp_auto
      iapply HΦ
      iright; iexact Hany

/-- `Update`, H2's form. -/
theorem wp_Update_fixed (Henc : enc_NodeMeta.spec (GF := GF)) (Hdec : dec_EmptyReply.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (ptr : Loc) (dq : DFrac) (m : MetaV) (r : Role) (Φ : val → IProp GF),
      ⌜metaAddrsOk cfg.chain m⌝ -∗ metaPtr ptr dq m -∗ roleHalf cfg.γ a r -∗ updDep cfg.γ r m -∗
      ▷ (∀ err : GoInterface,
          (⌜err = interface.nil⌝ ∗ metaPtr ptr dq m ∗ updPost cfg.γ a r m) ∨ models_lab.errAny err -∗
          Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Update" #c)) (Val #ptr)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %ptr %dq %m %ro %Φ %Hok Hm Hrole Hdep HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_alloc pr as Hpr
  wp_auto
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => by iintro ⟨%h, -⟩; ipureintro; rw [h rfl]; exact tagOk_EmptyReply) (tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply") r cfg.W a go!"RPC.Update" go!"RPC" go!"Update"
    (nodeSpec cfg.γ cfg.chain a) _ _
    (fun rep msg => iprop(⌜msg = [] → rep = encEmptyReply⌝ ∗ (⌜msg = []⌝ -∗ updPost cfg.γ a ro m)))
    (metaPtr ptr dq m)
    (pr ↦ transport.netrpc.EmptyReply.mk) (fun _ _ => pr ↦ transport.netrpc.EmptyReply.mk))
    $$ [Hm Hrole Hdep Hpr]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Hm Hrole Hdep]
    · iapply Henc ptr dq m
      iframe
      iintro Hm
      iframe
      rw [nodeSpec_Update]
      iexists m, ro
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Hok⟩
      isplit
      · iintro Hpost
        isplitr
        · ipureintro; intro _; rfl
        iintro %_; iexact Hpost
      · unfold errOk; iintro %_ %Hne
        isplitr
        · ipureintro; intro h; exact absurd h Hne
        iintro %Heq; exact absurd Heq Hne
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hpr
      iexact Hpr
  iintro %err Hpost
  icases Hpost with (⟨%Herr, Hm, %rep, ⟨-, Hp⟩, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft
    isplitr
    · ipureintro; exact Herr
    iframe
    iapply Hp; ipureintro; rfl
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

/-- `Read`. -/
theorem wp_Read (Henc : enc_string.spec (GF := GF)) (Hdec : dec_Item.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (k : GoString) (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      ⌜keyOk k⌝ -∗ opAU cfg.γ (.get k) Q -∗
      ▷ (∀ (k' : GoString) (sl : GoSlice) (err : GoInterface),
          ((⌜err = interface.nil⌝ ∗ ∃ (x : GoString) (σ : KvM.State), sl ↦* x ∗
              Q (.got (σ k)) ∗ ⌜σ k = some x⌝) ∨
            (⌜err = net.rpc.serverErr notFoundMsg⌝ ∗ ∃ σ : KvM.State, Q (.got (σ k)) ∗
              ⌜σ k = none⌝) ∨
            (⌜err ≠ interface.nil ∧ err ≠ net.rpc.serverErr notFoundMsg ∧
              (net.rpc.notServerErr err ∨ ∃ msg, err = net.rpc.serverErr msg)⌝)) -∗
          Φ (PairV (PairV #k' #sl) #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Read" #c)) (Val #k)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %k %Q %Φ %hk HAU HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => by
      rw [if_pos rfl]; iintro ⟨%x, %σ, %Hrep, -⟩
      ipureintro; rw [Hrep]; exact tagOk_Item k x)
    (tagOk go!"github.com/despreston/go-craq/transport.Item") r cfg.W a go!"RPC.Read" go!"RPC" go!"Read"
    (nodeSpec cfg.γ cfg.chain a) _ _
    (fun rep msg => if msg = [] then
        iprop(∃ (x : GoString) (σ : KvM.State), ⌜rep = encItem k x⌝ ∗ Q (.got (σ k)) ∗
          ⌜σ k = some x⌝)
      else if msg = notFoundMsg then iprop(∃ σ : KvM.State, Q (.got (σ k)) ∗ ⌜σ k = none⌝)
      else iprop(True)) iprop(True)
    («$r0_ptr» ↦ transport.Item.mk go!"" slice.nil)
    (fun rep ok => if ok then iprop(∃ (k0 : GoString) (sl : GoSlice) (x0 : GoString),
        «$r0_ptr» ↦ transport.Item.mk k0 sl ∗ sl ↦* x0 ∗
        ⌜∀ k' x', rep = encItem k' x' → k0 = k' ∧ x0 = x'⌝)
      else iprop(∃ (k0 : GoString) (sl0 : GoSlice), «$r0_ptr» ↦ transport.Item.mk k0 sl0)))
    $$ [«$r0» HAU]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [HAU]
    · iapply Henc k
      rw [nodeSpec_Read]
      isplitl
      · iexists k, Q
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hk⟩
        unfold readCont
        isplit
        · iintro %x %σ HQ %Hx
          rw [if_pos rfl]
          iexists x, σ
          iframe
          ipureintro; exact ⟨rfl, Hx⟩
        isplit
        · iintro %σ HQ %Hn
          rw [if_neg (by decide : notFoundMsg ≠ []), if_pos rfl]
          iexists σ
          iframe
          ipureintro; exact Hn
        · iintro %msg %Hmsg
          rw [if_neg Hmsg.1, if_neg Hmsg.2]
          ipureintro; trivial
      · ipureintro; trivial
    isplitl [«$r0»]
    · iexact «$r0»
    · imodintro
      iintro Hrp %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hok
      iexact Hok
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -, %rep, HΦ', Hok⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -, ⟨%rep, HΦ'⟩, Hrp⟩ |
    ⟨%Herr, #Hany, Hrest⟩)
  · rw [if_pos rfl]
    icases HΦ' with ⟨%x, %σ, %Hrep, HQ, %Hx⟩
    simp only [ite_true]
    icases Hok with ⟨%k0, %sl, %x0, Hrp, Hsl, %Hkx⟩
    obtain ⟨-, rfl⟩ := Hkx k x Hrep
    subst Herr
    iStructNamed Hrp
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists x0, σ
    iframe
    ipureintro; exact Hx
  · subst Herr
    rw [if_neg Hne]
    by_cases hnf : msg = notFoundMsg
    · subst hnf
      rw [if_pos rfl]
      icases HΦ' with ⟨%σ, HQ, %Hn⟩
      unfold net.rpc.serverErr
      iStructNamed Hrp
      wp_auto
      iapply HΦ
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists σ
      iframe
      ipureintro; exact Hn
    · unfold net.rpc.serverErr
      iStructNamed Hrp
      wp_auto
      iapply HΦ
      iright; iright
      ipureintro
      refine ⟨net.rpc.serverErr_ne_nil msg, fun h => hnf (serverErr_inj h), Or.inr ⟨msg, rfl⟩⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨Hnn, Hns⟩ := Herr
    icases Hrest with (⟨-, (Hrp | ⟨%rep, %k0, %sl0, Hrp⟩)⟩ | ⟨-, Hrp⟩)
    all_goals
      iStructNamed Hrp
      wp_auto
      iapply HΦ
      iright; iright
      ipureintro
      refine ⟨Hnn, fun h => ?_, Or.inl Hns⟩
      rw [h] at Hns; exact net.rpc.notServerErr_serverErr _ Hns

/-- `FwdPropagate`, H1/H2's form. -/
theorem wp_FwdPropagate_fixed (Henc : enc_PropagateRequest.spec (GF := GF)) (Hdec : dec_PropagateResponse.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (Φ : val → IProp GF),
      ⌜reqKeysOk req⌝ -∗ reqPtr ptr dq req -∗
      ▷ (∀ (rp : Loc) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ reqPtr ptr dq req ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp) ∨
            models_lab.errAny err) -∗ Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"FwdPropagate" #c)) (Val #ptr)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %ptr %dq %req %Φ %hreq Hreq HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) _ _) as %mp Hmp
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => by
      iintro H; ispecialize H $$ %rfl; icases H with ⟨%resp, %Hresp, -⟩
      ipureintro; exact tagOk_PropResp resp rep Hresp)
    (tagOk go!"github.com/despreston/go-craq/transport.PropagateResponse") r cfg.W a go!"RPC.FwdPropagate" go!"RPC" go!"FwdPropagate"
    (nodeSpec cfg.γ cfg.chain a) _ _
    (fun rep msg => iprop(⌜msg = []⌝ -∗ ∃ resp, ⌜encPropResp resp rep⌝ ∗ respItems cfg.γ resp))
    (reqPtr ptr dq req)
    iprop(«$r0_ptr» ↦ mp ∗ ownMap mp (DFrac.own 1) (∅ : GMap GoString GoSlice))
    (fun rep ok => if ok then iprop(∃ resp, respPtr «$r0_ptr» resp ∗ ⌜∀ r, encPropResp r rep → resp = r⌝)
      else iprop(∃ mp' : Loc, «$r0_ptr» ↦ mp')))
    $$ [Hreq «$r0» Hmp]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Hreq]
    · iapply Henc ptr dq req
      iframe
      iintro Hreq %bs %Hbs
      iframe
      rw [nodeSpec_Fwd]
      iexists req
      iframe
      isplitr
      · ipureintro; exact ⟨Hbs, hreq⟩
      isplit
      · iintro %resp %rbs %Hrbs Hi %_
        iexists resp
        iframe
        ipureintro; exact Hrbs
      · unfold errOk; iintro %_ %Hne %Heq; exact absurd Heq Hne
    isplitl [«$r0» Hmp]
    · iframe
    · imodintro
      iintro ⟨Hrp, Hmp⟩ %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hok
      iexact Hok
  iintro %err Hpost
  icases Hpost with (⟨%Herr, Hreq, %rep, HΦ', Hok⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, Hreq, -, -⟩ | ⟨%Herr, #Hany, Hrest⟩)
  · ispecialize HΦ' $$ %rfl
    icases HΦ' with ⟨%resp, %Hresp, Hi⟩
    simp only [ite_true]
    icases Hok with ⟨%resp', Hrp, %Hr'⟩
    obtain rfl := Hr' resp Hresp
    subst Herr
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iframe
  · subst Herr
    unfold net.rpc.serverErr
    wp_auto
    iapply HΦ
    iright; iapply errMsg_errAny; iexact Hmsg
  · rcases err with e | _
    · wp_auto
      iapply HΦ
      iright; iexact Hany
    · exact absurd rfl Herr.1

/-- `BackPropagate`, H1/H2's form. -/
theorem wp_BackPropagate_fixed (Henc : enc_PropagateRequest.spec (GF := GF)) (Hdec : dec_PropagateResponse.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (L : CLog) (Φ : val → IProp GF),
      ⌜reqKeysOk req⌝ -∗ reqPtr ptr dq req -∗ covers cfg.γ a L -∗
      ▷ (∀ (rp : Loc) (err : GoInterface),
          (⌜err = interface.nil⌝ ∗ reqPtr ptr dq req ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp ∗
              respCommitted cfg.γ resp ∗ ⌜respCovers req resp L⌝) ∨
            models_lab.errAny err) -∗ Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"BackPropagate" #c)) (Val #ptr)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %ptr %dq %req %L %Φ %hreq Hreq Hcov HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) _ _) as %mp Hmp
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_apply (wp_Call_tag (HS := fun bs => nodeSpec_frame _ _ _ bs _ Hss.2.2.2.2 _) (HT := fun rep => by
      iintro H; ispecialize H $$ %rfl; icases H with ⟨%resp, %Hresp, -⟩
      ipureintro; exact tagOk_PropResp resp rep Hresp)
    (tagOk go!"github.com/despreston/go-craq/transport.PropagateResponse") r cfg.W a go!"RPC.BackPropagate" go!"RPC" go!"BackPropagate"
    (nodeSpec cfg.γ cfg.chain a) _ _
    (fun rep msg => iprop(⌜msg = []⌝ -∗ ∃ resp, ⌜encPropResp resp rep⌝ ∗ respItems cfg.γ resp ∗
      respCommitted cfg.γ resp ∗ ⌜respCovers req resp L⌝))
    (reqPtr ptr dq req)
    iprop(«$r0_ptr» ↦ mp ∗ ownMap mp (DFrac.own 1) (∅ : GMap GoString GoSlice))
    (fun rep ok => if ok then iprop(∃ resp, respPtr «$r0_ptr» resp ∗ ⌜∀ r, encPropResp r rep → resp = r⌝)
      else iprop(∃ mp' : Loc, «$r0_ptr» ↦ mp')))
    $$ [Hreq Hcov «$r0» Hmp]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_node cfg a Hss.1 Hss.2.2.1 ha, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Hreq Hcov]
    · iapply Henc ptr dq req
      iframe
      iintro Hreq %bs %Hbs
      iframe
      rw [nodeSpec_Back]
      iexists req, L
      iframe
      isplitr
      · ipureintro; exact ⟨Hbs, hreq⟩
      isplit
      · iintro %resp %rbs %Hrbs Hi Hcm %Hcv %_
        iexists resp
        iframe
        ipureintro; exact ⟨Hrbs, Hcv⟩
      · unfold errOk; iintro %_ %Hne %Heq; exact absurd Heq Hne
    isplitl [«$r0» Hmp]
    · iframe
    · imodintro
      iintro ⟨Hrp, Hmp⟩ %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hok
      iexact Hok
  iintro %err Hpost
  icases Hpost with (⟨%Herr, Hreq, %rep, HΦ', Hok⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, Hreq, -, -⟩ | ⟨%Herr, #Hany, Hrest⟩)
  · ispecialize HΦ' $$ %rfl
    icases HΦ' with ⟨%resp, %Hresp, Hi, Hcm, %Hcv⟩
    simp only [ite_true]
    icases Hok with ⟨%resp', Hrp, %Hr'⟩
    obtain rfl := Hr' resp Hresp
    subst Herr
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iframe
    ipureintro; exact Hcv
  · subst Herr
    unfold net.rpc.serverErr
    wp_auto
    iapply HΦ
    iright; iapply errMsg_errAny; iexact Hmsg
  · rcases err with e | _
    · wp_auto
      iapply HΦ
      iright; iexact Hany
    · exact absurd rfl Herr.1


/-- `Close`. -/
theorem wp_Close (cfg : Cfg GF) (c cl : Loc) (a : GoString) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    ∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Close" #c)) (Val #())) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %Φ HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply rcs.close r cfg.W a $$ [Hrpkg Hr] as %err -
  · iexact Hr
  iapply HΦ

/-- A connected node client meets `isNodeClient`. -/
theorem isNodeClient_of
    (HencE : enc_EmptyArgs.spec (GF := GF)) (HencW : enc_WriteArgs.spec (GF := GF))
    (HencC : enc_CommitArgs.spec (GF := GF)) (HencS : enc_string.spec (GF := GF))
    (HencM : enc_NodeMeta.spec (GF := GF)) (HencP : enc_PropagateRequest.spec (GF := GF))
    (HdecE : dec_EmptyReply.spec (GF := GF)) (HdecV : dec_VersionResponse.spec (GF := GF))
    (HdecI : dec_Item.spec (GF := GF)) (HdecP : dec_PropagateResponse.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) (a : GoString) (ha : a ∈ cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ connected cfg cl a ⊢
    isNodeClient cfg (interface.mkOk (go.GoType.PointerType transport.netrpc.NodeClient.ty) #c) a := by
  iintro #H
  unfold isNodeClient
  iexists ⟨go.GoType.PointerType transport.netrpc.NodeClient.ty, #c⟩
  isplitr
  · ipureintro; exact ⟨rfl, ha⟩
  imodintro
  isplit
  · iapply wp_Ping HencE HdecE cfg c cl a ha $$ H
  isplit
  · iapply wp_Write HencW HdecE cfg c cl a ha $$ H
  isplit
  · iapply wp_Commit HencC HdecE cfg c cl a ha $$ H
  isplit
  · iapply wp_LatestVersion_fixed HencS HdecV cfg c cl a ha $$ H
  isplit
  · iapply wp_Read HencS HdecI cfg c cl a ha $$ H
  isplit
  · iapply wp_Update_fixed HencM HdecE cfg c cl a ha $$ H
  isplit
  · iapply wp_FwdPropagate_fixed HencP HdecP cfg c cl a ha $$ H
  isplit
  · iapply wp_BackPropagate_fixed HencP HdecP cfg c cl a ha $$ H
  · iapply wp_Close cfg c cl a $$ H

end proofs
end netrpcP
end github_com.despreston.go_craq
end Perennial
