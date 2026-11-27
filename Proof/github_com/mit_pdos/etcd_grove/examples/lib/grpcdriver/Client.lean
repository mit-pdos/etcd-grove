/- Lean-first (no Rocq counterpart).

# `Client`'s proof (the sections concurrent-calls and close)

`NewClient("passthrough:///" + Addr, WithTransportCredentials(insecure))`: the passthrough resolver
reaches `drvAddr`, no interceptor, no per-RPC credentials (`grpcConn`, `connCredsOk conn []`), no
stream interceptor (`grpcConnOpts`); the methods' facts come from the server's table (`grpcAddrAt`),
which gives the client's environment (`drvCli`). The counter of ids (`isCtr`: its mutex over
`ctrInv` at the random start, with `ctrBudget = 33` credits): at most 4 workers, joined by the wait
group's `tokJoin` (as net/rpc's driver's `callOn`), 8 credits each (`work`); then `Close`
(`grpcConnClosed`) and one `Echo` on `Background()` (quiet), which fails with a status of code
`Canceled` (`spec_done`), one credit for its value's id.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Client
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.work
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.freshValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Echo
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.NewDriverClient
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Spec.google_golang_org.grpc.NewClient
public import Spec.google_golang_org.grpc.WithTransportCredentials
public import Spec.google_golang_org.grpc.credentials.insecure.NewCredentials
public import Spec.google_golang_org.grpc.ClientConn__Close
public import Spec.google_golang_org.grpc.status.Code
public import Proof.google_golang_org.grpc.internal.status.Methods
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerServes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerServesStream
public import Perennial.Spec.context.Background
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link
public import Proof.context.LibKeysChain
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The workers' wait group's namespace. -/
def wkN : Namespace := nroot.@"grpcdriver.workers"

theorem drvAddr_passthrough :
    dialPassthrough [GrpcDialOpt.transportCreds] go!"passthrough:///127.0.0.1:7301" [drvAddr] := by
  refine ⟨by simp, drvAddr, by decide, ?_, by decide, rfl⟩
  intro b hb
  simp only [drvAddr, List.mem_cons, List.not_mem_nil, or_false] at hb
  unfold passthroughByteOk
  rcases hb with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

/-- **The client's environment from the server's table and a dial with no interceptor and no
per-RPC credentials.** -/
theorem drvCli_of [hX : HasExt netExt] (π : NetProtoGS) (σ : NetSlotGS) (γid γb : GName)
    (c : GoInterface) (ids conn : Loc) (d : GrpcConnOpts) (hd : d.streamIc = none) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      drvFacts ∗ isCtr γid γb ids ∗ drvStubAt c conn ∗ grpcConn conn [drvAddr] [] [] anyRes ∗
      grpcConnOpts conn d ∗ connCredsOk conn [] (fun _ => iprop(True)) ∗
      grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) drvAddr (drvSvc γid) ⊢
    drvCli γid γb c ids := by
  iintro ⟨#Hpkg, #Hf, #Hctr, #Hstub, #Hconn, #Hopts, #Hcreds, #Haddr⟩
  unfold drvCli
  iframe #
  isplitr
  · iapply (isGrpcRpcMd_of_addr (Req := (pbStringValueT (GF := GF)).toProtoMsg)
      (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr echoName (drvSvc γid) _ _
      (drvSvc_echo γid)) $$ Haddr
  isplitr
  · iapply (isGrpcRpcMd_of_addr (Req := (pbStringValueT (GF := GF)).toProtoMsg)
      (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr failName (drvSvc γid) _ _
      (drvSvc_fail γid)) $$ Haddr
  isplitr
  · iapply (isGrpcRpcMd_of_addr (Req := (pbStringValueT (GF := GF)).toProtoMsg)
      (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr metaName (drvSvc γid) _ _
      (drvSvc_meta γid)) $$ Haddr
  unfold drvStrmFacts
  imodintro
  isplitr
  · iexists d; iframe #; ipureintro; exact hd
  isplitr
  · iapply (isGrpcStreamMd_of_addr (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
      drvAddr serverStreamName (drvSvc γid) ssUp ssDn (strmSpec ssDn) (drvSvc_serverStream γid))
    iframe Haddr
    iapply strmSpec_self
  isplitr
  · iapply (isGrpcStreamMd_of_addr (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
      drvAddr clientStreamName (drvSvc γid) csUp csDn (strmSpec csDn) (drvSvc_clientStream γid))
    iframe Haddr
    iapply strmSpec_self
  iapply (isGrpcStreamMd_of_addr (Req := strmMsg (GF := GF)) (Rep := strmMsg (GF := GF))
    drvAddr bidiName (drvSvc γid) biUp biDn (strmSpec biDn) (drvSvc_bidi γid))
  iframe Haddr
  iapply strmSpec_self

theorem Client.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_work : work.spec (GF := GF) (hG := hG))
    (wp_freshValue : freshValue.spec (GF := GF) (hG := hG))
    (wp_EchoDone : svc.driverClient.Echo.spec_done (GF := GF) (hG := hG))
    (wp_NewDriverClient : svc.NewDriverClient.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (wp_NewCredentials : insecure.NewCredentials.spec (GF := GF) (hG := hG))
    (wp_WithTC : grpc.WithTransportCredentials.spec (GF := GF) (hG := hG))
    (wp_NewClient : grpc.NewClient.spec (GF := GF) (hG := hG))
    (wp_Close : grpc.ClientConn.Close.spec (GF := GF) (hG := hG))
    (wp_Code : status.Code.specNE (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro hX π σ γid
  wp_start as ⟨%Hb, Htok, #Hpkg, #Haddr, Hauth⟩
  ihave #Hf := drvFacts_of_init $$ Hpkg
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hins : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure $$ []
  · iPkgInit
  ihave #Hsvc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hf' := Hf
  iunfold drvFacts at Hf'
  icases Hf' with ⟨%fr, #Hrg, #Hrf⟩
  try wp_auto
  wp_apply wp_NewCredentials as %cr -
  wp_apply wp_WithTC cr as %o #Ho
  wp_apply wp_slice_literal (V := GoInterface) [o]
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  imod ownSlice_persist _ _ _ $$ Hosl with #Hosl
  try wp_auto
  wp_apply wp_NewClient go!"passthrough:///127.0.0.1:7301" _ [GrpcDialOpt.transportCreds]
      GoInterface.nil [] [drvAddr] anyRes (fun _ => iprop(True)) $$ []
    as %conn %err Hd
  · iframe #
    isplitr
    · iunfold dialOptsAt
      iexists [o]
      iframe Hosl
      iapply BigSepL2.bigSepL2_singleton.2; iexact Ho
    isplitr
    · iunfold dialTargetOk
      iright
      ipureintro; exact drvAddr_passthrough
    rw [show credsOfDial [GrpcDialOpt.transportCreds] = [] from rfl]
    iapply BigSepL.bigSepL_nil.2; itrivial
  icases Hd with (⟨%He, #Hconn, #Hcreds, #Hopts⟩ | %He)
  simp only [show unaryIcsOf [GrpcDialOpt.transportCreds] = [] from rfl,
    show credsOfDial [GrpcDialOpt.transportCreds] = [] from rfl]
  rotate_left
  · cases err with
    | nil => exact absurd rfl He
    | ok e =>
      try wp_auto
      iapply HΦ
      iexact Htok
  subst He
  try wp_auto
  wp_apply wp_NewDriverClient as %c ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  try wp_auto
  wp_apply wp_RandomUint64 as %start -
  try wp_auto
  irename «$r0» => Hcn
  generalize «$r0_ptr» = cn at *
  icases typedPointsto_split _ _ _ $$ Hcn with Hcn
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hcn with ⟨mu, next, -⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γb, Hba⟩
  imod ownTokAuth_add ctrBudget γb 0 $$ Hba with ⟨Hba, Hcred⟩
  imod sync.init_Mutex (ctrInv γid γb start cn) ⊤ (structFieldRef counter go!"mu" cn)
    $$ mu [next Hauth Hba] with #Hmu
  · inext
    unfold ctrInv
    iexists 0, 0 + ctrBudget
    rw [show start + W64 ((0 : Nat) : Int) = start by word]
    iframe
    ipureintro; omega
  ihave #Hctr : isCtr γid γb cn $$ []
  · unfold isCtr; iframe Hsync; iexists start; iexact Hmu
  ihave #Hcli : drvCli γid γb (interface.mkOk (go.GoType.PointerType svc.driverClient.ty) #dc) cn $$ []
  · ihave #Hstub : drvStubAt (GF := GF) (interface.mkOk (go.GoType.PointerType svc.driverClient.ty) #dc) conn $$ []
    · unfold drvStubAt; iexists dc; iframe #; ipureintro; rfl
    iapply (drvCli_of π σ γid γb _ cn conn (connOptsOf [GrpcDialOpt.transportCreds]) rfl)
    iframe #
  -- the credits: 32 for the workers, 1 for the call after `Close`
  rw [show ctrBudget = 32 + 1 from rfl]
  icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, Hc1⟩
  -- the variables the workers read (captured by their closure, never written after): shared
  ipersist ids
  ipersist c
  irename wg => Hwg0
  icases typedPointsto_not_null_dup _ _ _ $$ Hwg0 with ⟨Hwg0, %Hwgnn⟩
  imod sync.init_WaitGroup (wkN.@"wg") wg_ptr $$ Hwg0 with ⟨%γwg, #Hiswg, Hctr0, Hwait⟩
  ihave #Hlaw := sync.tokJoin.lendLaw_false (GF := GF) wkN
  imod sync.tokJoin.init wkN iprop(False) wg_ptr γwg ⊤ Hb $$ [$Hiswg $Hctr0 $Hwait $Hlaw] with Hadd
  wp_apply wp_below (W64 4) as %w0 %Hw0
  have hw0 : uint.Z w0 < 4 := Hw0.2 (by decide)
  try wp_auto
  have hN : uint.nat (W64 1 + w0) ≤ 4 := by word
  ihave Hcred : ownToks γb (8 * uint.nat (W64 1 + w0) + (32 - 8 * uint.nat (W64 1 + w0))) $$ [Hcred]
  · rw [show 8 * uint.nat (W64 1 + w0) + (32 - 8 * uint.nat (W64 1 + w0)) = 32 by omega]
    iexact Hcred
  icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, -⟩
  ihave IH : iprop(∃ (w : w64) (n : Nat) (Pw : IProp GF), "w" ∷ w_ptr ↦ w ∗
      "Hadd" ∷ sync.tokJoin.ownAdder wkN iprop(False) wg_ptr n Pw ∗ "Htok" ∷ threadTok ∗
      "Hcred" ∷ ownToks γb (8 * (uint.nat (W64 1 + w0) - uint.nat w)) ∗
      "%Hw" ∷ ⌜uint.nat w ≤ uint.nat (W64 1 + w0)⌝) $$ [w Hadd Htok Hcred]
  · iexists W64 0, 0, iprop(True)
    iframe w Hadd Htok
    rw [show uint.nat (W64 0) = 0 by rfl, Nat.sub_zero]
    iframe Hcred
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · -- a worker
    have hw : uint.nat w < uint.nat (W64 1 + w0) := by
      first | word | (simp at Hif; word) | (simp at Hif; omega)
    rw [show 8 * (uint.nat (W64 1 + w0) - uint.nat w) =
      8 * (uint.nat (W64 1 + w0) - uint.nat (w + W64 1)) + 8 by
        rw [show uint.nat (w + W64 1) = uint.nat w + 1 by word]; omega]
    icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, H8⟩
    try wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Add iprop(True) wkN iprop(False) wg_ptr n Pw)
      $$ [$Hsync $Hadd $Htok] as ⟨Hadd, Hdone⟩
    wp_bind (Fork _)
    iapply wp_fork_tok_self $$ [Hdone H8]
    · inext
      try wp_auto
      wp_apply wp_with_defer as %defer Hdefer
      try wp_auto
      wp_apply wp_work γid γb _ cn $$ [$Hcli $H8]
      try wp_auto
      wp_apply (sync.tokJoin.WaitGroup.wp_Done wkN iprop(False) wg_ptr iprop(True))
        $$ [$Hsync $Hdone] as Htok
      try wp_auto
      iframe Htok
    · inext
      iintro Htok
      try wp_auto
      wp_for_post
      iframe
      iexists w + W64 1, n + 1, iprop(Pw ∗ True)
      iframe
      ipureintro; word
  · try simp only [Hif, decide_true, ↓reduceIte]
    try wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Wait wkN iprop(False) wg_ptr n Pw) $$ [$Hsync $Hadd]
      as ⟨-, -⟩
    try wp_auto
    try wp_bind (App (Val #fr) (Val _))
    iapply wp_wand $$ (Hrf $$ %go!"concurrent-calls")
    iintro %v %Hv
    subst Hv
    try wp_auto
    wp_apply wp_Close conn [drvAddr] [] [] anyRes $$ [] as %e2 #Hclosed
    · iexact Hconn
    try wp_auto
    wp_apply wp_Background
    try wp_auto
    wp_apply wp_freshValue γid γb cn $$ [$Hpkg $Hctr $Hc1] as %v ⟨%id, %wd, %Hv, -⟩
    obtain ⟨rfl, hwd⟩ := Hv
    have hlen := mkVal_length id wd hwd
    try wp_auto
    wp_apply wp_String stringValueReqMax (mkVal id wd) (by unfold stringValueReqMax; omega)
      as %inp -
    try wp_auto
    let cd : context.ContextDesc (IProp GF) :=
      { Values := ∅, Deadline := none, Done_gn := ⟨γid, γid⟩, PDone := iprop(True) }
    ihave #Hq : ctxQuiet (GF := GF) context.backgroundCtxVal $$ []
    · iapply drv_ctxQuiet_background
    ihave #Hok : ctxOk context.backgroundCtxVal cd $$ []
    · iapply ctxOk_of_quiet
      iframe #
      iapply metadata.outgoingCtxOkC_background
    wp_apply (wp_EchoDone dc conn [drvAddr] context.backgroundCtxVal cd inp slice.nil []) $$ []
      as %resp %err2 ⟨-, #Hse, #Hcode⟩
    · iframe #
      isplitl []
      · iapply metadata.outMD_background
      isplitl []
      · iapply (ownSlice_nil (V := GoInterface) DFrac.discard)
      ipureintro; intro v hv; cases hv
    try wp_auto
    ihave %hne := statusCodeIs_notEtcd _ (W32 1) (Or.inl ⟨by decide, by decide⟩) $$ Hcode
    wp_apply wp_Code err2 (W32 1) hne $$ []
    · iframe #
    try wp_auto
    try wp_bind (App (Val #fr) (Val _))
    iapply wp_wand $$ (Hrf $$ %go!"close")
    iintro %u %Hu
    subst Hu
    try wp_auto
    iapply HΦ
    iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
