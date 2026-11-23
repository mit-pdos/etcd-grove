/-
The craq kit's client machines and orchestrator (kit.go's `Sys.end`, `Sys.readAt`, `Sys.remove`,
`op`, `newSys`, `Client`, `Orch`; lab `Kit/Op.lean`, `New.lean`, `Client.lean`), in paxos's shape
(`paxosnet/KitProof.lean`): the specs of other packages are theorem arguments, discharged at the
top level (`awaitConf.spec`, `configure.spec`: ConfProof.lean's `wp_awaitConf`, `wp_configure`
applied to the net specs).

* A client machine's `Sys` (`sysOk`): its configuration's fields read-only, its mutex over
  `endedInv` (some count). remote's `newClient` returns the `Sys` made before `ServeClient`
  (`tok sys := ⌜sys = s⌝`; everything else `op` needs is persistent).
* `op`: a put is the coordinator's `Write` (`putReceipt`), a get the `Read` of chain machine
  `readAt(c)` (2..6, an address of the chain: `cfgKit`), whose `notFoundMsg` ServerError is a
  not-found; any other error is `Out{Unknown: true}`. Linearization: `lin_opAU`.
* `newSys`: `awaitConf` in a goroutine, `<-ch` (`msgOk`), `Register()` (ServerProof.lean's
  `wp_Register` over the machine's fresh codec registry `codecFresh`, which gives `rpcReady`),
  `go s.remove(rs)`.
* `Orch`: remote's `Check`, whose premises on the store (`PendDec (kvR γ) kvS`, the outputs'
  bytes injective) are `ModelDefs.lean`'s `kvS_pendDec`, `kvR_encOut_inj` (finding F4: a put's
  success and a get's not found are one output, `got none`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.New
public import Net.Spec.net.rpc.SetCodec
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ConfProof
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitSpecs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.time.Link
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.despreston.go_craq github_com.despreston.go_craq.netrpcP

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions]
variable [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF] [bvi : go.BasicIntoValInj] [ρ : RemoteGS]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- `s`'s lock invariant: some count of ended operations. -/
def endedInv (s : Loc) : IProp GF :=
  iprop(∃ n : w64, structFieldRef Sys go!"ended" s ↦ n)

/-- `s` is a client machine's `Sys` with the accepted configuration `conf` (persistent). -/
def sysOk (s : Loc) (conf : Conf) : IProp GF :=
  iprop(structFieldRef Conf go!"N" (structFieldRef Sys go!"conf" s) ↦□ conf.N' ∗
    structFieldRef Conf go!"Late" (structFieldRef Sys go!"conf" s) ↦□ conf.Late' ∗
    structFieldRef Conf go!"ReadTail" (structFieldRef Sys go!"conf" s) ↦□ conf.ReadTail' ∗
    ⌜confOk conf⌝ ∗
    sync.isMutex (structFieldRef Sys go!"mu" s) (endedInv s))

instance sysOk_persistent (s : Loc) (conf : Conf) : Persistent (sysOk (hG := hG) s conf) := by
  unfold sysOk; infer_instance

theorem wp_Sys_end (s : Loc) (conf : Conf) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sysOk s conf }}
      (App (Val (s @!! go.GoType.PointerType Sys.ty @!! go!"end")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hs
  unfold sysOk
  icases Hs with ⟨-, -, -, %Hok, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  unfold endedInv
  icases Hi with ⟨%n, Hn⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hn]
  · iexists _; iframe
  iapply HΦ; itrivial

theorem N_ne0 (N : w64) (h : 3 ≤ uint.Z N) : ¬ uint.Z N = 0 := by omega

theorem readAt_mod (c N : w64) (h3 : 3 ≤ uint.Z N) (h5 : uint.Z N ≤ 5) :
    2 ≤ uint.Z (W64 2 + c % N) ∧ uint.Z (W64 2 + c % N) ≤ 6 := by
  have hN : N ≠ 0#64 := by intro h; subst h; exact absurd h3 (by decide)
  have hlt : c % N < N := BitVec.umod_lt c (by
    rw [BitVec.lt_def]; have : N.toNat ≠ 0 := fun h => hN (BitVec.eq_of_toNat_eq h); simp; omega)
  have hlt' : uint.Z (c % N) < uint.Z N := by word
  constructor <;> word

/-- `s.readAt(c)`: a chain machine, `2..6`. -/
theorem wp_Sys_readAt (s : Loc) (conf : Conf) (c : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sysOk s conf }}
      (App (Val (s @!! go.GoType.PointerType Sys.ty @!! go!"readAt")) (Val #c))
    {{ (r : w64), RET #r; ⌜2 ≤ uint.Z r ∧ uint.Z r ≤ 6⌝ }} := by
  wp_start as #Hs
  unfold sysOk
  icases Hs with ⟨#HN, #HL, #HR, %Hok, #Hmu⟩
  unfold confOk at Hok
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro
    constructor <;> word
  · simp only [N_ne0 conf.N' Hok.1, ↓reduceIte]
    wp_auto
    iapply HΦ
    ipureintro
    exact readAt_mod c conf.N' Hok.1 Hok.2.1

/-- The output `op` returns, boxed: an output of the store with `Φ` of it, or unknown. -/
def opPost (_γ : CraqNames) (Φ : KOut → IProp GF) (o : Out) : IProp GF :=
  iprop((∃ o' : KOut, ⌜interface.mkOk Out.ty #o = ovK o'⌝ ∗ Φ o') ∨ ⌜o = Out.mk true false []⌝)

/-- `op(s, c, x)`: through the coordinator's `Write` (a put) or chain machine `readAt(c)`'s
`Read` (a get); linearized by `lin_opAU`. -/
theorem wp_op
    (wp_NewNC : netrpc.wp_NewNodeClient.spec (GF := GF))
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) (s : Loc) (conf : Conf) (c : w64) (i : KIn)
    (Ψ : KOut → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ craqCtx cfg ∗ rpcReady ∗ sysOk s conf ∗
        slotUpd (Gg := hG.goose_globalGS) (kvR cfg.γ) i Ψ }}
      (App (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.op)) (Val #s))
        (Val #c)) (Val #(inOf i)))
    {{ (o : Out), RET #o; opPost cfg.γ Ψ o }} := by
  wp_start as ⟨#Hctx, #Hrdy, #Hs, Hupd⟩
  ihave #Hnp : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc $$ []
  · iPkgInit
  obtain ⟨k | ⟨k, x⟩, hi⟩ := i
  · -- a get
    rw [slotUpd_read _ rfl]
    icases Hupd with #Hupd
    ihave HAU := lin_opAU cfg.γ _ Ψ $$ Hupd
    wp_auto
    wp_apply wp_NewNC cfg as %nc Hnc
    · isplitr
      · iexact Hrdy
      · iexact Hctx
    unfold freshNodeClient
    icases Hnc with ⟨%e, %He, Hconn⟩
    subst He
    wp_apply wp_ServerAddrs as %sl Hsl
    wp_apply wp_Sys_readAt s conf c $$ [] as %r %Hr
    · iframe #
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    have hsl : sint.Z sl.len = 6 := by
      have := Hsll.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
    have hidx : sint.Z (r - W64 1) = uint.Z r - 1 := by word
    obtain ⟨a, ha, hmem⟩ := serverAddrs_chain (sint.Z (r - W64 1)).toNat (by omega) (by omega)
    rw [ite_eq_left ⟨by omega, by omega⟩]
    wp_apply wp_load_slice_index sl (sint.Z (r - W64 1)) serverAddrs _ a (by omega) $$ [Hsl]
      with Hsl
    · iframe; ipureintro; exact ha
    rw [← hcfg.2] at hmem
    wp_bind (App (Val #(methods e.ty go!"Connect" e.v)) (Val #a))
    iapply Hconn $$ %a [] 
    · ipureintro; exact hmem
    inext
    iintro %err Herr
    icases Herr with (⟨%Herr, #Hnc⟩ | #Herr)
    · subst Herr
      wp_auto
      unfold isNodeClient
      icases Hnc with ⟨%e', ⟨%He', -⟩, #Hm⟩
      cases He'
      icases Hm with ⟨-, -, -, -, #HR, -, -, -, #HC⟩
      wp_bind (App (Val #(methods e.ty go!"Read" e.v)) (Val #k))
      iapply HR $$ HAU
      inext
      iintro %k' %vsl %err2 Herr2
      wp_auto
      wp_bind (App (Val #(methods e.ty go!"Close" e.v)) (Val #()))
      iapply HC
      inext
      iintro %err3
      icases Herr2 with (⟨%Herr2, %xv, %σ, Hv, ⟨%o', %Ho', HΨ⟩, %Hσ⟩ |
        ⟨%Herr2, %σ, ⟨%o', %Ho', HΨ⟩, %Hσ⟩ | %Herr2)
      · subst Herr2
        wp_auto
        wp_apply wp_bytes_to_string $$ [Hv] as Hv
        · iexact Hv
        iapply HΦ
        unfold opPost
        ileft
        iexists o'
        iframe HΨ
        ipureintro
        rw [Hσ] at Ho'
        rcases o' with (_ | ⟨w, hw⟩) | _ <;> simp only [liftOut, isPut, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, KvOutput.got.injEq, Option.map_none,
          Option.map_some, reduceCtorEq, Option.some.injEq] at Ho'
        subst Ho'
        rfl
      · subst Herr2
        wp_auto
        iapply HΦ
        unfold opPost
        ileft
        iexists o'
        iframe HΨ
        ipureintro
        rw [Hσ] at Ho'
        rcases o' with (_ | ⟨w, hw⟩) | _ <;> simp only [liftOut, isPut, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte, KvOutput.got.injEq, Option.map_none,
          Option.map_some, reduceCtorEq] at Ho'
        rfl
      · obtain ⟨hnil, hnf, hns | ⟨msg, rfl⟩⟩ := Herr2
        · cases err2 with
          | nil => exact absurd rfl hnil
          | ok e2 =>
          have hty := hns e2 rfl
          wp_auto
          simp only [hty, ↓reduceIte, decide_false]
          wp_auto
          iapply HΦ
          unfold opPost
          iright
          ipureintro; rfl
        · have hmsg : msg ≠ notFoundMsg := fun h => hnf (by rw [h])
          wp_auto
          have hmsg' : decide (msg = notFoundMsg) = false := decide_eq_false hmsg
          unfold notFoundMsg at hmsg'
          rw [hmsg']
          wp_auto
          iapply HΦ
          unfold opPost
          iright
          ipureintro; rfl
    · unfold models_lab.errAny
      icases Herr with ⟨%e2, %He2, -⟩
      subst He2
      wp_auto
      iapply HΦ
      unfold opPost
      iright
      ipureintro; rfl
  · -- a put
    rw [slotUpd_write _ rfl]
    ihave HAU := lin_opAU cfg.γ _ Ψ $$ Hupd
    wp_auto
    wp_apply wp_NewCC cfg as %cc Hcc
    · isplitr
      · iexact Hrdy
      · iexact Hctx
    unfold freshCoordClient
    icases Hcc with ⟨%e, %He, Hconn⟩
    subst He
    wp_apply wp_ServerAddrs as %sl Hsl
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    have hsl : sint.Z sl.len = 6 := by
      have := Hsll.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
    rw [ite_eq_left ⟨by word, by rw [hsl]; word⟩]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) serverAddrs _ cfg.cAddr (by word) $$ [Hsl]
      with Hsl
    · iframe; ipureintro; rw [hcfg.1]; rfl
    wp_bind (App (Val #(methods e.ty go!"Connect" e.v)) (Val #cfg.cAddr))
    iapply Hconn
    inext
    iintro %err Herr
    icases Herr with (⟨%Herr, #Hcc⟩ | #Herr)
    · subst Herr
      wp_auto
      unfold isCoordClient
      icases Hcc with ⟨%e', %He', #Hm⟩
      cases He'
      icases Hm with ⟨-, #HW, #HC, -⟩
      wp_apply wp_string_to_bytes as %bsl ⟨Hbsl, -⟩
      wp_bind (App (App (Val #(methods e.ty go!"Write" e.v)) (Val #k)) (Val #bsl))
      iapply HW $$ Hbsl HAU
      inext
      iintro %err2 Herr2
      wp_auto
      wp_bind (App (Val #(methods e.ty go!"Close" e.v)) (Val #()))
      iapply HC
      inext
      iintro %err3
      icases Herr2 with (⟨%Herr2, -, HR⟩ | #Herr2)
      · subst Herr2
        wp_auto
        iapply HΦ
        unfold putReceipt opPost
        ileft
        icases HR with ⟨%o', %Ho', HΨ⟩
        iexists o'
        iframe HΨ
        ipureintro
        rcases o' with (_ | v) | _ <;> simp only [liftOut, isPut, Option.isNone_none,
          Option.isNone_some, Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          reduceCtorEq, ite_true] at Ho' ⊢
        rfl
      · unfold models_lab.errAny
        icases Herr2 with ⟨%e2, %He2, -⟩
        subst He2
        wp_auto
        iapply HΦ
        unfold opPost
        iright
        ipureintro; rfl
    · unfold models_lab.errAny
      icases Herr with ⟨%e2, %He2, -⟩
      subst He2
      wp_auto
      iapply HΦ
      unfold opPost
      iright
      ipureintro; rfl

theorem node_idx (N n : w64) (h2 : 2 ≤ uint.Z n) (h : uint.Z n ≤ uint.Z N + 1)
    (hN : uint.Z N ≤ 5) :
    0 ≤ sint.Z (n - W64 1) ∧ sint.Z (n - W64 1) < 6 ∧ 1 ≤ (sint.Z (n - W64 1)).toNat ∧
      (sint.Z (n - W64 1)).toNat ≤ 5 := by
  have hidx : sint.Z (n - W64 1) = uint.Z n - 1 := by word
  rw [hidx]; omega

/-- `s.remove(rs)`: each removal asked of the coordinator (`RemoveNode`, any address). -/
theorem wp_Sys_remove [LogHyp GF]
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) (s : Loc) (conf : Conf) (rs : GoSlice)
    (rl : List removal) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ craqCtx cfg ∗ rpcReady ∗ sysOk s conf ∗
        rs ↦* rl ∗ ⌜remsOk conf rl⌝ }}
      (App (Val (s @!! go.GoType.PointerType Sys.ty @!! go!"remove")) (Val #rs))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hctx, #Hrdy, #Hs, Hrs, %Hrl⟩
  ihave #Hnp : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc $$ []
  · iPkgInit
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hrs
  unfold sysOk
  icases Hs with ⟨#HN, #HL, #HR, %Hok, #Hmu⟩
  ihave HI : (∃ (j : w64) (rv : removal),
      "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ rv ∗ "Hrs" ∷ rs ↦* rl ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rs.len⌝ : IProp GF) $$ [i r Hrs]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
    list_elem rl (sint.nat j) as e
    wp_apply wp_load_slice_index rs (sint.Z j) rl _ e Hj.1 $$ [Hrs] with Hrs
    · iframe; ipureintro; exact He_lookup
    (try wp_auto)
    ihave %Hrnn := typedPointsto_not_null _ _ _ $$ r
    icases typedPointsto_split _ _ _ $$ r with r
    try simp only [TypedPointsto.typedPointstoDef]
    icases r with ⟨Client, Node, After, -⟩
    ihave HJ : ("Client" ∷ r_ptr.[removal, go!"Client"] ↦ e.Client' ∗
        "Node" ∷ r_ptr.[removal, go!"Node"] ↦ e.Node' ∗
        "After" ∷ r_ptr.[removal, go!"After"] ↦ e.After' : IProp GF) $$ [Client Node After]
    · iframe
    wp_for HJ
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
    unfold endedInv
    icases Hi with ⟨%n, Hn⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hn]
    · iexists _; iframe
    wp_if_destruct
    · wp_for_post
      wp_apply wp_digit
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %args_sl ⟨Hargs, -⟩
      wp_apply LogHyp.wp_Println _ _ _ $$ [Hargs]
      · iframe
        iapply argOks_of_wf _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
      iintro -
      wp_auto
      have hre : remOk conf e := Hrl.2 e (List.mem_of_getElem? He_lookup)
      have hN5 := Hok.2.1
      unfold remOk at hre
      wp_apply wp_NewCC cfg as %cc Hcc
      · isplitr
        · iexact Hrdy
        · iexact Hctx
      unfold freshCoordClient
      icases Hcc with ⟨%ec, %He, Hconn⟩
      subst He
      wp_apply wp_ServerAddrs as %sl Hsl
      ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
      have hsl : sint.Z sl.len = 6 := by
        have := Hsll.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
      rw [ite_eq_left ⟨by word, by rw [hsl]; word⟩]
      wp_apply wp_load_slice_index sl (sint.Z (W64 0)) serverAddrs _ cfg.cAddr (by word) $$ [Hsl]
        with Hsl
      · iframe; ipureintro; rw [hcfg.1]; rfl
      wp_bind (App (Val #(methods ec.ty go!"Connect" ec.v)) (Val #cfg.cAddr))
      iapply Hconn
      inext
      iintro %err Herr
      icases Herr with (⟨%Herr, #Hcc⟩ | #Herr)
      · subst Herr
        wp_auto
        unfold isCoordClient
        icases Hcc with ⟨%e', %He', #Hm⟩
        cases He'
        icases Hm with ⟨-, -, #HC, #HRN⟩
        wp_apply wp_ServerAddrs as %sl2 Hsl2
        ihave %Hsll2 := ownSlice_len _ _ _ $$ Hsl2
        have hsl2 : sint.Z sl2.len = 6 := by
          have := Hsll2.1; simp only [serverAddrs, List.length_cons, List.length_nil] at this; word
        obtain ⟨h0, h6, h1, h5⟩ := node_idx conf.N' e.Node' hre.1 hre.2.1 hN5
        obtain ⟨a, ha, -⟩ := serverAddrs_chain (sint.Z (e.Node' - W64 1)).toNat h1 h5
        rw [ite_eq_left ⟨h0, by rw [hsl2]; exact h6⟩]
        wp_apply wp_load_slice_index sl2 (sint.Z (e.Node' - W64 1)) serverAddrs _ a h0
          $$ [Hsl2] with Hsl2
        · iframe; ipureintro; exact ha
        wp_bind (App (Val #(methods ec.ty go!"RemoveNode" ec.v)) (Val #a))
        iapply HRN
        inext
        iintro %err4 -
        wp_auto
        wp_bind (App (Val #(methods ec.ty go!"Close" ec.v)) (Val #()))
        iapply HC
        inext
        iintro %err5
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, e
        iframe
        isplitl [Client Node After]
        · iapply typedPointsto_combine _ _ _ Hrnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipureintro; refine ⟨by word, by word⟩
      · unfold models_lab.errAny
        icases Herr with ⟨%e2, %He2, -⟩
        subst He2
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, e
        iframe
        isplitl [Client Node After]
        · iapply typedPointsto_combine _ _ _ Hrnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipureintro; refine ⟨by word, by word⟩
    · wp_apply time.wp_Sleep
      wp_for_post
      simp only [named]
      iframe
  · (try wp_auto)
    iapply HΦ
    itrivial

/-- `newSys(c)`: client machine `c`'s `Sys`, once its configuration arrived; the codec is
registered (`rpcReady`); its removals run in a goroutine. -/
theorem wp_newSys [LogHyp GF]
    (wp_awaitConf : awaitConf.spec (GF := GF) (hG := hG))
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF))
    (cfg : Cfg GF) (hcfg : cfgKit cfg) (c : w64) (hc : uint.nat c < 5) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ craqCtx cfg ∗ codecFresh ∗
        addrProto (Gg := hG.goose_globalGS) (confAddrs.getD (uint.nat c) []) confProto confProto }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.newSys)) (Val #c))
    {{ (s : Loc), RET #s; ∃ conf, sysOk s conf ∗ rpcReady }} := by
  wp_start as ⟨#Hctx, Hcf, #Ha⟩
  wp_auto
  wp_apply wp_make_conf_chan as %ch ⟨%γch, #Hbag⟩
  wp_apply wp_ConfAddrs as %cfgs Hcfgs
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcfgs
  have hcl : sint.Z cfgs.len = 11 := by
    have := Hcl.1; simp only [confAddrs, List.length_cons, List.length_nil] at this; word
  have hcn : uint.nat c < confAddrs.length := by
    simp only [confAddrs, List.length_cons, List.length_nil]; omega
  list_elem confAddrs (uint.nat c) as a
  have hca : a = confAddrs.getD (uint.nat c) [] := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst hca
  rw [ite_eq_left ⟨by word, by rw [hcl]; word⟩]
  wp_apply wp_load_slice_index cfgs (sint.Z c) confAddrs _ _ (by word) $$ [Hcfgs]
    with Hcfgs
  · iframe; ipureintro; rw [show (sint.Z c).toNat = uint.nat c by word]; exact Ha_lookup
  wp_apply wp_fork $$ []
  · wp_apply wp_awaitConf _ γch ch $$ [] as %hf
    · iframe #
    exact hf.elim
  wp_apply wp_recv_msg γch ch $$ [] as %m Hm
  · iframe #
  wp_apply wp_Register wp_SetCodec $$ [Hcf] as #Hcs
  · iframe
  iStructNamed «$r0»
  iStructNamed conf
  unfold msgOk
  icases Hm with ⟨%Hcok, %rl, Hrl, %Hrok⟩
  ipersist N
  ipersist Late
  ipersist ReadTail
  iapply fupd_wp
  imod sync.init_Mutex (endedInv «$r0_ptr») ⊤ _ $$ mu [ended] with #Hmu
  · inext; unfold endedInv; iexists _; iexact ended
  imodintro
  ihave #Hsys : sysOk «$r0_ptr» m.conf' $$ []
  · unfold sysOk
    iframe #
    ipureintro; exact Hcok
  ihave #Hrdy : rpcReady $$ []
  · unfold rpcReady
    isplitr
    · iPkgInit
    · iexact Hcs
  wp_apply wp_fork $$ [Hrl]
  · wp_apply wp_Sys_remove wp_NewCC cfg hcfg «$r0_ptr» m.conf' m.rs' rl $$ [Hrl]
    · iframe #
      iframe
      ipureintro; exact Hrok
    ipureintro; first | rfl | simp
  iapply HΦ
  iexists m.conf'
  iframe #

theorem Client.wp_proof [LogHyp GF]
    (wp_awaitConf : awaitConf.spec (GF := GF) (hG := hG))
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_NewNC : netrpc.wp_NewNodeClient.spec (GF := GF))
    (wp_NewCC : netrpc.wp_NewCoordinatorClient.spec (GF := GF))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := KIn) (O := KOut)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro cfg c hcfg hc
  wp_start as ⟨#Hctx, Hcf, #Hca, #Hra, #Hmap⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_newSys wp_awaitConf wp_SetCodec wp_NewCC cfg hcfg c hc $$ [Hcf]
    as %s ⟨%conf, #Hs, #Hrdy⟩
  · iframe; iframe #
  ipersist s
  ipersist c
  ipersist newClient
  ipersist opc
  wp_apply wp_ClientAddrs as %asl Hasl
  ihave %Hal := ownSlice_len _ _ _ $$ Hasl
  have hal : sint.Z asl.len = 5 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  have hcn : uint.nat c < clientAddrs.length := by
    simp only [clientAddrs, List.length_cons, List.length_nil]; omega
  list_elem clientAddrs (uint.nat c) as a
  have hca : a = clientAddrs.getD (uint.nat c) [] := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst hca
  rw [ite_eq_left ⟨by word, by rw [hal]; word⟩]
  wp_apply wp_load_slice_index asl (sint.Z c) clientAddrs _ _ (by word) $$ [Hasl] with Hasl
  · iframe; ipureintro; rw [show (sint.Z c).toNat = uint.nat c by word]; exact Ha_lookup
  wp_apply (wp_Codec cfg.γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (kvR cfg.γ)) _ _ _ _ cd d
    (fun sys => iprop(⌜sys = interface.mkOk (go.GoType.PointerType Sys.ty) #s⌝)) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Ψ
    iintro !> %Φr ⟨%Hsys, Hupd, -⟩ HΦr
    subst Hsys
    wp_auto
    rw [ivK_inOf i]
    wp_auto
    wp_apply wp_op wp_NewNC wp_NewCC cfg hcfg s conf c i Ψ $$ [Hupd] as %o Ho
    · iframe #
      iframe
    wp_apply wp_Sys_end s conf $$ []
    · iframe #
    iapply HΦr
    isplitr
    · ipureintro; rfl
    unfold opPost
    icases Ho with (⟨%o', %Ho', HΨ⟩ | %Ho)
    · ileft
      iexists o'
      iframe HΨ
      ipureintro; exact Ho'
    · iright
      ipureintro; subst Ho; rfl
  · -- the client's system: its `Sys`
    iintro %Φr HΦr
    wp_auto
    iapply HΦr
    ipureintro; rfl

/-! ## The orchestrator -/

theorem pendN_craq : (↑pendN : CoPset) ⊆ ⊤ \ craqEop := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  unfold craqEop craqN craqNodeN
  rw [LawfulSet.mem_union]
  rintro (h | h)
  · exact ndot_ne_disjoint nroot (show "remote" ≠ "craq" by decide) p ⟨h1, h⟩
  · exact ndot_ne_disjoint nroot (show "remote" ≠ "craq_node" by decide) p ⟨h1, h⟩

theorem lintestN_craq :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (craqEop ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · unfold craqEop craqN craqNodeN
    rw [LawfulSet.mem_union]
    rintro (h | h)
    · exact ndot_ne_disjoint nroot (show "lintest" ≠ "craq" by decide) p ⟨hp, h⟩
    · exact ndot_ne_disjoint nroot (show "lintest" ≠ "craq_node" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

theorem pendCtx_kvS (γ : CraqNames) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS (GF := GF)) γp := rfl

theorem pendLib_kvS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (kvS (GF := GF)) γp (kvS (GF := GF)).M.init := rfl

/-- **Orch**, from `remote.Check`'s spec, with its premises on the store `kvR γ` and its model
`kvS` (`ModelDefs.lean`'s `kvS_pendDec`, `kvR_encOut_inj`). -/
theorem Orch.wp_proof
    (wp_configure : configure.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := St) (I := KIn) (O := KOut)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_kvS, pendLib_kvS]
  wp_start as ⟨#Hra, #Hmap, #Hpend, Hlib, #Hcp, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply wp_choose as %conf %Hconf
  wp_apply wp_plan conf Hconf as %rs ⟨%rl, Hrs, %Hpl⟩
  wp_apply wp_configure conf rs rl _ $$ [Hrs] as Hrs
  · iframe #
    iframe
    ipureintro; exact ⟨Hconf, planOk_len Hpl⟩
  wp_apply time.wp_Sleep
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (wp_Codec γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 5 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (kvR γ) kvS γp m addrs clientAddrs cd _ _ d pendN_craq lintestN_craq
    (kvS_pendDec γ) (kvR_encOut_inj γ) (fun st => kvR_timeless γ st) hrb (by rw [hlen']; decide) (by decide)
    (by rw [hlen']; decide) 18 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := GF)
        (functions github_com.despreston.go_craq.examples.craqnet.Gen [])
        (fun x => iprop(∃ i, ⌜x = (kvR (Gg := hG.goose_globalGS) γ).iv i⌝)) from wp_Gen)
  iapply HΦ
  itrivial

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
