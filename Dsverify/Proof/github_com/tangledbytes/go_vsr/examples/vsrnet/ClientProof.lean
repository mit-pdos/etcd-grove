/-
Client machine `c`'s program (`kit.go`'s `Client`, notes/dsv-vr.md): `mkClient(Addrs(),
waitConf(CfgAddrs(), 1 + c), c)`, then `remote.ServeClient(c, ClientAddrs()[c], newClient, Op,
Codec(), attempt())` with `newClient` returning the system made before.

**Not against remote's `ServeClient.spec`**, which cannot be met here, for two reasons (findings,
notes/dsv-vr.md):
1. its `newClient` premise is a persistent triple with precondition `True`, so `tok sys` must be
   made from nothing any number of times, while the client's system is exclusive (its go-vsr
   client's request numbers, the ghost layer's counter); `ServeClient` calls `newClient` once.
2. its operation premise (`svcOp`) is for unboundedly many calls with the same `tok`, while each
   `Op` registers a request with the ghost layer, whose budget is below 2^28 requests per client
   (`ghost_register`, `RegBound`: what bounds every message's line); nothing in remote's protocol
   bounds the calls a client machine serves (`reqP` admits any number of slots).

`ServeClientB.spec` states the contract remote would give with both changed: `newClient`'s call
once (its WP, a resource), and a budget `K` of calls (`svcOpB`: `tok (k + 1)` to `tok k`). It is
**not proved by remote** (and not provable from `Serve`'s loop without a budget in its protocol); it
is a premise of `Client.wp_proof` only, so that the rest of the client machine is proved.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.MkClientProof
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- The far side's operation `op` with a budget: from `tok (k + 1) sys` and the update of `i`, it
returns an output with `Φ` of it, or an answer that is not one, and `tok k sys`. -/
def svcOpB {I O : Type} [Pos.Countable I] [Pos.Countable O] (S : RSvc GF I O)
    (tok : Nat → GoInterface → IProp GF) (op : GoFunc) : IProp GF :=
  iprop(∀ (k : Nat) (sys : GoInterface) (i : I) (Φ : O → IProp GF),
    {{ tok (k + 1) sys ∗ S.upd i Φ }}
      (App (App (Val #op) (Val #sys)) (Val #(S.iv i)))
    {{ (v : GoInterface), RET #v; tok k sys ∗ ((∃ o, ⌜v = S.ov o⌝ ∗ Φ o) ∨ ⌜S.unkAns i v⌝) }})

/-- **Not remote's** (see the file header): `ServeClient` with `newClient` called once and a
budget of `K` calls of `op`. -/
abbrev ServeClientB.spec : Prop :=
  ∀ {I O : Type} [Pos.Countable I] [Pos.Countable O] (S : RSvc GF I O) (c : w64) (a : GoString)
    (newClient op : GoFunc) (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec) (d : w64) (tok : Nat → GoInterface → IProp GF)
    (K : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗
      svcAddr (Gg := hG.goose_globalGS) S a ∗ wireOk S cd ∗ svcOpB S tok op ∗
      WP (App (Val #newClient) (Val #c)) {{ v, ∃ sys : GoInterface, ⌜v = #sys⌝ ∗ tok K sys }} }}
    (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient))
      (Val #c)) (Val #a)) (Val #newClient)) (Val #op)) (Val #cd)) (Val #d))
  {{ RET #(); False }}

/-- Client `c`'s system with `k` calls left: its counter `n` leaves room for `k` registrations. -/
def sysTok (γ : Names) (c : Nat) (k : Nat) (sys : GoInterface) : IProp GF :=
  iprop(∃ n : Nat, ⌜n + k < 2 ^ 28⌝ ∗ sysRes γ c sys n)

/-- `Op` meets the budgeted contract over `sysTok`. -/
theorem Op_svcOpB (wp_Op : Op.spec (GF := GF) (hG := hG)) (γ : Names) (c : Nat) (hc : c < 6) :
    isPkgInit (PROP := IProp GF) kpkg ⊢
      svcOpB (RBase.svc (Gg := hG.goose_globalGS) (kvR γ.gn)) (sysTok γ c)
        (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Op []) := by
  unfold svcOpB
  iintro #Hpkg %k %sys %i %Ψ
  iintro !> %Φ ⟨Htok, HU⟩ HΦ
  unfold sysTok
  icases Htok with ⟨%n, %hn, Hres⟩
  iapply (wp_Op γ c n sys i Ψ hc (by omega)) $$ [Hres HU]
  · isplitr
    · iexact Hpkg
    isplitl [Hres]
    · iexact Hres
    iexact HU
  iintro !> %v ⟨%n', %hn', Hres, Hv⟩
  iapply HΦ
  isplitl [Hres]
  · iexists n'
    iframe
    ipureintro; omega
  icases Hv with (⟨%o, %Ho, HΨ⟩ | %Hv)
  · ileft; iexists o; iframe; ipureintro; exact Ho
  · iright; ipureintro; exact Hv

/-- `Client(c)`: client machine `c`; it never returns. Its share of the start: the configuration
addresses' and go-vsr addresses' protocols, the ghost layer's invariants, client `c + 1`'s request
counter, the packages' states (`pkgStates`), and its address serving the far side's store. -/
abbrev Client.spec : Prop :=
  ∀ (γ : Names) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ confProtos (G := hG.goose_globalGS) γ ∗
      pkg.network.netProtos γ ∗ sysInv (G := hG.goose_globalGS) γ ∗
      regInv (G := hG.goose_globalGS) γ ∗ nextReq (G := hG.goose_globalGS) γ (c + 1) 1 ∗
      pkgStates ∗ remoteAddr (Gg := hG.goose_globalGS) (kvR γ.gn) (clientAddrs.getD c []) }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Client)) (Val #(W64 (c : Int))))
  {{ RET #(); False }}

theorem Client.wp_proof
    (conn_readerOk : connReaderOk (GF := GF) (hG := hG))
    (wp_NewTCP : pkg.network.NewTCP.spec (GF := GF) (hG := hG))
    (wp_New : log.slog.New.spec (GF := GF) (hG := hG))
    (wp_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG))
    (codec_ok : vsrnet.codecOk (GF := GF) (hG := hG))
    (wp_Op : Op.spec (GF := GF) (hG := hG))
    (wp_ServeClientB : ServeClientB.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γ c hc
  wp_start as ⟨#Hcp, #Hnp, #HsysI, #HregI, Hnext, #Hst, #Hra⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  ihave #Hkit : encoding.json.kitCodecOk (GF := GF) vsrnet.scanF $$ []
  · have hk := codec_ok
    unfold vsrnet.codecOk at hk
    iapply hk
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
  imodintro
  wp_apply CfgAddrs.wp_proof as %cfgs Hcfgs
  wp_apply (waitConf.wp_proof net.Listen.wp_proof net.Listener.Accept.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof conn_readerOk γ cfgs
    (DFrac.own 1) (W64 1 + W64 (c : Int)) (by word)) $$ [Hcfgs] as %cf ⟨-, #Hcf⟩
  · iframe; iframe #
  wp_apply (mkClient.wp_proof wp_NewTCP wp_New wp_Discard γ c asl cf hc) $$ [Hnext] as %x Hres
  · iframe; iframe #
  wp_apply wp_ClientAddrs as %casl Hcasl
  ihave %Hal := ownSlice_len _ _ _ $$ Hcasl
  have hal : clientAddrs.length = 6 := rfl
  have hb : 0 ≤ sint.Z (W64 (c : Int)) ∧ sint.Z (W64 (c : Int)) < sint.Z casl.len := by
    rw [hal] at Hal; constructor <;> word
  rw [ite_eq_left hb]
  list_elem clientAddrs c as a
  wp_apply wp_load_slice_index casl (sint.Z (W64 (c : Int))) clientAddrs _ a hb.1 $$ [Hcasl]
    as Hcasl
  · iframe
    ipureintro
    rw [show (sint.Z (W64 (c : Int))).toNat = c by word]
    exact Ha_lookup
  have ha : a = clientAddrs.getD c [] := by simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst ha
  wp_auto
  wp_apply (Codec.wp_proof γ.gn) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply (wp_ServeClientB (RBase.svc (Gg := hG.goose_globalGS) (kvR γ.gn)) (W64 (c : Int))
    (clientAddrs.getD c []) _ (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Op []) cd d
    (sysTok γ c) (2 ^ 28 - 2)) $$ [Hres sys] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplitl []
  · iapply (Op_svcOpB wp_Op γ c hc) $$ Hpkg
  -- `newClient(c)`: the system made before
  wp_auto
  iexists interface.mkOk (go.GoType.PointerType Sys.ty) #x
  isplitr
  · ipureintro; rfl
  unfold sysTok
  iexists 1
  iframe
  ipureintro
  decide

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
