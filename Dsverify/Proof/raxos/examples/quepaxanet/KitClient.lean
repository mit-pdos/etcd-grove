/-
`Client(c)` (`kit.go`), client machine `c`'s program: its QuePaxa client (`newClient`, once,
before serving), then `remote.ServeClient` whose `newClient` returns that client (`tok sys`: the
client's `*Sys`, whose facts `isSysL` are persistent) and whose `op` is `Op` (`wp_Op`, as remote's
`opMaybe`: overlapping calls are fine, `KitSys.lean`). The callees' specs are parameters (remote's
`ServeClient`, the kit's `Codec`, `net`'s, `io.ReadFull`'s, `bufio.NewReader`'s, `time.After`'s);
the kit's `Linked.lean` supplies the proofs.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitNewClient
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure raxos.msg

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] [_root_.Perennial.bufio.Assumptions]
variable [_root_.Perennial.io.Assumptions] [time.Assumptions]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]
variable [github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [QpBufioDeps GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem Client.wp_proof
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := QIn) (O := QOut))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γ c hc
  obtain ⟨cn, hcn⟩ : ∃ cn : Nat, uint.nat c = cn := ⟨_, rfl⟩
  have hcw : c = W64 (cn : Int) := by subst hcn; word
  subst hcw
  rw [hcn] at hc ⊢
  wp_start as ⟨Hres, #Hra, #Hmap⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  wp_apply wp_CfgAddrs as %csl Hcsl
  wp_apply wp_ClientAddrs as %clsl Hclsl
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
  imod ownSlice_persist _ _ _ $$ Hcsl with #Hcsl
  imodintro
  ihave %Hal := ownSlice_len _ _ _ $$ Hclsl
  have hal : clientAddrs.length = 6 := rfl
  have hb : 0 ≤ sint.Z (W64 (cn : Int)) ∧ sint.Z (W64 (cn : Int)) < sint.Z clsl.len := by
    constructor <;> word
  simp only [hb, _root_.and_self, ↓reduceIte]
  list_elem clientAddrs cn as a
  wp_apply wp_load_slice_index clsl (sint.Z (W64 (cn : Int))) clientAddrs _ a hb.1 $$ [Hclsl]
    with Hclsl
  · iframe; ipureintro; rw [show (sint.Z (W64 (cn : Int))).toNat = cn by word]; exact Ha_lookup
  have ha : a = clientAddrs.getD cn [] := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst ha
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_newClient wp_Listen wp_Accept wp_Read wp_Write wp_Close wp_ReadFull wp_Dial
    wp_NewReader γ cn hc asl csl $$ [Hres] as %s #Hsys
  · iframe Hres Hasl Hcsl
  ipersist s
  wp_apply (wp_Codec γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (qR γ)) _ _ _ _ cd d
    (fun sys => iprop(⌜sys = interface.mkOk (go.GoType.PointerType
      raxos.examples.quepaxanet.Sys.ty) #s⌝)) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation: `Op` over the client
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Φo
    iintro !> %Φr ⟨%Hsys', HL, -⟩ HΦr
    subst Hsys'
    wp_auto
    wp_apply wp_Op wp_Dial wp_Write wp_Close wp_After γ cn s i Φo $$ [HL] as %v Hv
    · iframe HL Hsys
    iapply HΦr
    isplitr
    · ipureintro; rfl
    icases Hv with (⟨%o, %Ho, HΦ⟩ | %Ho)
    · subst Ho
      ileft
      iexists o
      iframe HΦ
      ipureintro; rfl
    · subst Ho
      iright
      ipureintro; rfl
  · -- the client's system
    iintro %Φr HΦr
    wp_auto
    iapply HΦr
    ipureintro; rfl

end proof

end raxos.examples.quepaxanet
end Perennial
