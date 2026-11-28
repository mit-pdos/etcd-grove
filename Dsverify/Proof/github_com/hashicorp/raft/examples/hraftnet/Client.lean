/-
`hraftnet.Client`'s proof (notes/dsv-hraft.md, S5f): `Register()`, then `remote.ServeClient` with a fresh
`Sys` (its connections `serverConns()`, a random first server) and the operation `op` (`Sys.op`, over the
system's state `sysTok`: its counter, below the calls the address served, `budUsed_add`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Client
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Sys__op
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverConns
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.attempt
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rnd
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Register
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ClientAddrs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.KitCodecDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot rpctransport service

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : Net.NetProtoGS] [ρ : RemoteGS] [rsem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable [rpcsem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [net.rpc.Assumptions] [net.Assumptions]
variable [rmsem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

/-- Client `c`'s system at its address `a`: a `*Sys` of client `c`, its connections, a server, its count
`seq` with the counter `seqOwn` at `seq + 1`, at most the calls `m` the address served. -/
def sysTok (K : HK GF) (c : Nat) (a : GoString) (sys : GoInterface) : IProp GF :=
  iprop(∃ (s : Loc) (sv : Sys) (m : Nat), ⌜sys = interface.mkOk (go.GoType.PointerType Sys.ty) #s⌝ ∗
    s ↦ sv ∗ ⌜sv.c' = W64 (c : Int) ∧ 1 ≤ uint.nat sv.j' ∧ uint.nat sv.j' ≤ 6 ∧ uint.nat sv.seq' ≤ m⌝ ∗
    sysConns K sv.conns' ∗ seqOwn K.g c (uint.nat sv.seq' + 1) ∗ budUsed (Gg := hG.goose_globalGS) a m)

theorem Client.wp_proof
    (wp_op : Sys.op.spec (GF := GF) (hG := hG))
    (wp_serverConns : serverConns.spec (GF := GF) (hG := hG))
    (wp_attempt : attempt.spec (GF := GF))
    (wp_rnd : rnd.spec (GF := GF))
    (wp_Register : Register.spec (GF := GF))
    (wp_ClientAddrs : ClientAddrs.spec (GF := GF))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_ServeClient : ServeClient.spec (GF := GF) (hG := hG) (I := HIn) (O := HOut)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro K c N hc hN
  wp_start as ⟨#Hmu, Hun, %Hss, #Hdi, #Hid, Hseq, #Has, #Hra, %Hbud⟩
  wp_auto
  wp_apply wp_Register $$ [$Hmu $Hun] as #Hcod
  ipersist c
  ihave #Hrp : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  ihave #Hrt : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_ClientAddrs as %casl ⟨%L, Hcasl, %HL⟩
  subst HL
  ihave %Hal := ownSlice_len _ _ _ $$ Hcasl
  have hal : clientAddrs.length = 5 := rfl
  have hb : 0 ≤ sint.Z (W64 (c : Int)) ∧ sint.Z (W64 (c : Int)) < sint.Z casl.len := by
    rw [hal] at Hal; constructor <;> word
  rw [ite_eq_left hb]
  list_elem clientAddrs c as a
  wp_apply wp_load_slice_index casl (sint.Z (W64 (c : Int))) clientAddrs _ a hb.1 $$ [Hcasl] as Hcasl
  · iframe
    ipureintro
    rw [show (sint.Z (W64 (c : Int))).toNat = c by word]
    exact Ha_lookup
  have ha : a = clientAddrs.getD c go!"" := by simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst ha
  (try wp_auto)
  wp_apply (wp_Codec K.g.st) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply (wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (regR K.g.st)) (W64 (c : Int))
    (clientAddrs.getD c go!"") _ _ cd d (sysTok K c (clientAddrs.getD c go!""))) $$ [Hseq] as ⟨⟩
  iframe #
  isplitr
  · iapply codecOk_wireOk $$ Hcd
  isplitr
  · iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Ψ
    iintro !> %Φo ⟨Htok, Hupd, Hu⟩ HΦo
    iunfold sysTok at Htok
    icases Htok with ⟨%sp, %sv, %m, %Hsys, Hs, %Hsv, #Hconns, Hseq, Hused⟩
    subst Hsys
    obtain ⟨hsc, hj1, hj6, hsm⟩ := Hsv
    ihave ⟨Hused, %Hle⟩ := budUsed_add (Gg := hG.goose_globalGS) _ m $$ Hused Hu
    have hm : m + 1 ≤ N := Hle N Hbud.1
    have hcn : uint.nat sv.c' = c := by rw [hsc]; word
    ihave #Henv : cliEnv K $$ []
    · unfold cliEnv; iframe #; ipureintro; exact Hss
    have hiv : (regR (GF := GF) (Gg := hG.goose_globalGS) K.g.st).iv i =
        interface.mkOk In.ty #(inS i) := rfl
    rw [hiv]
    wp_auto
    rw [← hcn]
    wp_apply (wp_op K sp sv i Ψ (by omega) (by omega) hj1 hj6) $$ [$Henv $Hs $Hconns $Hid $Hseq $Hupd]
      as %o ⟨⟨%sv', Hs, %Hsv'⟩, Hseq, Hres⟩
    obtain ⟨hc', hcn', hsq', hj1', hj6'⟩ := Hsv'
    (try wp_auto)
    iapply HΦo
    isplitl [Hs Hseq Hused]
    · unfold sysTok
      iexists sp, sv', m + 1
      have hs1 : uint.nat sv'.seq' = uint.nat sv.seq' + 1 := by rw [hsq']; word
      rw [hs1, hcn', hc']
      iframe Hs Hconns Hused
      rw [show uint.nat sv.seq' + 1 + 1 = uint.nat sv.seq' + 2 by omega]
      iframe Hseq
      ipureintro
      exact ⟨rfl, by word, hj1', hj6', by omega⟩
    unfold outRes
    icases Hres with (⟨%out, %Ho, HΨ⟩ | %Ho)
    · ileft
      iexists out
      iframe HΨ
      ipureintro
      rw [Ho]; rfl
    · iright
      ipureintro
      rw [Ho]; rfl
  iintro %Φn HΦn
  (try wp_auto)
  wp_apply (wp_serverConns K.W) $$ [$Has] as %sl ⟨%ps, Hsl, %Hpl, #Hcs⟩
  · ipureintro; exact Hbud.2
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  imodintro
  wp_apply (wp_rnd (W64 6) (by decide)) as %r %Hr
  (try wp_auto)
  wp_alloc sp as Hsp
  (try wp_auto)
  iapply HΦn
  unfold sysTok
  iexists sp, _, 0
  iframe Hsp
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only; word
    · simp only; have := Hr; word
    · simp only; word
  isplitr
  · unfold sysConns
    iexists ps
    iframe Hsl Hcs
    ipureintro; exact Hpl
  isplitl [Hseq]
  · simp only
    rw [show uint.nat (0 : w64) + 1 = 1 from rfl]
    iexact Hseq
  iapply budUsed_zero

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
