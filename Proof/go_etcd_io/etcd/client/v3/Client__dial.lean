/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__dial.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__dial
public import Spec.go_etcd_io.etcd.client.v3.Client__dialSetupOpts
public import Spec.go_etcd_io.etcd.client.v3.authority
public import Spec.google_golang_org.grpc.NewClient
public import Spec.fmt.SprintfArgs
public import Proof.fmt.SprintfPure
public import Spec.google_golang_org.grpc.WithPerRPCCredentials
public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle__PerRPCCredentials

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.dial.wp_proof
    (wp_dialSetupOpts : Client.dialSetupOpts.spec (GF := GF) (hG := hG))
    (wp_authority : authority.spec (GF := GF) (hG := hG))
    (wp_NewClient : grpc.NewClient.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.SprintfArgs.spec (GF := GF) (hG := hG))
    (wp_PerRPCCredentials :
      credentials.perRPCCredentialBundle.PerRPCCredentials.spec (GF := GF) (hG := hG))
    (wp_WithPerRPCCredentials : grpc.WithPerRPCCredentials.spec (GF := GF) (hG := hG)) :
    Client.dial.spec (GF := GF) (hG := hG) := by
  intro c cfg cr sl rb esl eps atb P
  wp_start as ⟨#Hc, #Hcfg, #Hdo, #Hatb, #Htb, #Heps, #Hesl, %Hplain, #Hds, Hrb⟩
  obtain ⟨ep, rest, rfl⟩ : ∃ ep rest, eps = ep :: rest := by
    cases eps with
    | nil => exact absurd rfl Hplain.1
    | cons a l => exact ⟨a, l, rfl⟩
  have Hp1 : plainEndpoint ep := Hplain.2 ep List.mem_cons_self
  ihave #Hgrpc : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_dialSetupOpts c cfg cr sl [.resolvers [rb]] $$ [$Hc $Hcfg $Hds]
    as %o1 ⟨%si, %ic, #Ho1, Ho1c, %Hsi, #Hic⟩
  iunfold dialOptsAt at Ho1
  icases Ho1 with ⟨%os1, #Hos1, #Hos1d⟩
  iStructNamed Hcfg
  -- (2026-10-25, the auth plan's E2d) the token bundle, if any, as per-RPC credentials
  wp_join iprop(∃ (o1' : GoSlice) (ex : List GrpcDialOpt) (os1' : List GoInterface),
      c_ptr ↦ c ∗ opts_ptr ↦ o1' ∗ o1' ↦*□ os1' ∗ ownSliceCap GoInterface o1' (DFrac.own 1) ∗
      ([∗list] o;d ∈ os1';(kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
          [GrpcDialOpt.transportCreds, GrpcDialOpt.streamInterceptor si,
            GrpcDialOpt.unaryInterceptor ic] ++ ex), grpcDialOptIs o d) ∗
      (⌜ex = []⌝ ∨ ∃ pc, ⌜ex = [GrpcDialOpt.perRPCCreds pc]⌝ ∗ perRPCCredsOk pc anyRes (tokMdOk P)))
    at next with [c opts Ho1c] as ⟨%o1', %ex, %os1', c, opts, #Hos1', Ho1c', #Hex, #Hexc⟩
  · icases Htb with (%Hnil | #Hb)
    · subst Hnil
      wp_auto
      wp_join_done
      iexists o1, [], os1
      iframe c opts Hos1 Ho1c
      isplitr
      · rw [List.append_nil]; iexact Hos1d
      · ileft; ipureintro; rfl
    iunfold tokenBundleInv at Hb
    icases Hb with ⟨%b, %rc, %Hbeq, #Hrc, #Hinv⟩
    subst Hbeq
    wp_auto
    wp_apply wp_PerRPCCredentials b rc P $$ [$Hrc $Hinv] as %pc #Hpc
    wp_apply wp_WithPerRPCCredentials pc $$ [$Hgrpc] as %o #Ho
    wp_apply wp_slice_literal (V := GoInterface) [o]
    isplitr
    · ipureintro; rfl
    iintro %ol ⟨Hol, -⟩
    (try wp_auto)
    wp_apply wp_slice_append_dfrac (V := GoInterface) o1 os1 DFrac.discard _ [o] (DFrac.own 1)
      $$ [$Hos1 $Ho1c $Hol] as %o1' ⟨#Ho1', Ho1c', -⟩
    · ipureintro; exact DFrac.valid_discard
    (try wp_auto)
    wp_join_done
    iexists o1', [GrpcDialOpt.perRPCCreds pc], os1 ++ [o]
    iframe c opts Ho1' Ho1c'
    isplitr
    · iapply (BigSepL2.bigSepL2_append (l1b := [o]) (l2b := [GrpcDialOpt.perRPCCreds pc])
        (Or.inr rfl)).2
      isplitl []
      · iexact Hos1d
      · iapply BigSepL2.bigSepL2_singleton.2; iexact Ho
    · iright
      iexists pc
      iframe Hpc
      ipureintro; rfl
  wp_apply wp_slice_append_dfrac (V := GoInterface) o1' os1' DFrac.discard cfg.DialOptions' []
    DFrac.discard $$ [$Hos1' $Ho1c' $Hdo] as %o2 ⟨#Ho2, Ho2c, -⟩
  · ipureintro; exact DFrac.valid_discard
  -- `clientTargetSeq.Add(1)`: the target's number (any value), under the counter's invariant
  ihave Hci : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, -, -, -, -, -, -, #Hcts⟩
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_apply _root_.Perennial.sync.atomic.Uint64.wp_Add _ (W64 1) $$ [$Hat]
  iinv Hcts with ⟨%n, >Hn⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑go_etcd_io.etcd.cache.v3.clientTargetSeqN from
    Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists n
  iframe Hn
  iintro Hn
  imod Hmask with -
  imod Hclose $$ [Hn] with -
  · inext; iexists _; iexact Hn
  imodintro
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hesl
  rw [ite_eq_left (by simp at Hlen; word)]
  wp_apply wp_load_slice_index esl (sint.Z (W64 0)) (ep :: rest) DFrac.discard ep (by decide) $$ [$Hesl]
    as -
  · ipureintro; rfl
  wp_apply wp_authority ep as %a -
  · ipureintro; exact Hp1
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #(go!"etcd-endpoints"),
      interface.mkOk go.uint64 #(n + W64 1), interface.mkOk go.string #a]
  isplitr
  · ipureintro; rfl
  iintro %al ⟨Hal, -⟩
  (try wp_auto)
  -- `Sprintf("%s://0x%x/%s", resolver.Schema, n, a)`: the scheme, then `://`
  wp_apply (fmt.wp_Sprintf_pure wp_Sprintf go!"%s://0x%x/%s"
    [.dir none _root_.Perennial.fmt.verb_s, .lit go!"://0x", .dir none _root_.Perennial.fmt.verb_x,
      .lit go!"/", .dir none _root_.Perennial.fmt.verb_s] _ _ _ (DFrac.own 1) (by fmt_encode)
    (by fmt_fits) (.str _ _ _ (.int _ _ _ _ (.uint64 _) (.str _ _ _ .nil)))) $$ [$Hal] as %tgt ⟨-, %Hout⟩
  have Hpre : (go!"etcd-endpoints" ++ go!"://") <+: tgt := by
    rw [Hout]
    simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render]
  have Hdok0 : dialOk ([GrpcDialOpt.resolvers [rb]] ++
      [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) rb := by
    refine ⟨?_, by simp⟩
    intro rbs h
    simp at h
    exact h
  -- (2026-10-21, D28) the keepalive option, if any, first
  have Hdok1 : dialOk (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
      [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) rb := by
    rw [List.append_assoc]; exact dialOk_kaOpts cfg _ rb Hdok0
  -- (E2d) the per-RPC credentials, if any, last
  -- (C1) the credentials, if any, are the dial's only ones
  have Hcr : credsOfDial (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
      [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ ex) = credsOfDial ex := by
    rw [credsOfDial_append, credsOfDial_append, credsOfDial_append]
    unfold kaOpts
    split <;> simp [GrpcDialOpt.credsOf]
  icases Hexc with (%Hex0 | ⟨%pc, %Hex1, #Hpc⟩)
  all_goals first | subst Hex0 | subst Hex1
  · have Hdok : dialOk (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ []) rb := by
      rw [List.append_nil]; exact Hdok1
    wp_apply wp_NewClient tgt o2 (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ []) rb etcdScheme (ep :: rest)
        anyRes (tokMdOk P) $$ [$Hgrpc Hrb]
      as %conn %err Hres
    · isplitr
      · iunfold dialOptsAt
        iexists _
        iframe Ho2
        simp only [List.append_nil]; iexact Hex
      isplitl [Hrb]
      · iunfold dialTargetOk
        ileft
        iframe Hrb
        ipureintro; exact ⟨Hdok, Hpre⟩
      rw [Hcr, credsOfDial_nil]
      iapply BigSepL.bigSepL_nil.2; itrivial
    iapply HΦ
    icases Hres with (⟨%Herr, #Hconn, #Hcc, #Hco⟩ | %Herr)
    · ileft
      isplitr
      · ipureintro; exact Herr
      have Hics : unaryIcsOf (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
          [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ []) = [ic] := by
        rw [List.append_nil, List.append_assoc, unaryIcsOf_kaOpts]; rfl
      rw [Hcr, Hics, credsOfDial_nil] at *
      isplitl []
      · unfold isEtcdConnG
        iexists ic
        iframe Hconn Hic
        unfold etcdConnStream
        iexists _
        iframe Hco
        ipureintro
        have hs := streamIcOf_etcdDial cfg rb si ic [] (Or.inl rfl)
        refine ⟨?_, Or.inr ⟨si, ?_, Hsi⟩⟩ <;>
          first
          | simp [connOptsOf, hs]
          | (unfold connOptsOf streamIcOf kaOpts; split <;>
              simp [GrpcDialOpt.streamOf, List.filterMap_cons, List.filterMap_append])
      · iapply connTokOk_none conn _ P
        iexact Hcc
    · iright
      ipureintro; exact Herr
  · have Hdok : dialOk (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++
        [GrpcDialOpt.perRPCCreds pc]) rb :=
      dialOk_perRPCCreds _ rb pc Hdok1
    wp_apply wp_NewClient tgt o2 (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ [GrpcDialOpt.perRPCCreds pc]) rb
        etcdScheme (ep :: rest) anyRes (tokMdOk P) $$ [$Hgrpc Hrb]
      as %conn %err Hres
    · isplitr
      · iunfold dialOptsAt
        iexists _
        iframe Ho2
        simp only [List.append_nil]; iexact Hex
      isplitl [Hrb]
      · iunfold dialTargetOk
        ileft
        iframe Hrb
        ipureintro; exact ⟨Hdok, Hpre⟩
      rw [Hcr, show credsOfDial [GrpcDialOpt.perRPCCreds pc] = [pc] by simp [GrpcDialOpt.credsOf]]
      iapply BigSepL.bigSepL_singleton.2
      iexact Hpc
    iapply HΦ
    icases Hres with (⟨%Herr, #Hconn, #Hcc, #Hco⟩ | %Herr)
    · ileft
      isplitr
      · ipureintro; exact Herr
      have Hics : unaryIcsOf (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
          [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++
          [GrpcDialOpt.perRPCCreds pc]) = [ic] := by
        rw [unaryIcsOf_perRPCCreds, List.append_assoc, unaryIcsOf_kaOpts]; rfl
      rw [Hcr, Hics, show credsOfDial [GrpcDialOpt.perRPCCreds pc] = [pc] by simp [GrpcDialOpt.credsOf]] at *
      isplitl []
      · unfold isEtcdConnG
        iexists ic
        iframe Hconn Hic
        unfold etcdConnStream
        iexists _
        iframe Hco
        ipureintro
        have hs := streamIcOf_etcdDial cfg rb si ic [GrpcDialOpt.perRPCCreds pc] (Or.inr ⟨pc, rfl⟩)
        refine ⟨?_, Or.inr ⟨si, ?_, Hsi⟩⟩ <;>
          first
          | simp [connOptsOf, hs]
          | (unfold connOptsOf streamIcOf kaOpts; split <;>
              simp [GrpcDialOpt.streamOf, List.filterMap_cons, List.filterMap_append])
      · iapply connTokOk_one conn pc P
        iexact Hcc
    · iright
      ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
