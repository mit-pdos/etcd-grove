/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__dial.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__dial
public import Spec.go_etcd_io.etcd.client.v3.Client__dialSetupOpts
public import Spec.go_etcd_io.etcd.client.v3.authority
public import Spec.google_golang_org.grpc.NewClient
public import Spec.fmt.SprintfClientPtr
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

omit [GooseInterp] [GooseSemantics] hG sem package_sem in
/-- `Sprintf("%s://%p/%s", x, ...)` begins with `x` and `://`. -/
theorem sprintf_scheme_prefix [GoSemanticsFunctions] [go.IntoValInj GoString] (x : GoString)
    (args : List GoInterface) (out : GoString)
    (h : _root_.Perennial.fmt.SprintfOut go!"%s://%p/%s" (interface.mkOk go.string #x :: args)
      out) :
    (x ++ go!"://") <+: out := by
  have hf : go!"%s://%p/%s" = W8 37 :: W8 115 :: go!"://%p/%s" := rfl
  rw [hf] at h
  obtain ⟨o1, rfl, h1⟩ := _root_.Perennial.fmt.SprintfOut.str_inv h
  have hf1 : go!"://%p/%s" = W8 58 :: W8 47 :: W8 47 :: go!"%p/%s" := rfl
  rw [hf1] at h1
  obtain ⟨o2, rfl, h2⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h2
  obtain ⟨o4, rfl, -⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv (by decide) h3
  exact ⟨o4, by simp⟩

theorem Client.dial.wp_proof
    (wp_dialSetupOpts : Client.dialSetupOpts.spec (GF := GF) (hG := hG))
    (wp_authority : authority.spec (GF := GF) (hG := hG))
    (wp_NewClient : grpc.NewClient.spec (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.SprintfClientPtr.spec (GF := GF) (hG := hG))
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
  icases Ho1 with ⟨%os1, #Hos1, %Hos1⟩
  iStructNamed Hcfg
  -- (2026-10-25, the auth plan's E2d) the token bundle, if any, as per-RPC credentials
  wp_join iprop(∃ (o1' : GoSlice) (ex : List GrpcDialOpt) (os1' : List GoInterface),
      c_ptr ↦ c ∗ opts_ptr ↦ o1' ∗ o1' ↦*□ os1' ∗ ownSliceCap GoInterface o1' (DFrac.own 1) ∗
      ⌜List.Forall₂ grpcDialOptIs os1'
        (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
          [GrpcDialOpt.transportCreds, GrpcDialOpt.streamInterceptor si,
            GrpcDialOpt.unaryInterceptor ic] ++ ex)⌝ ∗
      (⌜ex = []⌝ ∨ ∃ pc, ⌜ex = [GrpcDialOpt.perRPCCreds pc]⌝ ∗ perRPCCredsOk pc (tokMdOk P)))
    at next with [c opts Ho1c] as ⟨%o1', %ex, %os1', c, opts, #Hos1', Ho1c', %Hex, #Hexc⟩
  · icases Htb with (%Hnil | #Hb)
    · subst Hnil
      wp_auto
      wp_join_done
      iexists o1, [], os1
      iframe c opts Hos1 Ho1c
      isplitr
      · ipureintro
        rw [List.append_nil]; exact Hos1
      · ileft; ipureintro; rfl
    iunfold tokenBundleInv at Hb
    icases Hb with ⟨%b, %rc, %Hbeq, #Hrc, #Hinv⟩
    subst Hbeq
    wp_auto
    wp_apply wp_PerRPCCredentials b rc P $$ [$Hrc $Hinv] as %pc #Hpc
    wp_apply wp_WithPerRPCCredentials pc $$ [$Hgrpc] as %o %Ho
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
    · ipureintro
      exact List.Forall₂.append Hos1 (.cons Ho .nil)
    · iright
      iexists pc
      iframe Hpc
      ipureintro; rfl
  wp_apply wp_slice_append_dfrac (V := GoInterface) o1' os1' DFrac.discard cfg.DialOptions' []
    DFrac.discard $$ [$Hos1' $Ho1c' $Hdo] as %o2 ⟨#Ho2, Ho2c, -⟩
  · ipureintro; exact DFrac.valid_discard
  ihave %Hlen := ownSlice_len _ _ _ $$ Hesl
  rw [ite_eq_left (by simp at Hlen; word)]
  wp_apply wp_load_slice_index esl (sint.Z (W64 0)) (ep :: rest) DFrac.discard ep (by decide) $$ [$Hesl]
    as -
  · ipureintro; rfl
  wp_apply wp_authority ep as %a -
  · ipureintro; exact Hp1
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string go_etcd_io.etcd.client.v3.internal.resolver.Schema,
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty) #c,
      interface.mkOk go.string #a]
  isplitr
  · ipureintro; rfl
  iintro %al ⟨Hal, -⟩
  (try wp_auto)
  wp_apply wp_Sprintf _ _ _ (DFrac.own 1) $$ [$Hal] as %tgt ⟨-, %Hout⟩
  · ipureintro
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string go!"etcd-endpoints" []
        _root_.Perennial.fmt.ArgsWf.nil _ (List.mem_singleton_self _)
    · right; rfl
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string a [] _root_.Perennial.fmt.ArgsWf.nil _
        (List.mem_singleton_self _)
  have Hpre := sprintf_scheme_prefix go!"etcd-endpoints" _ tgt Hout
  have Hdok0 : dialOk ([GrpcDialOpt.resolvers [rb]] ++
      [.transportCreds, .streamInterceptor si, .unaryInterceptor ic]) rb := by
    refine ⟨?_, ?_, by simp⟩
    · intro si' h
      simp at h
      rw [h]; exact Hsi
    · intro rbs h
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
    unfold credsOfDial
    rw [List.filterMap_append, List.filterMap_append, List.filterMap_append]
    unfold kaOpts
    split <;> rfl
  icases Hexc with (%Hex0 | ⟨%pc, %Hex1, #Hpc⟩)
  all_goals first | subst Hex0 | subst Hex1
  · have Hdok : dialOk (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ []) rb := by
      rw [List.append_nil]; exact Hdok1
    wp_apply wp_NewClient tgt o2 _ rb etcdScheme (ep :: rest) (tokMdOk P) Hdok $$ [$Hgrpc $Hrb]
      as %conn %err Hres
    · isplitr
      · iunfold dialOptsAt
        iexists _
        iframe Ho2
        ipureintro
        rw [List.append_nil]; exact Hex
      isplitr
      · ipureintro; exact Hpre
      rw [Hcr, show credsOfDial ([] : List GrpcDialOpt) = [] from rfl]
      iapply BigSepL.bigSepL_nil.2; itrivial
    iapply HΦ
    icases Hres with (⟨%Herr, #Hconn, #Hcc⟩ | %Herr)
    · ileft
      isplitr
      · ipureintro; exact Herr
      have Hics : unaryIcsOf (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
          [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++ []) = [ic] := by
        rw [List.append_nil, List.append_assoc, unaryIcsOf_kaOpts]; rfl
      rw [Hcr, Hics, show credsOfDial ([] : List GrpcDialOpt) = [] from rfl] at *
      isplitl []
      · unfold isEtcdConnG
        iexists ic
        iframe Hconn Hic
      · iapply connTokOk_none conn _ P
        iexact Hcc
    · iright
      ipureintro; exact Herr
  · have Hdok : dialOk (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
        [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++
        [GrpcDialOpt.perRPCCreds pc]) rb :=
      dialOk_perRPCCreds _ rb pc Hdok1
    wp_apply wp_NewClient tgt o2 _ rb etcdScheme (ep :: rest) (tokMdOk P) Hdok $$ [$Hgrpc $Hrb]
      as %conn %err Hres
    · isplitr
      · iunfold dialOptsAt
        iexists _
        iframe Ho2
        ipureintro
        rw [List.append_nil]; exact Hex
      isplitr
      · ipureintro; exact Hpre
      rw [Hcr, show credsOfDial [GrpcDialOpt.perRPCCreds pc] = [pc] from rfl]
      iapply BigSepL.bigSepL_singleton.2
      iexact Hpc
    iapply HΦ
    icases Hres with (⟨%Herr, #Hconn, #Hcc⟩ | %Herr)
    · ileft
      isplitr
      · ipureintro; exact Herr
      have Hics : unaryIcsOf (kaOpts cfg ++ [GrpcDialOpt.resolvers [rb]] ++
          [.transportCreds, .streamInterceptor si, .unaryInterceptor ic] ++
          [GrpcDialOpt.perRPCCreds pc]) = [ic] := by
        rw [unaryIcsOf_perRPCCreds, List.append_assoc, unaryIcsOf_kaOpts]; rfl
      rw [Hcr, Hics, show credsOfDial [GrpcDialOpt.perRPCCreds pc] = [pc] from rfl] at *
      isplitl []
      · unfold isEtcdConnG
        iexists ic
        iframe Hconn Hic
      · iapply connTokOk_one conn pc P
        iexact Hcc
    · iright
      ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
