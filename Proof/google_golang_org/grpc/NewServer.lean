/-
Proof of `Spec/google_golang_org/grpc/NewServer.lean` over the model's body (W1, 2026-11-26; until
then a trust-boundary axiom, `notes/axiom-review/phase7-w1.md` §3): `opts := defaultServerOptions`
(grpc's package fact: no hook set), the global options (none: `globalServerOptions` is nil) and
`opt`'s applied in order, each by its kind (`srvOptFnOk`); then the `Server` literal, no compressor
and no credentials (none set), the chains (`chain{Unary,Stream}ServerInterceptors`), the condition
variable, and the mutex's invariant (`True`) allocated: `grpcSrvNew` with nothing registered.
-/
module

public import Spec.google_golang_org.grpc.NewServer
public import Spec.google_golang_org.grpc.internal.stats.NewCombinedHandler
public import Spec.google_golang_org.grpc.internal.grpcsync.NewEvent
public import Spec.google_golang_org.grpc.chainUnaryServerInterceptors
public import Spec.google_golang_org.grpc.chainStreamServerInterceptors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What `NewServer`'s option loop owns of the `serverOptions` `so`: the two chains (elements `us`,
`ss`) and the stats handlers (`hs`), with their capacities (what the options' closures append to). -/
abbrev grpcNS_optsOwn (so : google_golang_org.grpc.serverOptions) (us ss : List GoFunc)
    (hs : List GoInterface) : IProp GF :=
  iprop(so.chainUnaryInts' ↦* us ∗ ownSliceCap GoFunc so.chainUnaryInts' (DFrac.own 1) ∗
    so.chainStreamInts' ↦* ss ∗ ownSliceCap GoFunc so.chainStreamInts' (DFrac.own 1) ∗
    so.statsHandlers' ↦* hs ∗ ownSliceCap GoInterface so.statsHandlers' (DFrac.own 1))

/-- The stats handlers an option of the kind `k` adds (`srvOptFnOk`'s `.stats` clause). -/
def grpcNS_statsOf : SrvOptKind → List GoInterface
  | .stats h => if h = interface.nil then [] else [h]
  | _ => []

/-- **The hooks of `so` are unset** (what `srvOptsIs` states of the built server): no credentials,
compressor, decompressor, single interceptor, unknown-stream handler or stream wrapper; the codec
nil or a protobuf codec's (`srvCodecOk`'s second form). `defaultServerOptions` has them
(`grpcDefaultSrvOpts`), and every option kind keeps them (`grpcNS_hooks_step`). -/
def grpcNS_hooksOk (so : google_golang_org.grpc.serverOptions) : Prop :=
  so.creds' = GoInterface.nil ∧ so.cp' = GoInterface.nil ∧ so.dc' = GoInterface.nil ∧
  so.unaryInt' = zero_val GoFunc ∧ so.streamInt' = zero_val GoFunc ∧
  so.unknownStreamDesc' = null ∧ so.streamWrapper' = zero_val GoFunc ∧
  (so.codec' = GoInterface.nil ∨ ∃ c : GoInterface, grpcProtoCodec c ∧
    so.codec' = interface.mkOk google_golang_org.grpc.codecV0Bridge.ty
      #(google_golang_org.grpc.codecV0Bridge.mk c))

theorem grpcNS_hooks_step {so so' : google_golang_org.grpc.serverOptions}
    (h : srvOptsSameBut so so') (hc : srvCodecOk so so') (H : grpcNS_hooksOk so) :
    grpcNS_hooksOk so' := by
  unfold srvOptsSameBut at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; exact h1
  · rw [h]; exact h2
  · rw [h]; exact h3
  · rw [h]; exact h4
  · rw [h]; exact h5
  · rw [h]; exact h6
  · rw [h]; exact h7
  · rcases hc with hc | hc
    · rw [hc]; exact h8
    · exact Or.inr hc

theorem grpcNS_unary_snoc (l : List SrvOptKind) (k : SrvOptKind) :
    srvOptsUnary (l ++ [k]) = srvOptsUnary l ++ k.unary := by
  simp [srvOptsUnary]

theorem grpcNS_stream_snoc (l : List SrvOptKind) (k : SrvOptKind) :
    srvOptsStream (l ++ [k]) = srvOptsStream l ++ k.stream := by
  simp [srvOptsStream]

/-- **`.stats h` carries `grpcStatsHandlerOk h`** (`srvOptFnOk`'s `.stats` clause, etcd-grove#60). -/
theorem grpcNS_stats_ok (f : GoFunc) (h : GoInterface) :
    srvOptFnOk (GF := GF) f (.stats h) ⊢ ⌜grpcStatsHandlerOk h⌝ := by
  unfold srvOptFnOk
  iintro ⟨%Hok, -⟩
  ipureintro
  exact Hok

/-- **One option applied** (`o.apply(&opts)`'s closure call), uniformly over its kind: the chains and
the stats handlers grow by what the kind adds, every other field but the whitelist stays
(`srvOptsSameBut`), the codec is kept or a protobuf codec's (`srvCodecOk`), and an added stats
handler has `grpcStatsHandlerOk`. -/
theorem grpcNS_srvOptFnOk_wp (f : GoFunc) (k : SrvOptKind) (p : Loc)
    (so : google_golang_org.grpc.serverOptions) (us ss : List GoFunc) (hs : List GoInterface) :
    {{ (srvOptFnOk (GF := GF) f k ∗ p ↦ so ∗ grpcNS_optsOwn (GF := GF) so us ss hs : IProp GF) }}
      (App (Val #f) (Val #p))
    {{ (so' : google_golang_org.grpc.serverOptions), RET #();
        p ↦ so' ∗ grpcNS_optsOwn so' (us ++ k.unary) (ss ++ k.stream) (hs ++ grpcNS_statsOf k) ∗
        ⌜srvOptsSameBut so so' ∧ srvCodecOk so so' ∧
          ∀ h ∈ grpcNS_statsOf k, grpcStatsHandlerOk h⌝ }} := by
  cases k with
  | neutral =>
    wp_start_folded as ⟨#Hf, Hp, Hu, Huc, Hs, Hsc, Hh, Hhc⟩
    iunfold srvOptFnOk at Hf
    iapply Hf $$ %p %so %Φ Hp
    inext
    iintro %so' Hp' %Hok
    obtain ⟨hsb, hcod, hcu, hcs, hch⟩ := Hok
    iapply HΦ $$ %so'
    isplitl [Hp']
    · iexact Hp'
    isplitl [Hu Huc Hs Hsc Hh Hhc]
    · simp only [grpcNS_optsOwn, SrvOptKind.unary, SrvOptKind.stream, grpcNS_statsOf,
        List.append_nil]
      rw [hcu, hcs, hch]
      iframe
    ipureintro
    exact ⟨hsb, hcod, fun h hh => by simp [grpcNS_statsOf] at hh⟩
  | chainUnary ics =>
    wp_start_folded as ⟨#Hf, Hp, Hu, Huc, Hs, Hsc, Hh, Hhc⟩
    iunfold srvOptFnOk at Hf
    iapply Hf $$ %p %so %us %Φ Hp Hu Huc
    inext
    iintro %so' Hp' Hu' Huc' %Hok
    obtain ⟨hsb, hcod, hcs, hch⟩ := Hok
    iapply HΦ $$ %so'
    isplitl [Hp']
    · iexact Hp'
    isplitl [Hu' Huc' Hs Hsc Hh Hhc]
    · simp only [grpcNS_optsOwn, SrvOptKind.unary, SrvOptKind.stream, grpcNS_statsOf,
        List.append_nil]
      rw [hcs, hch]
      iframe
    ipureintro
    exact ⟨hsb, Or.inl hcod, fun h hh => by simp [grpcNS_statsOf] at hh⟩
  | chainStream ics =>
    wp_start_folded as ⟨#Hf, Hp, Hu, Huc, Hs, Hsc, Hh, Hhc⟩
    iunfold srvOptFnOk at Hf
    iapply Hf $$ %p %so %ss %Φ Hp Hs Hsc
    inext
    iintro %so' Hp' Hs' Hsc' %Hok
    obtain ⟨hsb, hcod, hcu, hch⟩ := Hok
    iapply HΦ $$ %so'
    isplitl [Hp']
    · iexact Hp'
    isplitl [Hu Huc Hs' Hsc' Hh Hhc]
    · simp only [grpcNS_optsOwn, SrvOptKind.unary, SrvOptKind.stream, grpcNS_statsOf,
        List.append_nil]
      rw [hcu, hch]
      iframe
    ipureintro
    exact ⟨hsb, Or.inl hcod, fun h hh => by simp [grpcNS_statsOf] at hh⟩
  | stats h =>
    wp_start_folded as ⟨#Hf, Hp, Hu, Huc, Hs, Hsc, Hh, Hhc⟩
    ihave %Hok0 := grpcNS_stats_ok f h $$ Hf
    iunfold srvOptFnOk at Hf
    icases Hf with ⟨-, #Hf⟩
    iapply Hf $$ %p %so %hs %Φ Hp Hh Hhc
    inext
    iintro %so' Hp' Hh' Hhc' %Hok
    obtain ⟨hsb, hcod, hcu, hcs⟩ := Hok
    iapply HΦ $$ %so'
    isplitl [Hp']
    · iexact Hp'
    isplitl [Hu Huc Hs Hsc Hh' Hhc']
    · simp only [grpcNS_optsOwn, SrvOptKind.unary, SrvOptKind.stream, grpcNS_statsOf,
        List.append_nil]
      rw [hcu, hcs]
      iframe
    ipureintro
    refine ⟨hsb, Or.inl hcod, fun h' hh => ?_⟩
    simp only [grpcNS_statsOf] at hh
    split at hh
    · exact absurd hh (by simp)
    · rw [List.mem_singleton] at hh
      subst hh
      exact Hok0

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

set_option maxHeartbeats 2000000 in
theorem grpc.NewServer.wp_proof
    (wp_NewCombinedHandler : istats.NewCombinedHandler.spec (GF := GF) (hG := hG))
    (wp_NewEvent : grpcsync.NewEvent.spec (GF := GF) (hG := hG))
    (wp_chainUnaryServerInterceptors : grpc.chainUnaryServerInterceptors.spec (GF := GF) (hG := hG))
    (wp_chainStreamServerInterceptors :
      grpc.chainStreamServerInterceptors.spec (GF := GF) (hG := hG)) :
    grpc.NewServer.spec (GF := GF) (hG := hG) := by
  intro sl vs ks
  wp_start as ⟨#Hsl, #Hopts⟩
  -- grpc's package fact: `globalServerOptions` nil, `defaultServerOptions` with no hook set
  ihave #Hi : (_root_.Perennial.go_etcd_io.etcd.cache.v3.grpcInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, #Hgso, %dso, #Hdso, %Hdef⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Hvk := BigSepL2.bigSepL2_length $$ Hopts
  obtain ⟨Hvl, -⟩ := Hsll
  iapply wp_fupd
  wp_auto
  -- `for _, o := range globalServerOptions`: nil, no iteration
  wp_for
  first
  | (wp_if_destruct
     exfalso
     revert Hif
     first | decide | (simp [slice.nil]; done) | (word_lit_simp; omega))
  | skip
  -- `for _, o := range opt`: the options in order
  ihave IH : iprop(∃ (n : w64) (ov : GoInterface) (so : google_golang_org.grpc.serverOptions)
      (hs : List GoInterface),
      "Hcnt" ∷ i_ptr ↦ n ∗ "Ho" ∷ o_ptr ↦ ov ∗ "Hso" ∷ opts_ptr ↦ so ∗
      "Hown" ∷ grpcNS_optsOwn (GF := GF) so (srvOptsUnary (ks.take (sint.nat n)))
        (srvOptsStream (ks.take (sint.nat n))) hs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ vs.length ∧ (∀ h ∈ hs, grpcStatsHandlerOk h) ∧
        grpcNS_hooksOk so⌝) $$ [i o opts]
  · obtain ⟨hcr, hcod, hcp, hdc, hui, hsi, hcu, hcs, hsh, husd, hsw⟩ := Hdef
    iexists W64 0, _, dso, []
    simp only [named]
    iframe
    simp only [grpcNS_optsOwn]
    rw [hcu, hcs, hsh, show (zero_val GoSlice) = slice.nil from rfl]
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, srvOptsUnary, srvOptsStream,
      List.flatMap_nil]
    isplitl []
    · isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply ownSlice_nil
      iapply ownSliceCap_nil
    ipureintro
    exact ⟨by decide, by word, fun h hh => by simp at hh,
      ⟨hcr, hcp, hdc, hui, hsi, husd, hsw, Or.inl hcod⟩⟩
  wp_for IH
  wp_if_destruct
  · -- an iteration: `o.apply(&opts)`
    obtain ⟨Hn0, Hnle, Hok, Hhk⟩ := Hn
    have Hif : sint.Z n < sint.Z sl.len
      := by first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
    have Hlt : sint.nat n < vs.length := by rw [Hvl]; word
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨k, Hk⟩ : ∃ k, ks[sint.nat n]? = some k :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hvk]; exact Hlt)⟩
    ihave #Hvk' := BigSepL2.bigSepL2_lookup (Φ := fun _ v k => grpcSrvOpt (GF := GF) v k) Hv Hk
      $$ Hopts
    iunfold grpcSrvOpt at Hvk'
    icases Hvk' with ⟨%l, %f, %Hvl', #Hl, #Hf⟩
    subst Hvl'
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn0, Hif⟩
    (try simp only [Hbnd, _root_.and_self, ite_true])
    wp_apply (wp_load_slice_index sl (sint.Z n) vs DFrac.discard _ Hn0) $$ [$Hsl] as -
    · ipureintro; exact Hv
    iStructNamed Hl
    (try wp_auto)
    -- the interface call `o.apply(&opts)` on the `*funcServerOption` at `l`: its closure `f`
    wp_method_call
    wp_call
    (try wp_auto)
    wp_apply (grpcNS_srvOptFnOk_wp f k opts_ptr so _ _ hs) $$ [$Hf $Hso $Hown]
      as %so' ⟨Hso, Hown, %Hso'⟩
    wp_for_post
    iframe
    iexists n + W64 1, _, so', hs ++ grpcNS_statsOf k
    simp only [named]
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hn1, List.take_add_one, Hk]
    simp only [Option.toList_some, grpcNS_unary_snoc, grpcNS_stream_snoc]
    iframe
    ipureintro
    refine ⟨by word, by omega, ?_, grpcNS_hooks_step Hso'.1 Hso'.2.1 Hhk⟩
    intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact Hok h hh
    · exact Hso'.2.2 h hh
  -- every option applied: the chains are the options' (`srvOptsUnary ks`, `srvOptsStream ks`)
  obtain ⟨Hn0, Hnle, Hok, Hhk⟩ := Hn
  have Hif : ¬ sint.Z n < sint.Z sl.len
      := by first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h]) | (intro h; apply Hif; simp [h])
  have Hnl : sint.nat n = ks.length := by rw [← Hvk]; rw [Hvl] at Hnle ⊢; word
  rw [Hnl, List.take_length]
  icases Hown with ⟨Hu, -, Hs, -, Hh, -⟩
  imod ownSlice_persist _ _ _ $$ Hu with #Hu
  imod ownSlice_persist _ _ _ $$ Hs with #Hs
  imod ownSlice_persist _ _ _ $$ Hh with #Hh
  obtain ⟨hcr, hcp, hdc, hui, hsi, husd, hsw, hcod⟩ := Hhk
  -- `&Server{lis, opts, statsHandler, conns, services, quit, done}`
  wp_apply (wp_map_make1 (K := GoInterface) (V := Bool)) as %lis Hlis
  wp_apply (wp_NewCombinedHandler so.statsHandlers' hs) $$ [$Hh] as %sh Hsh
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %conns Hconns
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %svm Hsvm
  wp_apply wp_NewEvent as %q Hq
  wp_apply wp_NewEvent as %dn Hdn
  (try wp_auto)
  iStructNamedPrefix «$r0» "S"
  -- `opts.cp != nil || opts.dc != nil`, `opts.creds != nil && …`: none is set
  (try simp only [hcp, hdc, hcr])
  (try wp_auto)
  wp_apply (wp_chainUnaryServerInterceptors «$r0_ptr» so (srvOptsUnary ks)) $$ [$Sopts $Hu]
    as %cu ⟨Sopts, Hcu⟩
  · ipureintro; exact hui
  wp_apply (wp_chainStreamServerInterceptors «$r0_ptr» { so with unaryInt' := cu }
      (srvOptsStream ks)) $$ [$Sopts $Hs] as %cs ⟨Sopts, Hcs⟩
  · ipureintro; exact hsi
  wp_apply sync.wp_NewCond as %cv #Hcv
  -- the mutex, its invariant `True` (the fields are `grpcSrvNew`'s)
  imod (sync.init_Mutex (GF := GF) (BI.pure True : IProp GF) ⊤
    (structFieldRef google_golang_org.grpc.Server go!"mu" «$r0_ptr»)) $$ Smu [] with #Hmu
  · (try inext)
    itrivial
  imodintro
  iapply HΦ
  unfold grpcSrvNew
  iexists _, sh, lis, conns, svm, cv, q, dn, [], [], ∅
  isplitl [Sopts]
  · iexact Sopts
  isplitl [Hcu Hcs Hsh]
  · unfold srvOptsIs
    isplitl [Hcu]
    · iexact Hcu
    isplitl [Hcs]
    · iexact Hcs
    isplitl [Hsh]
    · iexists hs
      unfold srvStatsIs
      isplitr
      · iexact Hh
      isplitr
      · ipureintro; exact Hok
      iexact Hsh
    ipureintro
    exact ⟨hcr, hcp, hdc, husd, hsw, hcod⟩
  isplitl [SstatsHandler]
  · iexact SstatsHandler
  isplitr
  · iexact Hmu
  isplitl [Slis]
  · iexact Slis
  isplitl [Hlis]
  · iexact Hlis
  isplitl [Sconns]
  · iexact Sconns
  isplitl [Hconns]
  · iexact Hconns
  isplitl [Sserve]
  · iexact Sserve
  isplitl [Sdrain]
  · iexact Sdrain
  isplitl [Scv]
  · iexact Scv
  isplitr
  · iexact Hcv
  isplitl [Sservices]
  · iexact Sservices
  isplitl [Hsvm]
  · iexact Hsvm
  isplitl [Sevents]
  · iexact Sevents
  isplitl [Squit]
  · iexact Squit
  isplitl [Hq]
  · iexact Hq
  isplitl [Sdone]
  · iexact Sdone
  isplitl [Hdn]
  · iexact Hdn
  isplitl [SserveWG]
  · iexact SserveWG
  isplitl [ShandlersWG]
  · iexact ShandlersWG
  isplitl []
  · ipureintro
    exact ⟨rfl, List.nodup_nil, rfl, fun _ => rfl, rfl, rfl, fun _ h => by simp at h⟩
  iapply BigSepL2.bigSepL2_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
