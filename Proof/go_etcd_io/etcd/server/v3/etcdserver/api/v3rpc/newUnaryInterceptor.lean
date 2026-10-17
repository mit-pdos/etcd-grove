/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newUnaryInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.IsCapabilityEnabled
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsMemberExist
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsLearner
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isRPCSupportedForLearner
public import Spec.google_golang_org.grpc.metadata.FromIncomingContext
public import Spec.google_golang_org.grpc.metadata.MD__Get
public import Spec.unicode.utf8.ValidString
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option hygiene false in
/-- The interceptor's last statement: `return handler(ctx, req)`, from the handler's continuation
`Hk`. -/
local macro "handler_tail" : tactic => `(tactic| (
  icases Hk with ⟨Hk, -⟩;
  iunfold srvHandlerCall at Hk;
  wp_bind (App (App (Val #h) _) _);
  iapply (wp_wand (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
    (True -∗ Ψ v)))) $$ Hk;
  iintro %v ⟨%resp, %err, %Hv, HΨ⟩;
  subst Hv;
  wp_auto;
  iapply HΨ;
  itrivial))

set_option hygiene false in
/-- An early `return nil, err` of the interceptor, from the error continuation of `Hk`. -/
local macro "error_return" e:term : tactic => `(tactic| (
  icases Hk with ⟨-, Hk⟩;
  iapply Hk $$ [] %(GoInterface.ok $e);
  · itrivial
  ipureintro; intro h; cases h))

theorem v3rpc.newUnaryInterceptor.wp_proof
    (wp_IsCap : api.IsCapabilityEnabled.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_IsMemberExist : EtcdServer.IsMemberExist.spec (GF := GF) (hG := hG))
    (wp_IsLearner : EtcdServer.IsLearner.spec (GF := GF) (hG := hG))
    (wp_isRPC : v3rpc.isRPCSupportedForLearner.spec (GF := GF) (hG := hG))
    (wp_FromIncoming : metadata.FromIncomingContext.spec (GF := GF) (hG := hG))
    (wp_MDGet : metadata.MD.Get.spec (GF := GF) (hG := hG))
    (wp_ValidString : utf8.ValidString.spec (GF := GF) (hG := hG))
    (wp_WithLabelValues : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG)) :
    v3rpc.newUnaryInterceptor.spec (GF := GF) (hG := hG) := by
  intro s c mid
  wp_start as ⟨#Hmid, #Hlead, #Hcl, #Hrc', #Hkept⟩
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, #Hiv, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.interceptorVars at Hiv
  icases Hiv with ⟨#HeNS, #HeNC, #HeNL, #HeIV, #HeNoL, ⟨%kv, #Hkv⟩, ⟨%kl, #Hkl⟩, ⟨%hl, #Hhl⟩,
    ⟨%cv, #Hcv⟩⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeNS HeNC HeNL HeIV HeNoL
  icases HeNC with ⟨%eNC, #HeNC⟩
  icases HeNL with ⟨%eNL, #HeNL⟩
  icases HeIV with ⟨%eIV, #HeIV⟩
  icases HeNoL with ⟨%eNoL, #HeNoL⟩
  wp_pures
  wp_alloc_auto
  irename : (s_ptr ↦ s : IProp GF) => Hs
  ipersist Hs
  wp_auto
  rw [recv_eq_func_mk]
  iapply HΦ
  unfold srvInterceptorOk
  iintro !> %ci %cd %req %info %h %Ψ HR #Hctx #Hrc #Hinfo #HQ Hk
  iunfold srvInterceptorCall
  wp_auto
  wp_apply wp_IsCap as %b -
  cases b
  · wp_auto
    icases Hk with ⟨-, Hk⟩
    iapply Hk $$ HR %(GoInterface.ok eNC)
    ipureintro; intro h; cases h
  wp_auto
  irename : (req_ptr ↦ req : IProp GF) => Hreqp
  ipersist Hreqp
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
      (WP (srvHandlerCall h #(GoInterface.ok ci) #req)
          {{ v, ∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗ (True -∗ Ψ v) }} ∧
        (True -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗
          Ψ (PairV #GoInterface.nil #err)))) ∨
      ∃ e : GoInterface, ⌜v = returnVal (PairV #GoInterface.nil #e)⌝ ∗
        Ψ (PairV #GoInterface.nil #e))) at next with [HR Hk]
  · wp_apply wp_MemberID s mid $$ []
    · iframe #
    wp_apply wp_IsMemberExist s c mid $$ [] as %b1 -
    · iframe #
    cases b1
    · wp_auto
      ileft; iframe; ipureintro; rfl
    wp_auto
    wp_apply wp_IsLearner s c $$ [] as %b2 -
    · iframe #
    cases b2
    · wp_auto
      ileft; iframe; ipureintro; rfl
    wp_auto
    wp_apply wp_isRPC req $$ [] as %b3 -
    · iframe #
    cases b3
    · wp_auto
      iright
      iexists (GoInterface.ok eNL)
      isplitr
      · ipureintro; rfl
      icases Hk with ⟨-, Hk⟩
      iapply Hk $$ HR %(GoInterface.ok eNL)
      ipureintro; intro h; cases h
    · wp_auto
      ileft; iframe; ipureintro; rfl
  rename_i v
  iintro (⟨%Hv, Hk⟩ | ⟨%e, %Hv, HΨ⟩)
  rotate_left
  · subst Hv
    wp_auto
    iexact HΨ
  subst Hv
  wp_auto
  wp_apply wp_FromIncoming as %md %ok Hmd
  cases ok
  · iclear Hmd
    wp_auto
    handler_tail
  icases Hmd with (%Hok | ⟨%m, Hm, Hsls⟩)
  · cases Hok
  irename : (md_ptr ↦ md : IProp GF) => Hmdp
  ipersist Hmdp
  ipersist Hm
  wp_auto
  wp_apply wp_MDGet md_ptr md m kv $$ [] as %vsl %Hvs
  · iframe #
  irename : (vs_ptr ↦ vsl : IProp GF) => Hvsp
  ipersist Hvsp
  wp_join (iprop(∃ ver : GoString, ver_ptr ↦ ver ∗
      [∗map] _k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝)) with [ver Hsls]
    as ⟨%ver, ver, Hsls⟩
  · rcases Hvs with rfl | ⟨k', hk'⟩
    · exfalso; revert Hif; simp [slice.nil]
    ihave ⟨⟨%vss, Hvss, %Hne⟩, Hback⟩ :=
      (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝)) hk').1 $$ Hsls
    ihave %Hlen := ownSlice_len vsl _ vss $$ Hvss
    simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vsl.len) from by word]
    obtain ⟨v0, vss', rfl⟩ : ∃ v0 vss', vss = v0 :: vss' := by
      cases vss with
      | nil => exact absurd rfl Hne
      | cons a l => exact ⟨a, l, rfl⟩
    wp_apply wp_load_slice_index vsl (sint.Z (W64 0)) (v0 :: vss') _ v0 (by word) $$ [Hvss] as Hvss
    · iframe; ipureintro; rfl
    wp_join_done
    iexists v0
    iframe
    iapply Hback
    iexists _
    iframe
    ipureintro; exact Hne
  wp_apply wp_ValidString as %bv -
  cases bv
  · wp_auto
    error_return eIV
  wp_auto
  wp_apply wp_slice_literal (V := GoString) [go!"unary", ver]
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  wp_auto
  wp_apply wp_WithLabelValues cv _ as %cnt ⟨%cnti, %Hcnt, #Hcs⟩
  subst Hcnt
  iunfold prometheus.counterSpec at Hcs
  wp_apply Hcs
  wp_apply (wp_map_lookup1 go.string (go.GoType.SliceType go.string) md m kl _) $$ [Hm]
  · iframe #
  cases hkl : m !! kl with
  | none =>
    iintro -
    simp only [Option.getD_none]
    wp_auto
    handler_tail
  | some ksl =>
    iintro -
    simp only [Option.getD_some]
    wp_auto
    ihave ⟨⟨%kss, Hkss, %Hkne⟩, -⟩ :=
      (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝)) hkl).1 $$ Hsls
    ihave %Hklen := ownSlice_len ksl _ kss $$ Hkss
    obtain ⟨k0, kss', rfl⟩ : ∃ k0 kss', kss = k0 :: kss' := by
      cases kss with
      | nil => exact absurd rfl Hkne
      | cons a l => exact ⟨a, l, rfl⟩
    wp_if_destruct
    · simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len) from by word]
      wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) (k0 :: kss') _ k0 (by word) $$ [Hkss]
        as Hkss
      · iframe; ipureintro; rfl
      wp_if_destruct
      · wp_apply wp_Leader s $$ [] as %ld -
        · iframe #
        wp_if_destruct
        · error_return eNoL
        · handler_tail
      · handler_tail
    · exfalso; simp at Hklen; word

end proof

end EtcdGrove
end Perennial
