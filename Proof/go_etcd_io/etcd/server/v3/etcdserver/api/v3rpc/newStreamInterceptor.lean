/-
Proof of the spec of the same name (the watch slice's unit W-W, 2026-10-15). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newStreamInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.monitorLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.IsCapabilityEnabled
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsMemberExist
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsLearner
public import Spec.google_golang_org.grpc.metadata.MD__Get
public import Spec.unicode.utf8.ValidString
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues

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
/-- The interceptor's last statement: `return handler(srv, ss)` on the same server end, from the
handler's continuation `Hk`. -/
local macro "handler_tail" : tactic => `(tactic| (
  icases Hk with ⟨Hk, -⟩;
  ihave Hk := Hk $$ %(GoInterface.ok si) %ci %cd Hss;
  iunfold streamHandlerCall at Hk;
  wp_bind (App (App (Val #h) _) _);
  iapply (wp_wand (Φ := fun v =>
    iprop(∃ err : GoInterface, ⌜v = #err⌝ ∗ (True -∗ Ψ v))))
    $$ Hk;
  iintro %v ⟨%err, %Hv, HΨ⟩;
  subst Hv;
  wp_auto;
  iapply HΨ;
  itrivial))

set_option hygiene false in
/-- An early `return err` of the interceptor, from the error continuation of `Hk`. -/
local macro "error_return" e:term : tactic => `(tactic| (
  icases Hk with ⟨-, Hk⟩;
  iapply Hk $$ [] %(GoInterface.ok $e);
  · itrivial
  ipureintro; intro h; cases h))

theorem v3rpc.newStreamInterceptor.wp_proof
    (wp_monitorLeader : v3rpc.monitorLeader.spec (GF := GF) (hG := hG))
    (wp_IsCap : api.IsCapabilityEnabled.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_IsMemberExist : EtcdServer.IsMemberExist.spec (GF := GF) (hG := hG))
    (wp_IsLearner : EtcdServer.IsLearner.spec (GF := GF) (hG := hG))
    (wp_MDGet : metadata.MD.Get.spec (GF := GF) (hG := hG))
    (wp_ValidString : utf8.ValidString.spec (GF := GF) (hG := hG))
    (wp_WithLabelValues : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    v3rpc.newStreamInterceptor.spec (GF := GF) (hG := hG) := by
  intro s c ch mid tm et
  wp_start as ⟨#Hmid, #Hlead, #Hcl, #Hrc', #Hkept, Hgr, Hlg, #Hst, #Hstc, #Htm, #Het, #Hnrl⟩
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, #Hiv, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.interceptorVars at Hiv
  icases Hiv with ⟨#HeNS, #HeNC, #HeNL, #HeIV, #HeNoL, ⟨%kv, #Hkv⟩, ⟨%kl, #Hkl⟩,
    ⟨%hl, #Hhl⟩, ⟨%cv, #Hcv, %Hcvl⟩⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeNS HeNC HeNL HeIV HeNoL
  icases HeNC with ⟨%eNC, #HeNC⟩
  icases HeNL with ⟨%eNL, #HeNL⟩
  icases HeIV with ⟨%eIV, #HeIV⟩
  wp_pures
  wp_alloc_auto
  irename : (s_ptr ↦ s : IProp GF) => Hs
  ipersist Hs
  wp_auto
  wp_apply wp_monitorLeader s ch tm et $$ [Hgr Hlg] as %smap ⟨#Hsm, Hgr, Hlg⟩
  · iframe; iframe #
  rw [recv_eq_func_mk]
  iapply HΦ
  iframe Hgr Hlg
  unfold srvStreamInterceptorOk
  iintro !> %Req %Rep %Up %Dn %γ %ci %cd %srv %st %info %h %Ψ HR #Hss #Hinfo Hk
  iunfold streamInterceptorCall
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_IsCap as %b -
  iclear HR
  iunfold srvStreamInfoIs at Hinfo
  icases Hinfo with ⟨%fm, %cs, %sss, #Hfm, -, -⟩
  cases b
  · wp_auto
    error_return eNC
  wp_auto
  ipersist info
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
      ((∀ (st' : GoInterface) (ci' : GoInterfaceOk) (cd' : context.ContextDesc (IProp GF)),
          srvRawStreamIs st' γ Req Rep Up Dn ci' cd' -∗
          WP (streamHandlerCall #h #srv #st')
            {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗ (True -∗ Ψ v) }}) ∧
        (True -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ Ψ #err))) ∨
      ∃ e : GoInterface, ⌜v = returnVal #e⌝ ∗ Ψ #e)) at next with [Hk]
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
    wp_if_destruct
    · ileft; iframe
    · iright
      iexists (GoInterface.ok eNL)
      isplitr
      · ipureintro; rfl
      error_return eNL
  rename_i v
  iintro (⟨%Hv, Hk⟩ | ⟨%e, %Hv, HΨ⟩)
  rotate_left
  · subst Hv
    wp_auto
    iexact HΨ
  subst Hv
  wp_auto
  ihave #Hss' := Hss
  iunfold srvRawStreamIs at Hss'
  icases Hss' with ⟨%si, %Hsi, -, -, #HCtx, #Hctx, #Hrc⟩
  subst Hsi
  wp_auto
  wp_apply HCtx
  iunfold v3rpc.runsNoRequireLeader at Hnrl
  wp_apply Hnrl $$ %kl %hl %ci %cd Hkl Hhl Hctx Hrc as %md %ok Hmd
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
      [∗map] k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗
        ⌜k = kl → vs.head? ≠ some hl⌝)) with [ver Hsls]
    as ⟨%ver, ver, Hsls⟩
  · rcases Hvs with rfl | ⟨k', hk'⟩
    · exfalso; revert Hif; simp [slice.nil]
    ihave ⟨⟨%vss, Hvss, %Hne, %Hhd⟩, Hback⟩ :=
      (BigSepM.bigSepM_lookup_acc (Φ := fun (k : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs ∗
        ⌜vs ≠ []⌝ ∗ ⌜k = kl → vs.head? ≠ some hl⌝)) hk').1 $$ Hsls
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
    ipureintro; exact ⟨Hne, Hhd⟩
  wp_apply wp_ValidString as %bv %Hbv
  cases bv
  · wp_auto
    error_return eIV
  wp_auto
  wp_apply wp_slice_literal (V := GoString) [go!"stream", ver]
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  wp_auto
  wp_apply wp_WithLabelValues cv _ [go!"type", go!"client_api_version"] _ _ $$ [Hlsl]
    as %cnt ⟨%cnti, %Hcnt, #Hcs, -⟩
  · iframe #; iframe Hlsl; ipureintro
    exact ⟨Hcvl, prometheus.labelValuesOk_two _ _ _ _ (by decide) (of_decide_eq_true Hbv.symm)⟩
  subst Hcnt
  iunfold prometheus.counterSpec at Hcs
  icases Hcs with ⟨#Hcs, -⟩
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
    ihave ⟨⟨%kss, Hkss, %Hkne, %Hkhd⟩, -⟩ :=
      (BigSepM.bigSepM_lookup_acc (Φ := fun (k : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs ∗
        ⌜vs ≠ []⌝ ∗ ⌜k = kl → vs.head? ≠ some hl⌝)) hkl).1 $$ Hsls
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
      · exfalso; exact Hkhd rfl (by simp [Hif])
      · handler_tail
    · exfalso; simp at Hklen; word

end proof

end EtcdGrove
end Perennial
