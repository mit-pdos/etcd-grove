/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__initChannelKey.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__initChannelKey
public import Proof.go_etcd_io.etcd.client.v3.Client__dialWithBalancer
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.New
public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver__Close
public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.initChannelKey.wp_proof
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (wp_validateChannelKey : validateChannelKey.spec (GF := GF) (hG := hG))
    (wp_resolverNew : resolver.New.spec (GF := GF) (hG := hG))
    (wp_rClose : resolver.EtcdManualResolver.Close.spec (GF := GF) (hG := hG))
    (wp_credentialsForEndpoint : Client.credentialsForEndpoint.spec (GF := GF) (hG := hG))
    (wp_WithResolvers : grpc.WithResolvers.spec (GF := GF) (hG := hG))
    (wp_dial : Client.dial.spec (GF := GF) (hG := hG)) :
    Client.initChannelKey.spec (GF := GF) (hG := hG) := by
  intro c mu mref ctx cctx dq0 key cfg cr esl eps chs
  wp_start as ⟨#Hc, Hctx, #Hmu, #Hguard, #Hcfg, #Hdo, #Hatb, #Hcr, #Heps, #Hesl, %Hplain, %Hmref, Hchs, Hm⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_validateChannelKey key as %verr Hvres
  by_cases hres : key = go!"" ∨ key = go!"default"
  · simp only [decide_eq_true hres, ↓reduceIte]
    ihave Hvres' : (∃ e : GoInterfaceOk, ⌜verr = GoInterface.ok e⌝ ∗
      go_etcd_io.etcd.cache.v3.errorStringSpec e) $$ [Hvres]
    · simp only [hres, ↓reduceIte]; iexact Hvres
    icases Hvres' with ⟨%e, %Hverr, #HeS⟩
    subst Hverr
    wp_auto
    iapply HΦ
    iframe Hctx Hchs Hm
    iexists e
    iframe HeS
    ipureintro; rfl
  · simp only [decide_eq_false hres, Bool.false_eq_true, ↓reduceIte]
    ihave Hvres' : ⌜verr = GoInterface.nil⌝ $$ [Hvres]
    · simp only [hres, ↓reduceIte]; iexact Hvres
    icases Hvres' with %Hvres
    subst Hvres
    cases ctx with
    | nil =>
      wp_auto
      wp_apply sync.RWMutex.wp_Lock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hguard] as ⟨Hwl, -⟩
      rw [decide_eq_false Hmref]
      wp_auto
      wp_apply wp_map_lookup2 $$ [$Hm] as Hm
      by_cases hok : (chs !! key).isSome
      · simp only [hok, ↓reduceIte]
        wp_auto
        wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
        iapply HΦ
        iframe Hctx Hchs Hm
        ipureintro; rfl
      · have hokf : (chs !! key).isSome = false := Bool.eq_false_iff.2 hok
        simp only [hokf, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        ihave %Hel := ownSlice_len _ _ _ $$ Hesl
        wp_apply wp_slice_make2 (V := GoString) esl.len as %nesl ⟨Hnesl, -⟩
        · ipureintro; exact Hel.2
        (try wp_auto)
        wp_apply +noauto wp_slice_copy $$ [$Hnesl $Hesl] as %nc ⟨-, Hnesl, -⟩
        have Hcp : (eps.take (List.replicate (sint.nat esl.len) (zero_val GoString)).length ++
            (List.replicate (sint.nat esl.len) (zero_val GoString)).drop eps.length) = eps := by
          rw [List.length_replicate, List.take_of_length_le (by rw [Hel.1]; exact Nat.le_refl _),
            List.drop_of_length_le (by rw [List.length_replicate, Hel.1]; exact Nat.le_refl _),
            List.append_nil]
        rw [Hcp]
        ipersist Hnesl
        wp_auto
        wp_apply wp_resolverNew nesl eps $$ [$Hnesl] as %r ⟨%Hrnn, Hro⟩
        wp_apply (Client.dialWithBalancerForKey.wp_proof wp_credentialsForEndpoint wp_WithResolvers wp_dial)
          c cctx key cfg cr r nesl DFrac.discard eps
          $$ [$Hc $Hcfg $Hdo $Hatb $Hcr $Hro $Hnesl] as %conn %derr ⟨_, Hdres⟩
        · ipureintro; exact Hplain
        icases Hdres with (⟨⟨%Hderr, %Hconn⟩, #Hec⟩ | %Hderr)
        · subst Hderr
          wp_auto
          wp_apply wp_mapInsert $$ [$Hm] as Hm
          wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
          iapply HΦ
          iframe Hctx Hchs
          ileft
          isplitr
          · ipureintro; rfl
          iexists conn, r
          iframe Hm Hec
          ipureintro; exact ⟨Hconn, Hrnn⟩
        · cases derr with
          | nil => exact absurd rfl Hderr
          | ok de =>
            wp_auto
            wp_apply wp_rClose r
            wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
            iapply HΦ
            iframe Hctx Hchs
            iright
            iframe Hm
            ipureintro; exact Hderr
    | ok ci =>
      wp_auto
      wp_apply sync.RWMutex.wp_Lock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hguard] as ⟨Hwl, -⟩
      rw [decide_eq_false Hmref]
      wp_auto
      wp_apply wp_map_lookup2 $$ [$Hm] as Hm
      by_cases hok : (chs !! key).isSome
      · simp only [hok, ↓reduceIte]
        wp_auto
        wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
        iapply HΦ
        iframe Hctx Hchs Hm
        ipureintro; rfl
      · have hokf : (chs !! key).isSome = false := Bool.eq_false_iff.2 hok
        simp only [hokf, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        ihave %Hel := ownSlice_len _ _ _ $$ Hesl
        wp_apply wp_slice_make2 (V := GoString) esl.len as %nesl ⟨Hnesl, -⟩
        · ipureintro; exact Hel.2
        (try wp_auto)
        wp_apply +noauto wp_slice_copy $$ [$Hnesl $Hesl] as %nc ⟨-, Hnesl, -⟩
        have Hcp : (eps.take (List.replicate (sint.nat esl.len) (zero_val GoString)).length ++
            (List.replicate (sint.nat esl.len) (zero_val GoString)).drop eps.length) = eps := by
          rw [List.length_replicate, List.take_of_length_le (by rw [Hel.1]; exact Nat.le_refl _),
            List.drop_of_length_le (by rw [List.length_replicate, Hel.1]; exact Nat.le_refl _),
            List.append_nil]
        rw [Hcp]
        ipersist Hnesl
        wp_auto
        wp_apply wp_resolverNew nesl eps $$ [$Hnesl] as %r ⟨%Hrnn, Hro⟩
        wp_apply (Client.dialWithBalancerForKey.wp_proof wp_credentialsForEndpoint wp_WithResolvers wp_dial)
          c (GoInterface.ok ci) key cfg cr r nesl DFrac.discard eps
          $$ [$Hc $Hcfg $Hdo $Hatb $Hcr $Hro $Hnesl] as %conn %derr ⟨_, Hdres⟩
        · ipureintro; exact Hplain
        icases Hdres with (⟨⟨%Hderr, %Hconn⟩, #Hec⟩ | %Hderr)
        · subst Hderr
          wp_auto
          wp_apply wp_mapInsert $$ [$Hm] as Hm
          wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
          iapply HΦ
          iframe Hctx Hchs
          ileft
          isplitr
          · ipureintro; rfl
          iexists conn, r
          iframe Hm Hec
          ipureintro; exact ⟨Hconn, Hrnn⟩
        · cases derr with
          | nil => exact absurd rfl Hderr
          | ok de =>
            wp_auto
            wp_apply wp_rClose r
            wp_apply sync.RWMutex.wp_Unlock_guard mu (fun _ => iprop(True)) $$ [$Hsync $Hwl]
            iapply HΦ
            iframe Hctx Hchs
            iright
            iframe Hm
            ipureintro; exact Hderr

end proof

end EtcdGrove
end Perennial
