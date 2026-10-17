/-
Proof of `Spec/go_etcd_io/etcd/client/v3/New.lean` (pr-verify etcd#21714). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.New
public import Spec.go_etcd_io.etcd.client.v3.newClient

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem clientv3.New.wp_proof (wp_newClient : newClient.spec (GF := GF) (hG := hG)) :
    clientv3.New.spec (GF := GF) (hG := hG) := by
  intro cv xs ds
  wp_start as ⟨#Hvars, #Hxs, #Hds, #Hctx⟩
  ihave %Hxlen := ownSlice_len _ _ _ $$ Hxs
  ihave #Hvars0 := Hvars
  iunfold newClientVars at Hvars
  ihave #Hvars' := Hvars
  icases Hvars' with ⟨-, ⟨%eNE, #HeNE, #HeNEs⟩, -⟩
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedPrefix Hcf "F"
  wp_if_destruct
  · iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists eNE
    iframe #
    isplitr
    · ipureintro; rfl
    ileft
    iframe #
    ipureintro
    apply List.eq_nil_of_length_eq_zero
    word
  wp_apply wp_newClient cfg_ptr cv xs ds $$ [] as %c %err Hpost
  · iframe #
  iapply HΦ
  icases Hpost with (Hok | ⟨%Hc, %e, %He, #Hes, #Herr⟩)
  · ileft; iexact Hok
  iright
  isplitr
  · ipureintro; exact Hc
  iexists e
  isplitr
  · ipureintro; exact He
  isplitr
  · iexact Hes
  iright
  iexact Herr

end proof

end EtcdGrove
end Perennial
