/-
Lean-first (no Rocq counterpart).

The proof of `etcd3.StartCompactorPerEndpoint` (Q1 (c) of `notes/k8s-compactor-plan.md`): under the
registry's lock, the client's endpoints (`Endpoints()`, the ones `isNewClient` fixes) are looked up;
an entry found carries a claim of its endpoint whose predicate holds of its compactor, and the
caller's claim of the same endpoint agrees with it (`epClaim_agree`); otherwise the new compactor
(`NewCompactor`, with the `onClose` closure, which returns: it takes the lock and deletes, keeping the
invariant) is registered at every endpoint with the caller's claims.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.StartCompactorPerEndpoint
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewCompactor
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.k8s_io.klog.v2.V
public import Spec.k8s_io.klog.v2.Verbose__Infof
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem StartCompactorPerEndpoint.wp_proof
    (wp_NewCompactor : NewCompactor.spec (GF := GF) (hG := hG))
    (wp_Endpoints : EtcdGrove.Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_V : klog.V.spec (GF := GF) (hG := hG))
    (wp_Infof : klog.Verbose.Infof.spec (GF := GF) (hG := hG)) :
    StartCompactorPerEndpoint.spec (GF := GF) (hG := hG) := by
  intro _ _ cl ms V γk Seen recorded _ _ iv hsame hcmp hcret hiv
  wp_start as ⟨#Hcl, Hone, Hregs, #Hko, #Hwo, #Hcas, #Hkr, #Hclaims⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pe : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  ihave #Hreg : (registryFact : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pe
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, #Hrco, -⟩
  ihave #Heps := isNewClient_endpoints $$ Hcl
  iunfold clientEndpointsAt at Heps
  icases Heps with ⟨%esl0, #Hef, #Hes⟩
  iunfold registryFact at Hreg
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock _ registryInv) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  iunfold registryInv at HR
  icases HR with ⟨%mref, %m, Hmp, Hm, Hents⟩
  (try wp_auto)
  wp_apply wp_Endpoints cl $$ [] as %esl ⟨%eps, Hesl, Heq⟩
  · iframe #
  ihave %Heq' := Heq $$ %esl0 %_ Hef Hes
  subst Heq'
  ipersist Hesl
  ihave %Hsll := ownSlice_len $$ Hesl
  (try wp_auto)
  -- the lookups: no endpoint so far is registered
  ihave IH : iprop(∃ (n : w64) (e0 : GoString),
      "i" ∷ i_ptr ↦ n ∗ "ep" ∷ ep_ptr ↦ e0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ((ms.map client.SrvAt.addr).length : Int)⌝ ∗
      "%Hnone" ∷ ⌜∀ j e, j < sint.nat n → (ms.map client.SrvAt.addr)[j]? = some e →
        m.lookup e = none⌝) $$ [i ep]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by constructor <;> word, fun j e hj _ => ?_⟩
    simp at hj; omega
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < (ms.map client.SrvAt.addr).length := by word
    obtain ⟨e, He⟩ : ∃ e, (ms.map client.SrvAt.addr)[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) e esl DFrac.discard _ Hn.1 He $$ Hesl with ⟨#Hle, -⟩
    (try wp_auto)
    ihave #Hmy := BigSepL.bigSepL_lookup He $$ Hclaims
    iunfold epOf at Hmy
    cases Hme : m !! e with
    | none =>
      wp_apply (wp_map_lookup2 (K := GoString) (V := Loc) go.string _ mref m e) $$ [$Hm] as Hm
      simp only [Hme, Option.isSome_none, Option.getD_none]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, e
      simp only [named]
      iframe
      ipureintro
      refine ⟨by constructor <;> word, fun j e' hj he' => ?_⟩
      by_cases hjn : j < sint.nat n
      · exact Hnone j e' hjn he'
      · have hj' : j = sint.nat n := by word
        subst hj'
        rw [He] at he'
        cases he'
        exact Hme
    | some c =>
      icases (BigSepM.bigSepM_lookup_acc Hme).1 $$ Hents with ⟨Hent, Hback⟩
      icases Hent with ⟨%Ψ, %x, #HcΨ, %Hx, #HΨx⟩
      ihave Hents := Hback $$ []
      · iexists Ψ, x
        iframe #
        ipureintro; exact Hx
      ihave #Hx' : ▷ compactorFor γk recorded x $$ []
      · iapply (epClaim_agree e Ψ (compactorFor γk recorded) x) $$ HcΨ Hmy
        inext; iexact HΨx
      wp_apply (wp_map_lookup2 (K := GoString) (V := Loc) go.string _ mref m e) $$ [$Hm] as Hm
      simp only [Hme, Option.isSome_some, Option.getD_some]
      (try wp_auto)
      wp_apply wp_Endpoints cl $$ [] as %esl2 ⟨%eps2, Hesl2, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      (try wp_auto)
      wp_apply wp_V as %vb -
      (try wp_auto)
      -- the endpoints: a fresh `[]string`, owned
      wp_apply wp_Infof _ _ _ _ _ $$ [$Hasl Hesl2] as -
      · iframe #
        klog_args_intro
        isplitl [Hesl2]
        · iapply klog.argOkAt_strSlice $$ Hesl2
        itrivial
      (try wp_auto)
      wp_for_post
      wp_apply (sync.Mutex.wp_Unlock _ registryInv) $$ [Hlocked Hmp Hm Hents]
      · iframe #
        iframe Hlocked
        inext
        iunfold registryInv
        iexists mref, m
        iframe
      (try wp_auto)
      iapply HΦ
      iunfold compactorFor at Hx'
      icases Hx' with ⟨#Hc, #H0⟩
      iexists x.2.1, ⟨x.2.2⟩
      rw [← Hx]
      iframe #
  · -- no endpoint is registered: a new compactor, registered at each
    ipersist client
    simp only [recv_eq_func_mk]
    wp_apply (wp_NewCompactor cl ms V γk Seen recorded iv _ _ hsame hcmp hcret hiv)
      $$ [Hone Hregs] as %c %γc ⟨#Hc, #H0⟩
    · iframe #
      iframe
      -- `onClose`: under the lock, delete the client's endpoints (dropping their entries)
      unfold closeOk
      iright
      iintro !> %Φc HΦc
      (try wp_auto)
      wp_apply wp_with_defer as %defer2 defer2
      (try wp_auto)
      wp_apply (sync.Mutex.wp_Lock _ registryInv) $$ [] as ⟨Hlocked2, HR2⟩
      · iframe #
      iunfold registryInv at HR2
      icases HR2 with ⟨%mref2, %m2, Hmp2, Hm2, Hents2⟩
      (try wp_auto)
      wp_apply wp_Endpoints cl $$ [] as %esl3 ⟨%eps3, Hesl3, -⟩
      · iframe #
      ipersist Hesl3
      ihave %Hsll3 := ownSlice_len $$ Hesl3
      (try wp_auto)
      ihave IH3 : iprop(∃ (n : w64) (e0 : GoString) (m' : GMap GoString Loc),
          "i" ∷ i_ptr ↦ n ∗ "ep" ∷ ep_ptr ↦ e0 ∗ "Hm2" ∷ mref2 ↦$ m' ∗
          "Hents2" ∷ ([∗map] k ↦ v ∈ m', iprop(∃ (Ψ : CompactorId → IProp GF) (x : CompactorId),
            epClaim k Ψ ∗ ⌜x.fst = v⌝ ∗ □ Ψ x)) ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (eps3.length : Int)⌝) $$ [i ep Hm2 Hents2]
      · iexists W64 0, _, m2
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      wp_for IH3
      wp_if_destruct
      · have Hlt : sint.nat n < eps3.length := by word
        obtain ⟨e, He⟩ : ∃ e, eps3[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl3.len := ⟨Hn.1, by word⟩
        rw [ite_eq_left Hbnd]
        icases ownSlice_elem_acc (sint.Z n) e esl3 DFrac.discard _ Hn.1 He $$ Hesl3 with ⟨#Hle3, -⟩
        (try wp_auto)
        wp_apply (wp_mapDelete (K := GoString) (V := Loc) mref2 m' e go.string _) $$ [$Hm2] as Hm2
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, e, GMap.delete e m'
        simp only [named]
        iframe
        isplitl [Hents2]
        · iapply (BigSepM.bigSepM_subseteq LawfulPartialMap.delete_subset_self) $$ Hents2
        ipureintro; constructor <;> word
      · (try wp_auto)
        wp_apply (sync.Mutex.wp_Unlock _ registryInv) $$ [Hlocked2 Hmp2 Hm2 Hents2]
        · iframe #
          iframe Hlocked2
          inext
          iunfold registryInv
          iexists mref2, m'
          iframe
        (try wp_auto)
        iapply HΦc
    ihave #Hfor : compactorFor γk recorded (c, cl, γc.lb) $$ []
    · iunfold compactorFor
      iframe #
    (try wp_auto)
    wp_apply wp_Endpoints cl $$ [] as %esl4 ⟨%eps4, Hesl4, Heq4⟩
    · iframe #
    ihave %Heq4' := Heq4 $$ %esl0 %_ Hef Hes
    subst Heq4'
    ipersist Hesl4
    ihave %Hsll4 := ownSlice_len $$ Hesl4
    (try wp_auto)
    ihave IH4 : iprop(∃ (n : w64) (e0 : GoString) (m' : GMap GoString Loc),
        "i" ∷ i_ptr ↦ n ∗ "ep" ∷ ep_ptr ↦ e0 ∗ "Hm" ∷ mref ↦$ m' ∗
        "Hents" ∷ ([∗map] k ↦ v ∈ m', iprop(∃ (Ψ : CompactorId → IProp GF) (x : CompactorId),
          epClaim k Ψ ∗ ⌜x.fst = v⌝ ∗ □ Ψ x)) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ((ms.map client.SrvAt.addr).length : Int)⌝) $$ [i ep Hm Hents]
    · iexists W64 0, _, m
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH4
    wp_if_destruct
    · have Hlt : sint.nat n < (ms.map client.SrvAt.addr).length := by word
      obtain ⟨e, He⟩ : ∃ e, (ms.map client.SrvAt.addr)[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl4.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) e esl4 DFrac.discard _ Hn.1 He $$ Hesl4 with ⟨#Hle4, -⟩
      (try wp_auto)
      ihave #Hmy := BigSepL.bigSepL_lookup He $$ Hclaims
      iunfold epOf at Hmy
      wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string mref m' e c) $$ [$Hm] as Hm
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, e, <[e := c]> m'
      simp only [named]
      iframe
      isplitl [Hents]
      · iapply BigSepM.bigSepM_insert_delete.2
        isplitr
        · iexists compactorFor γk recorded, (c, cl, γc.lb)
          iframe #
          ipureintro; rfl
        iapply (BigSepM.bigSepM_subseteq LawfulPartialMap.delete_subset_self) $$ Hents
      ipureintro; constructor <;> word
    · (try wp_auto)
      wp_apply (sync.Mutex.wp_Unlock _ registryInv) $$ [Hlocked Hmp Hm Hents]
      · iframe #
        iframe Hlocked
        inext
        iunfold registryInv
        iexists mref, m'
        iframe
      (try wp_auto)
      iapply HΦ
      iexists cl, γc
      iframe #

end proof

end k8s
end EtcdGrove
end Perennial
