/-
Lean-first (no Rocq counterpart).

# The in-process instance of the k8s library's etcd client (K5, `notes/k8s-dist-lean-plan.md` §4.1)

`inProcEtcd ms V`: a client of the in-process members `ms` (`client.SrvAt`), whose handle is `New`'s
client of them (`isNewClient`, sending a write at most once, each member's KV registered), with an
update at every member's KV, live when no member refuses connections. `inProcEtcd_laws`: its laws,
from the in-process specs of the calls (hypotheses, which the linking modules pass).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.EtcdClient
public import Proof.go_etcd_io.etcd.client.v3.ClientCallLaws
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver EtcdGrove.kubernetes

section inproc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client of the in-process members `ms`** (see the file header). -/
def inProcEtcd [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) : K8sEtcd GF where
  kvs := ms.map (fun x => x.γr.kv)
  live := ∀ x ∈ ms, noRefusalAt x.addr
  eps := ms.map client.SrvAt.addr
  handle cl := iprop(isNewClient cl (ms.map client.SrvAt.addr) V ∗
    client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ [∗list] x ∈ ms, client.kvRegsAt x)
  kvAt api := iprop(EtcdGrove.kvObjAt api (ms.map client.SrvAt.addr) ∗ [∗list] x ∈ ms, client.kvRegsAt x)

theorem inProcEtcd_kvs [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) :
    (inProcEtcd ms V).kvs = ms.map (fun x => x.γr.kv) := rfl

/-- **The in-process client's laws**, from the in-process specs. -/
theorem inProcEtcd_laws [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (wp_Get : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.Get.spec (GF := GF) (hG := hG))
    (wp_List : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.List.spec (GF := GF) (hG := hG))
    (wp_OptimisticPut : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.OptimisticPut.spec (GF := GF) (hG := hG))
    (wp_OptimisticDelete : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.OptimisticDelete.spec (GF := GF) (hG := hG))
    (h_range_any : client.client_range_any.law (GF := GF) (hG := hG))
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) : (inProcEtcd ms V).Laws where
  get := by
    intro _ _ _ kc ci cd key opts Q h1 h2
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, -, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_Get kc ms V ci cd key opts Q h1 h2) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  list := by
    intro _ _ _ kc ci cd pfx opts Q h1 h2 h3 h4 h5
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, -, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_List kc ms V ci cd pfx opts Q h1 h2 h3 h4 h5) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  optimisticPut := by
    intro _ _ _ kc ci cd key vsl val rev opts Q h1 h2 h3
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, #Hwo, #Hregs⟩, #Hctx, #Hce, #Hv, Hau⟩ HΦ
    iapply (wp_OptimisticPut kc ms V ci cd key vsl val rev opts Q h1 h2 h3) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  optimisticDelete := by
    intro _ _ _ kc ci cd key rev opts Q h1
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, #Hwo, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_OptimisticDelete kc ms V ci cd key rev opts Q h1) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  ctxFields := by
    intro cl
    simp only [inProcEtcd]
    iintro ⟨#Hnc, -, -⟩
    iapply EtcdGrove.isNewClient_ctxOk $$ Hnc
  kvField := by
    intro cl
    simp only [inProcEtcd]
    iintro ⟨#Hnc, -, #Hregs⟩
    iunfold isNewClient at Hnc
    icases Hnc with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
    iexists api
    isplitr
    · iexact Hkvf
    imodintro
    isplitr
    · iexact Hkv
    iexact Hregs
  kvGet := by
    intro _ _ api ctx cdw pk osl gs Qr hsz hg hser hss
    simp only [inProcEtcd]
    iintro %Φ ⟨#Pc, Hlt, ⟨#Hkv, #Hregs⟩, #Hctx, #Hce, #Hopts, #Hra⟩ HΦ
    imod (client.srvStart_alloc (GF := GF) ms) with #Hst
    ihave #Hopts' := optsAt_res osl gs iprop(True) $$ Hopts
    ihave #Hst' := client.srvStart_both ms $$ Hst
    ihave #Hau : (□ [∧list] x ∈ ms, ⌜Qr = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel pk gs)).base.serializable = false⌝ ∗ kvReadAu x.γr.kv Qr)) $$ [Hra]
    · imodintro
      iapply (BigAndL.bigAndL_intro
        (P := iprop(□ [∗list] γ ∈ ms.map (fun x => x.γr.kv), kvReadAu γ Qr)) (fun k x hk => ?_)) $$ Hra
      iintro #H'
      ihave #Hx := BigSepL.bigSepL_lookup
        (show (ms.map (fun x : client.SrvAt GF => x.γr.kv))[k]? = some x.γr.kv by simp [hk]) $$ H'
      iright
      iframe Hx
      ipureintro; exact hser
    wp_apply (h_range_any api ms (W64 0) ctx cdw pk osl gs iprop(True) Qr [] hsz) $$ [$Hlt]
      as %resp %err ⟨Hlt, -, Hout, -⟩
    · iframe #
      isplitl []
      · rw [hss]; iapply sortNamesIf_false
      ipureintro; exact hg
    iapply HΦ
    iframe Hlt
    icases Hout with (⟨%Herr, %m, Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
    · subst Herr
      ihave Hs := kubernetes.rangeReply_state_at x.E x.γr (W64 0) x.cid x.mid _ [] Qr m hser $$ Hq
      icases Hs with ⟨%σ, #HQ, %Hσ⟩
      obtain ⟨hsel, -, hrevσ, hle, hb, -⟩ := Hσ
      ileft
      isplitr
      · ipureintro; rfl
      iexists m, σ
      iframe Hm HQ
      ipureintro
      exact ⟨hsel, hrevσ, hle, hb⟩
    · iright
      iunfold kvErr at Hke
      icases Hke with ⟨%Hce, #Hse, #Hcl⟩
      isplitr
      · ipureintro; exact Herr
      iframe Hse Hcl
      ipureintro; exact ⟨Herr, Hce⟩

/-- **The in-process client** from `New`'s client of the members (`isStore`'s former conjuncts). -/
theorem k8sClient_inProc [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (hl : (inProcEtcd ms V).Laws) (cl : Loc) :
    isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ⊢
    k8sClient (inProcEtcd ms V) cl := by
  iintro #H
  unfold k8sClient
  isplitr
  · ipureintro; exact hl
  imodintro
  simp only [inProcEtcd]
  iexact H

end inproc

end k8s
end EtcdGrove
end Perennial
