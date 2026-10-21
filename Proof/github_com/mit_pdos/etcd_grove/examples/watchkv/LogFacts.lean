/-
**What a watchkv server's certified logs hold** (D23, 2026-10-20). Lean-first (no Rocq
counterpart).

At watchkv's workload (`Workload.lean`), a log the server certified (`mvcc.certOk`: the KV model of
a committed raft prefix, `kv_cert_read`) and sealed (`mvcc.idxSealed`: every watch event's log is
both, `mvcc.evLog`) is a watchkv log (`wk_log`): the committed prefix is of plain entries of the
workload (the KV invariant's `plainLog`, through `srvRLog_lb`), and a log of at most two
revisions is a prefix of the start log (the store's certificate of `[[], []]`, comparable with
every sealed log). So no revision writes a key twice: the watch client's premise
`srvNoDupKeys` (`srvNoDupKeys_wk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Workload
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section facts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A certified sealed log of a watchkv server is a watchkv log** (see the file header). -/
theorem wk_log (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []]) (L : mvcc.Log) :
    ⊢ srvKVInvs (GF := GF) E γr -∗ mvcc.idxCert E.γ.idx [[], []] -∗ mvcc.idxSealed E.γ.idx L -∗
      mvcc.certOk E.γ L ={⊤}=∗ ⌜WkLog P L⌝ := by
  iintro #Hinvs #H0 #Hs #Hc
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, %Hcok⟩
  imod kv_cert_read γr.raft γr.kv E.γ Hcok ⊤ (fun _ _ => CoPset.mem_full) L $$ HcI Hc with (%hl | ⟨%A, #HA, %hA⟩)
  · -- at most two revisions: a prefix of the start log
    ihave #H0s := mvcc.idxCert_sealed _ _ $$ H0
    ihave %Hp := mvcc.idxSealed_prefix E.γ.idx L [[], []] $$ [Hs H0s]
    · isplit
      · iexact Hs
      · iexact H0s
    imodintro
    ipureintro
    apply WkLog.of_start_prefix
    rcases Hp with h | h
    · exact h
    · have := h.length_le
      have heq : [[], []] = L := h.eq_of_length (by simp at this ⊢; omega)
      rw [← heq]; exact List.prefix_refl _
  · -- the KV model of a committed prefix of plain entries
    have hk : (↑kvN : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full
    iunfold kvInv at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%Lc, HL, Hσ, %Hok, #Hw⟩
    imod srvRLog_lb γr.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
      Lc A $$ HrI HL HA with ⟨HL, -, %Hp⟩
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists Lc; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    ipureintro
    obtain ⟨hpl, -, -, hch, -⟩ := Hok
    have hplA : plainLog γr.kv.wl A := fun m hm => hpl m (Hp.subset hm)
    rw [hwl] at hplA
    rw [← hA]
    unfold kvModel
    rw [hch, hlog]
    exact kvRaftOf_wk P γr.kv.c0 A [[], []] hplA (WkLog.start P) (by simp)

/-- **`srvNoDupKeys` at a watchkv server** (D23: derived from the workload, no longer a premise of
the watch path for a program that picks it). -/
theorem srvNoDupKeys_wk (R : v3rpc.WSrv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []]) (hst : R.γ.st = R.E.γ) :
    srvKVInvs (GF := GF) R.E γr ∗ mvcc.idxCert R.E.γ.idx [[], []] ⊢ client.srvNoDupKeys R := by
  iintro ⟨#Hinvs, #H0⟩
  unfold client.srvNoDupKeys
  rw [hst]
  iintro !> %L #Hs #Hc
  imod wk_log R.E γr P hwl hlog L $$ Hinvs H0 Hs Hc with %Hwk
  imodintro
  ipureintro
  exact Hwk.noDup

end facts

end watchkv
end EtcdGrove
end Perennial
