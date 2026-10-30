/-
**The KV invariant's readers in the auth mode `on`** (the auth plan's E2u, 2026-10-26;
`notes/decisions.md`, "E2u of the auth plan"): the counterparts over E2q's mode-`on` invariants
(`kvInvOn`, `kvCertInvOn`, `KVApplyOn.lean`) of what the server's readers learn from the mode-off
ones: a certified store log is the mode-`on` model of a committed raft prefix
(`kv_cert_read_on`, `kv_cert_read`'s), and is below the committed KV state (`kv_cert_floor_on`,
`kv_cert_floor`'s); and the KV invariant's step at a commit (`kvInvOn_facts_snoc`,
`kvInvOn_commit_granted`, `kvInvOn_commit_keep`), where a client's update fires: a granted plain
write steps the KV state by its request, an admin entry or a refused one keeps it.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The mode-`on` model is monotone in the raft log** (`kvRaftOf_prefix`'s counterpart). -/
theorem kvRaftOfOn_prefix (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A B : List EntryModel) (h : A <+: B) :
    (kvRaftOfOn c₀ ch s₀ A).2 <+: (kvRaftOfOn c₀ ch s₀ B).2 := by
  obtain ⟨D, rfl⟩ := h
  rw [kvRaftOfOn_append]
  exact kvRaftOfOn_extends _ _ _ _

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A store log's certificate, read at the server, in the mode `on`** (`kv_cert_read`'s): the
log has at most two revisions, or it is the mode-`on` model of a committed raft log. -/
theorem kv_cert_read_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (γs : mvcc.StoreNames) (hγ : γs.cok = γk.cok) (E : CoPset) (hE : ↑kvcN ⊆ E) (l : mvcc.Log) :
    ⊢ kvCertInvOn (GF := GF) γ γk st₀ -∗ mvcc.certOk γs l ={E}=∗
      ⌜l.length ≤ 2⌝ ∨ ∃ A, srvRLogLb γ A ∗ ⌜kvModelOn γk st₀ A = l⌝ := by
  unfold mvcc.certOk
  rw [hγ]
  iintro #Hinv (%h | #He | #He)
  · imodintro; ileft; ipureintro; exact h
  · iunfold kvCertInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hm := ghost_map_lookup $$ HC He
    imod Hclose $$ [HC Hhi'] with -
    · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
    imodintro
    iright
    obtain ⟨-, -, -, A, hA, hm⟩ := Hok.1 _ _ Hm
    iexists A
    isplitr
    · iapply srvRLogLb_mono γ A Lb hA $$ HLb
    ipureintro; exact hm
  · iunfold kvCertInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hm := ghost_map_lookup $$ HC He
    obtain ⟨-, -, -, A, -, hm⟩ := Hok.1 _ _ Hm
    have h0 := kvRaftOfOn_extends γk.c0 γk.ch0 (st₀, γk.log0) A
    unfold kvModelOn at hm
    rw [hm] at h0
    have := h0.length_le
    simp only [List.length_nil] at this
    omega

/-- **A certified log is below the committed KV state, in the mode `on`** (`kv_cert_floor`'s):
the state `σ` of a holder of `etcdKV` is the state of the committed raft log's mode-`on` model, and
a certified log is the model of a committed raft prefix (`kv_cert_read_on`) or has at most two
revisions, so its length is at most `σ`'s revision and one. -/
theorem kv_cert_floor_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (γs : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (x : String) (hx1 : x ≠ "server_kv") (hx2 : x ≠ "server_kv_cert")
    (hx3 : x ≠ "raft_commit") (l : mvcc.Log) (σ : KVState) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ kvCertInvOn γ γk st₀ -∗ srvRaftLogInv γ -∗
      mvcc.certOk γs l -∗ etcdKV γk σ ={⊤ \ ↑(nroot.@x)}=∗ etcdKV γk σ ∗ ⌜l.length ≤ σ.rev + 1⌝ := by
  sorry
/- REPAIR-OLD
  have hc : (↑kvcN : CoPset) ⊆ ⊤ \ ↑(nroot.@x) := mask_ndot_ne' nroot "server_kv_cert" x (Ne.symm hx2)
  have hk : (↑kvN : CoPset) ⊆ ⊤ \ ↑(nroot.@x) := mask_ndot_ne' nroot "server_kv" x (Ne.symm hx1)
  have hr : (↑srvRaftN : CoPset) ⊆ (⊤ \ ↑(nroot.@x)) \ ↑kvN :=
    mask_ndot_ne2 "raft_commit" x "server_kv" (Ne.symm hx3) (by decide)
  iintro #HkI #HcI #HrI #Hc Hσ
  ihave #HcI' := HcI
  iunfold kvCertInvOn at HcI'
  iinv HcI' with >Hi Hclose
  icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
  imod Hclose $$ [HC Hhi'] with -
  · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
  have h2 := Hok.2
  imod kv_cert_read_on γ γk st₀ γs hγ (⊤ \ ↑(nroot.@x)) hc l $$ HcI Hc with Hcase
  ihave #HkI' := HkI
  iunfold kvInvOn at HkI'
  iinv HkI' with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ', Hh, %Hok', #Hw⟩
  iunfold etcdKV at Hσ
  ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ' Hσ
  have hlen := (kvRaftOfOn_extends γk.c0 γk.ch0 (st₀, γk.log0) L).length_le
  ihave Hp : iprop(|={(⊤ \ ↑(nroot.@x)) \ ↑kvN}=> srvRLog γ L ∗
      ⌜l.length ≤ (kvModelOn γk st₀ L).length⌝) $$ [HL Hcase]
  · icases Hcase with (%hl | ⟨%A, #HA, %hA⟩)
    · imodintro; iframe HL; ipureintro; unfold kvModelOn; simp only at hlen; omega
    · imod srvRLog_lb γ ((⊤ \ ↑(nroot.@x)) \ ↑kvN) hr L A $$ HrI HL HA with ⟨HL, %Hp⟩
      ihave %HAi := srvRLogLb_idx γ A $$ HA
      imodintro; iframe HL; ipureintro
      obtain ⟨L', hL', hAL⟩ := kvRaftOfOn_of_lb γ γk.c0 γk.ch0 (st₀, γk.log0) A L Hok'.2.2.2.1
        HAi Hp.1 Hp.2.1 Hp.2.2
      have := (kvRaftOfOn_prefix γk.c0 γk.ch0 (st₀, γk.log0) L' L hL').length_le
      unfold kvModelOn at hA ⊢; rw [← hA, hAL]; exact this
  imod Hp with ⟨HL, %Hle⟩
  imod Hclose $$ [HL Hσ' Hh] with -
  · inext; iexists L; iframe HL Hσ' Hh Hw; ipureintro; exact Hok'
  imodintro
  iunfold etcdKV
  iframe Hσ
  ipureintro
  rw [← Hag]
  simp only [kvStateOf_rev]
  unfold kvModelOn at *
  simp only at hlen
  omega
-/

end lemmas

section commit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The mode-`on` KV invariant's pure facts, one committed entry on** (`kvInv_facts_snoc`'s):
the entry meets the committer's obligation (`commitOkOn`: admitted and determinate at the model's
state after `L`), and its index the next. -/
theorem kvInvOn_facts_snoc (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (L : List EntryModel) (e : EntryModel)
    (hok : plainLogOn L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) L ∧ srvIdxOkW γ.ai0 L ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [])
    (hidx' : srvIdxOkW γ.ai0 (L ++ [e]))
    (hc : commitOkOn γk.c0 γk.ch0 (st₀, γk.log0) L e) :
    plainLogOn (L ++ [e]) ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) (L ++ [e]) ∧
      srvIdxOkW γ.ai0 (L ++ [e]) ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [] := by
  obtain ⟨hp, hd, -, hc0, hch, h0⟩ := hok
  obtain ⟨hp', hd'⟩ := logOn_snoc γk.c0 γk.ch0 (st₀, γk.log0) L e hp hd hc
  exact ⟨hp', hd', hidx', hc0, hch, h0⟩

/-- **A granted plain write's commit fires its client's update** (the ghost step at the commit, in
the mode `on`): the invariant's half of the state's ghost variable at the committed log `L`'s model
and a client's `etcdKV` at `σ` agree, and both move to the request's step, which is the model's
state after `L ++ [e]` (`kvModelOn_snoc_granted`). -/
theorem kvInvOn_commit_granted (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (σ : KVState)
    (hch : γk.ch0 = apply.alarmChain true false false)
    (h0 : γk.log0 ≠ []) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (hna : apply.needAdminPermission rq = false)
    (hg : kvGranted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1 rq) (hpc : plainCover rq) :
    ⊢ ghostVar (GF := GF) γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) -∗ etcdKV γk σ ==∗
      ⌜σ = kvStateOf (kvModelOn γk st₀ L)⌝ ∗
      ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ (L ++ [e]))) ∗
      etcdKV γk (kvReqStep rq σ) := by
  iintro Hσ Hc
  iunfold etcdKV at Hc
  ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ Hc
  have hst := kvModelOn_snoc_granted γk st₀ L e rq hch h0 ht hd hdec hidx hna hg hpc
  imod ghostVar_update_halves (kvReqStep rq σ) γk.st _ _ $$ Hσ Hc with ⟨Hσ, Hc⟩
  imodintro
  isplitr
  · ipureintro; exact Hag.symm
  rw [hst, Hag]
  iframe Hσ
  iunfold etcdKV
  iexact Hc

/-- **An entry that keeps the KV log keeps the state** (an admin entry, `kvModelOn_snoc_admin`, or
a refused KV entry, `kvModelOn_snoc_refused`): the invariant's half moves to `L ++ [e]` unchanged,
no client's update fires. -/
theorem kvInvOn_commit_keep (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (hk : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L) :
    ghostVar (GF := GF) γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) ⊢
      ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ (L ++ [e]))) := by
  rw [hk]

end commit

end EtcdGrove
end Perennial
