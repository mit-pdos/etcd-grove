/-
**The apply thread's KV ghost state** (unit T1, 2026-10-14; `notes/decisions.md`, "Put and Get as
persistent atomic updates linearized by raft"): the apply thread at the committed raft log `A`
(`kvApplied`: its KV log the model of `A`, certified) applies the next committed entry `m`. The
KV invariant keeps the committed log plain, so `m` is plain and the chain is the start's (auth
disabled): the log after `m` is the model's (`batchStep_plain`), whose certificate the apply
thread mints before applying `m` (`kv_applied_step`), as the store's write transaction asks of
its commit (`apply.certPre`, `kv_certPre`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

/-! ## Pure facts of the model -/

/-- A request the backend does not write changes no log through any chain. -/
theorem chainLog_of_backendLog (rq : apply.IRRModel) (log : mvcc.Log)
    (h : backendLog rq log = log) : ∀ c : apply.Chain, chainLog c rq log = log := by
  intro c
  induction c with
  | backend => simpa only [chainLog] using h
  | corrupt c ih => simp only [chainLog]; split <;> simp [ih]
  | capped c ih => simp only [chainLog]; split <;> simp [ih]
  | auth _ c ih => simp only [chainLog]; exact ih
  | quota c ih => simp only [chainLog]; exact ih

/-- An entry whose request changes no log through any chain keeps the model. -/
theorem kvEntry_of_chainLog (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (m : EntryModel)
    (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (h : ∀ c : apply.Chain, chainLog c rq log = log) : kvEntry c₀ ch log m = log := by
  unfold kvEntry
  split
  · split
    · rfl
    · rw [hdec]
      simp only
      unfold dispatchLog
      split
      · rfl
      · split
        · exact h ch
        · rfl
  · rfl

/-- **An entry's model log is within the revision budget** when its request's premises hold
(`entryOk`: a put's or a delete's room for one more revision). -/
theorem kvEntry_len (c₀ : w64) (ch : apply.Chain) (x : apply.ApplyKV) (m : EntryModel)
    (hok : entryOk x m) (hl : x.log.length < 2 ^ 63) :
    (kvEntry c₀ ch x.log m).length < 2 ^ 63 := by
  rcases kvEntry_grow c₀ ch x.log m with h | ⟨cs, h⟩
  · rw [h]; exact hl
  · rcases hok with hd | ⟨rq, hdec, -, hrq, -⟩
    · rw [kvEntry_nonwrite c₀ ch x.log m (Or.inl hd)] at h; simp at h
    · by_cases hk : writeKind (apply.dispatchKind rq)
      · rw [h, List.length_append, List.length_singleton]
        rcases hk with hk | hk | hk
        · have := hrq; simp only [apply.rqOk, hk, apply.putOk] at this; omega
        · cases ho : rq.deleteRange with
          | some o =>
            have := hrq; simp only [apply.rqOk, hk] at this
            have : apply.delOk x.log o := this o ho
            unfold apply.delOk at this; omega
          | none =>
            have hb : backendLog rq x.log = x.log := by
              unfold backendLog; rw [hk]; simp only [ho]
            rw [kvEntry_of_chainLog c₀ ch x.log m rq hdec (chainLog_of_backendLog rq x.log hb)] at h
            simp at h
        · cases ho : rq.txn with
          | some t =>
            have := hrq; simp only [apply.rqOk, hk] at this
            have := (this t ho).1; omega
          | none =>
            have hb : backendLog rq x.log = x.log := by
              unfold backendLog; rw [hk]; simp only [ho]
            rw [kvEntry_of_chainLog c₀ ch x.log m rq hdec (chainLog_of_backendLog rq x.log hb)] at h
            simp at h
      · have hnw : ∀ rq', apply.irrDecode m.data = some rq' →
            ¬ writeKind (apply.dispatchKind rq') := by
          intro rq' h'; rw [hdec] at h'; cases h'
          exact hk
        rw [kvEntry_nonwrite c₀ ch x.log m (Or.inr (Or.inr hnw))] at h; simp at h

/-- **A dispatched request's chain log is the entry's model log** (`v3`: above `c₀`). -/
theorem kvEntry_chainLog (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index) :
    chainLog ch rq log = kvEntry c₀ ch log m := by
  unfold kvEntry
  rw [if_pos ht, if_neg hd, hdec]
  simp only
  unfold dispatchLog
  rw [decide_eq_true hv]
  by_cases hk : writeKind (apply.dispatchKind rq)
  · have h1 : apply.preV3Kind (apply.dispatchKind rq) = false := by
      rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
    have h2 : apply.storeKind (apply.dispatchKind rq) = true := by
      rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
    simp [h1, h2]
  · have hn := chainLog_nonwrite rq log hk ch
    rw [hn]
    split <;> (try split) <;> simp [hn]

/-- `batchStep` from an entry step, at `v3` as the model's. -/
theorem batchStep_of_entryStep (c₀ : w64) (m : EntryModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (ht : m.typ = W32 0) (hv : v3 = decide (uint.Z c₀ < uint.Z m.index))
    (h : entryStep m v3 x x' out) : batchStep c₀ m x x' := by
  unfold batchStep; rw [if_pos ht]; subst hv; exact ⟨out, h⟩

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The committed log is plain** (the KV invariant's), and the start's chain the base chain with
auth disabled. -/
theorem kv_log_plain (γ : ServerRaftNames) (γk : KVNames) (B : List EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ B ={⊤}=∗
      ⌜plainLog B ∧ γk.ch0 = apply.alarmChain false false false⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L B $$ Hr HL HB with ⟨HL, -, %Hp⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  exact ⟨fun m hm => Hok.1 m (Hp.subset hm), Hok.2.2.2.1⟩

/-- A KV certificate is the store's (at the server's names). -/
theorem kvCert_certOk (γk : KVNames) (γs : mvcc.StoreNames) (hγ : γs.cok = γk.cok)
    (l : mvcc.Log) : kvCert (GF := GF) γk l ⊢ mvcc.certOk γs l := by
  unfold kvCert mvcc.certOk
  rw [hγ]
  iintro (%h | #H)
  · ileft; ipureintro; exact h
  · iright; ileft; iexact H

/-- **The certificates `apply.Apply` asks of a plain entry's request** (`certPreV`): with `v3`,
every outcome's log is the entry's model log (auth disabled), which is certified. -/
theorem kv_certPre (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (x : apply.ApplyKV) (m : EntryModel) (rq : apply.IRRModel) (v3 : Bool)
    (hp : plainCover rq) (hoff : x.chain.kvExact = true) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : v3 = decide (uint.Z c₀ < uint.Z m.index)) :
    kvCert (GF := GF) γk (kvEntry c₀ x.chain x.log m) ⊢ apply.certPreV v3 E x.chain rq x.log := by
  iintro #Hc
  cases v3
  · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
  · have hv' : uint.Z c₀ < uint.Z m.index := of_decide_eq_true hv.symm
    simp only [apply.certPreV, ↓reduceIte]
    unfold apply.certPre
    imodintro
    iintro %oc %hs
    rcases chainStep_plain x.chain rq x.log oc hp hs with h | ⟨-, h⟩
    · rw [h, kvEntry_chainLog c₀ x.chain x.log m rq ht hd hdec hv']
      iapply kvCert_certOk γk E.γ hγ $$ Hc
    · rw [hoff] at h; cases h

/-- **The apply thread's step on the next committed entry `m`**: `m` plain, the chain the start's
(auth disabled), the log after `m` the model's, certified (`kv_cert_step`). -/
theorem kv_applied_step (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel)
    (m : EntryModel) (x : apply.ApplyKV)
    (hlen : (kvEntry γr.kv.c0 x.chain x.log m).length < 2 ^ 63) :
    ⊢ srvKVInvs (GF := GF) E γr -∗ kvApplied γr.raft γr.kv A x -∗ srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainEntry m ∧ x.chain = γr.kv.ch0 ∧ x.chain.kvExact = true⌝ ∗
      kvAppliedL γr.raft γr.kv (A ++ [m]) (kvEntry γr.kv.c0 x.chain x.log m) := by
  iintro #Hinvs Ha #Hlb
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, %Hcok⟩
  iunfold kvApplied at Ha
  icases Ha with ⟨Ha, %Hch⟩
  imod kv_log_plain γr.raft γr.kv (A ++ [m]) $$ HkI HrI Hlb with %Hpc
  obtain ⟨Hpl, Hch0⟩ := Hpc
  ihave %Hl : iprop(⌜x.log = kvModel γr.kv A⌝) $$ [Ha]
  · iunfold kvAppliedL at Ha; icases Ha with ⟨-, -, -, %h⟩; ipureintro; exact h
  have hl' : kvEntry γr.kv.c0 x.chain x.log m = kvModel γr.kv (A ++ [m]) := by
    unfold kvModel; rw [kvRaftOf_snoc, Hch, Hl]; rfl
  imod kv_cert_step γr.raft γr.kv ⊤ (fun _ _ => CoPset.mem_full) A m x.log _ hl'
    (kvEntry_grow γr.kv.c0 x.chain x.log m) hlen $$ HcI Ha Hlb with Ha
  imodintro
  iframe Ha
  ipureintro
  refine ⟨Hpl m (by simp), Hch, ?_⟩
  rw [Hch, Hch0]; rfl

/-- The apply thread's KV log is the model of its applied raft log (unit W-M3: for the result's
tie, `entryWit`). -/
theorem kvApplied_log (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (x : apply.ApplyKV) :
    kvApplied (GF := GF) γ γk A x ⊢ kvApplied γ γk A x ∗ ⌜x.log = kvModel γk A⌝ := by
  iintro H
  iunfold kvApplied at H
  icases H with ⟨H, %Hch⟩
  iunfold kvAppliedL at H
  icases H with ⟨#HB, Hhi, #Hc, %Hl⟩
  isplitl
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HB Hhi Hc
    ipureintro; exact ⟨Hl, Hch⟩
  · ipureintro; exact Hl

/-- A namespace `nroot.@x` inside `⊤` without two other ones. -/
theorem mask_ndot_ne2 (x y z : String) (hxy : x ≠ y) (hxz : x ≠ z) :
    (↑(nroot.@x) : CoPset) ⊆ (⊤ \ ↑(nroot.@y)) \ ↑(nroot.@z) :=
  Perennial.mask_ndot_ne2 nroot x y z hxy hxz

/-- **A certified log is below the committed KV state** (unit W-M3): the state `σ` of a holder of
`etcdKV` is the state of the committed raft log's model (the KV invariant's other half), and a
log the server certified (`certOk` at the KV's names) is the model of a committed raft prefix
(`kv_cert_read`), or has at most `NewStore`'s two revisions, so its length is at most `σ`'s
revision and one. Any mask without the three invariants' namespaces (a client's invariant
holding `etcdKV` open: `nroot.@x`). -/
theorem kv_cert_floor (γ : ServerRaftNames) (γk : KVNames) (γs : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (x : String) (hx1 : x ≠ "server_kv") (hx2 : x ≠ "server_kv_cert")
    (hx3 : x ≠ "raft_commit") (l : mvcc.Log) (σ : KVState) :
    ⊢ kvInv (GF := GF) γ γk -∗ kvCertInv γ γk -∗ srvRaftLogInv γ -∗ mvcc.certOk γs l -∗
      etcdKV γk σ ={⊤ \ ↑(nroot.@x)}=∗ etcdKV γk σ ∗ ⌜l.length ≤ σ.rev + 1⌝ := by
  have hc : (↑kvcN : CoPset) ⊆ ⊤ \ ↑(nroot.@x) := mask_ndot_ne' nroot "server_kv_cert" x (Ne.symm hx2)
  have hk : (↑kvN : CoPset) ⊆ ⊤ \ ↑(nroot.@x) := mask_ndot_ne' nroot "server_kv" x (Ne.symm hx1)
  have hr : (↑srvRaftN : CoPset) ⊆ (⊤ \ ↑(nroot.@x)) \ ↑kvN :=
    mask_ndot_ne2 "raft_commit" x "server_kv" (Ne.symm hx3) (by decide)
  iintro #HkI #HcI #HrI #Hc Hσ
  -- the start log has two revisions (the certificates' invariant)
  ihave #HcI' := HcI
  iunfold kvCertInv at HcI'
  iinv HcI' with >Hi Hclose
  icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
  imod Hclose $$ [HC Hhi'] with -
  · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
  have h2 := Hok.2
  imod kv_cert_read γ γk γs hγ (⊤ \ ↑(nroot.@x)) hc l $$ HcI Hc with Hcase
  ihave #HkI' := HkI
  iunfold kvInv at HkI'
  iinv HkI' with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ', %Hok', #Hw⟩
  iunfold etcdKV at Hσ
  ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ' Hσ
  have hlen := (kvRaftOf_extends γk.c0 γk.ch0 γk.log0 L).length_le
  ihave Hp : iprop(|={(⊤ \ ↑(nroot.@x)) \ ↑kvN}=> srvRLog γ L ∗
      ⌜l.length ≤ (kvModel γk L).length⌝) $$ [HL Hcase]
  · icases Hcase with (%hl | ⟨%A, #HA, %hA⟩)
    · imodintro; iframe HL; ipureintro; unfold kvModel; omega
    · imod srvRLog_lb γ ((⊤ \ ↑(nroot.@x)) \ ↑kvN) hr L A $$ HrI HL HA with ⟨HL, -, %Hp⟩
      imodintro; iframe HL; ipureintro
      have := (kvRaftOf_prefix γk.c0 γk.ch0 γk.log0 A L Hp).length_le
      unfold kvModel at hA ⊢; rw [← hA]; exact this
  imod Hp with ⟨HL, %Hle⟩
  imod Hclose $$ [HL Hσ'] with -
  · inext; iexists L; iframe HL Hσ' Hw; ipureintro; exact Hok'
  imodintro
  iunfold etcdKV
  iframe Hσ
  ipureintro
  rw [← Hag]
  simp only [kvStateOf]
  unfold kvModel at *
  omega

/-- The certificate in the apply thread's KV ghost state. -/
theorem kvAppliedL_cert (γ : ServerRaftNames) (γk : KVNames) (B : List EntryModel) (l : mvcc.Log) :
    kvAppliedL (GF := GF) γ γk B l ⊢ kvAppliedL γ γk B l ∗ kvCert γk l := by
  iintro H
  iunfold kvAppliedL at H
  icases H with ⟨#HB, Hhi, #Hc, %Hl⟩
  iframe Hc
  iunfold kvAppliedL
  iframe HB Hhi Hc
  ipureintro; exact Hl

/-- **After the entry**: the apply thread's KV ghost state at the next state `x'` (its log the
model's, the chain the start's), and the applied log's raft log for the read side
(`kvLogAt`, at the entry's index). -/
theorem kvApplied_next (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (x x' : apply.ApplyKV) (i : w64)
    (hi : uint.Z i = uint.Z γr.raft.ai0 + A.length + 1)
    (hl : x'.log = kvEntry γr.kv.c0 x.chain x.log m) (hc : x'.chain = γr.kv.ch0) :
    kvAppliedL (GF := GF) γr.raft γr.kv (A ++ [m]) (kvEntry γr.kv.c0 x.chain x.log m) ⊢
      kvApplied γr.raft γr.kv (A ++ [m]) x' ∗ kvLogAt γr i x'.log := by
  rw [← hl]
  iintro H
  iunfold kvAppliedL at H
  icases H with ⟨#HB, Hhi, #Hc, %Hl⟩
  isplitl [Hhi]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HB Hhi Hc
    ipureintro; exact ⟨Hl, hc⟩
  iunfold kvLogAt
  iexists A ++ [m]
  iframe HB
  ipureintro
  refine ⟨?_, Hl⟩
  simp only [List.length_append, List.length_singleton]
  push_cast
  omega

end lemmas

end EtcdGrove
end Perennial
