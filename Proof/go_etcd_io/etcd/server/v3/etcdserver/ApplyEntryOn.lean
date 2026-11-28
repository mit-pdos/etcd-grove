/-
**The apply thread's KV entry in the auth mode `on`: the certificates it can give** (the auth plan's
E3f, 2026-10-27; `notes/decisions.md`, "E3f of the auth plan"). Lean-first (no Rocq counterpart).

`apply.Apply` asks of a KV entry the certificates of the logs its outcomes leave (`certPre`, what
the store's writer mints a revision's token on). With auth on, the auth chain's relation admits the
write whatever the latest state says (the auth layer's mode-generic triples decide at some recorded
state), but the apply thread certifies only the mode-`on` model's log after the entry
(`kv_applied_step_on`), which a write the latest state refuses is not. So the latest-state triples
ask only the certificates of the outcomes their verdict admits (`apply.certPreW`, `kvOutL`), and
those the apply thread gives: such an outcome is the model's (`outcomeOn_of_kvOutL`, `outcomeOn_eq`
at a determinate entry), whose log it certified (`kv_certPreW_on`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVOutcomeOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- A request that is no alarm keeps the chain through `apply.Apply`. -/
theorem applyStep_chain_nonAlarm (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hk : apply.dispatchKind rq ≠ .alarm) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain := by
  cases out with
  | skipped => obtain ⟨-, rfl⟩ := h; rfl
  | rejected => obtain ⟨-, rfl⟩ := h; rfl
  | dispatched o skip =>
    obtain ⟨-, -, -, hc⟩ := h
    rcases hc with hc | ⟨-, hk', -⟩
    · exact hc
    · exact absurd hk' hk

/-- **After `apply.Apply` on a KV entry in the mode `on`, the apply thread's state is the model's**
(`apply.Apply.kvSpecL`'s post): a KV request of the auth-on log at the lease mode `lm` (auth-lease S3a2: a
leased put or transaction too) of the entry `m` above `c₀`, applied with `v3` at the start chain with auth on,
its dispatched outcome decided at the latest state of `hs` (whose latest state is the model's `st`) and, unless
plain, lease-exact at the model's table, determinate there: the chain kept, and the auth state and the log after
the model's step (`kvEntryOn`). -/
theorem kvOn_after_kv (lm : lease.Mode) (c₀ : w64) (st : auth.AuthState) (lt : LeaseTable) (x x' : apply.ApplyKV)
    (m : EntryModel) (rq : apply.IRRModel) (out : apply.ApplyOut)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainReqL lm rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hz : noZeroEnds rq)
    (hdet : entryDetOn c₀ (st, x.log, lt) m) (hch : x.chain = apply.alarmChain true false false)
    (hstep : apply.applyStep rq true x x' out)
    (hout : ∀ o b, out = .dispatched o b →
      apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o ∧
        (plainCover rq ∨ apply.leaseExactL lt.ids rq x.log o)) :
    x'.chain = x.chain ∧ (st, x'.log, lt) = kvEntryOn c₀ x.chain (st, x.log, lt) m := by
  have hns := (plainReqL_facts lm rq hp).1
  have hc := applyStep_chain_nonAlarm rq true x x' out
    (fun h => by rw [h] at hk; simp [apply.isKVKind] at hk) hstep
  refine ⟨hc, ?_⟩
  cases out with
  | skipped =>
    obtain ⟨hn, -⟩ := hstep; rw [hns] at hn; cases hn
  | rejected =>
    obtain ⟨hn, -⟩ := hstep; rw [hna] at hn; cases hn
  | dispatched o b =>
    obtain ⟨-, -, hlog, -⟩ := hstep
    obtain ⟨hk1, hex⟩ := hout o b rfl
    have ho := outcomeOn_of_kvOutLL lm c₀ (st, x.log, lt) m rq ht hd hdec hv hna hk hp γa hs hl hz o hk1 hex
    rw [hlog, hch]
    exact outcomeOn_eq c₀ _ (st, x.log, lt) _ m hdet ho

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

variable [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions] in
open Iris.ProofMode in
/-- **`kvOutLT`'s certificate at another live set that agrees when leases are granted** (auth-lease S3a2 §4:
the model's table and the server's `srvIds`). -/
theorem certPreVW_kvOutLT_tie (E : apply.AEnv GF) (v3 : Bool) (c : apply.Chain) (rq : apply.IRRModel)
    (log : mvcc.Log) (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (ci : apply.Chain)
    (T T' : List w64) (h : E.lg = true → T = T') :
    apply.certPreVW v3 E c rq log (apply.kvOutLT M E.lg hs ai ci rq log T) ⊢
      apply.certPreVW v3 E c rq log (apply.kvOutLT M E.lg hs ai ci rq log T') := by
  cases v3
  · simp only [apply.certPreVW, Bool.false_eq_true, ↓reduceIte]; exact .rfl
  · simp only [apply.certPreVW, ↓reduceIte]
    iapply apply.certPreW_mono
    intro oc hy
    exact ⟨hy.1, fun hg => (h hg) ▸ hy.2 hg⟩

variable [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions] in
open Iris.ProofMode in
/-- **`kvOutL`'s certificate is `kvOutLT`'s** (fewer outcomes; auth-lease S3a2: the revocation's). -/
theorem certPreVW_kvOutLT_other (E : apply.AEnv GF) (v3 : Bool) (c : apply.Chain) (rq : apply.IRRModel)
    (log : mvcc.Log) (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (ci : apply.Chain)
    (T : List w64) :
    apply.certPreVW v3 E c rq log (apply.kvOutL M hs ai ci rq log) ⊢
      apply.certPreVW v3 E c rq log (apply.kvOutLT M E.lg hs ai ci rq log T) := by
  cases v3
  · simp only [apply.certPreVW, Bool.false_eq_true, ↓reduceIte]; exact .rfl
  · simp only [apply.certPreVW, ↓reduceIte]
    iapply apply.certPreW_mono
    intro oc hy
    exact hy.1

/-- **The certificates a KV entry's latest-state outcomes need, in the mode `on`** (see the file
header): for a plain KV request of the entry `m` above `c₀`, at the start chain with auth on and
no alarm, determinate at the model's state `s` (whose auth part is the latest state of `hs`),
without `"\x00"` range ends (a transaction's verdict on its own permissions by
`txnVerdictOwn_of`, E3e), every outcome the verdict at the latest
state admits leaves the model's log after `m`, which has the mode's raft witness (strict M1,
2026-11-06: `kvNxOn`, which `srvKVInvsOn` ties `E.Nx` to, in place of the KV certificate `kvCert`
and mvcc's `certOk`, as `kv_certPre`). -/
theorem kv_certPreW_on (E : apply.AEnv GF) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) (hNx : E.Nx = kvNxOn γ γk st₀) (c₀ : w64)
    (s : OnState) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainReqL γk.lm rq)
    (hlm : E.lg = false → γk.lm = .none)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (hdet : entryDetOn c₀ s m) :
    kvNxOn (GF := GF) γ γk st₀ (kvEntryOn c₀ (apply.alarmChain true false false) s m).2.1 ⊢
      apply.certPreW E (apply.alarmChain true false false) rq s.2.1
        (apply.kvOutLT (.on γa) E.lg hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2.1 s.2.2.ids) := by
  iintro #Hc
  iunfold apply.certPreW
  iintro !> %oc %h
  have hex : plainCover rq ∨ apply.leaseExactL s.2.2.ids rq s.2.1 oc := by
    cases hg : E.lg
    · left
      have hp0 : plainReqL .none rq := by rw [← hlm hg]; exact hp
      exact ((plainReqL_none rq).1 hp0).1
    · right; exact h.2.2 hg
  have ho := outcomeOn_of_kvOutLL γk.lm c₀ s m rq ht hd hdec hv hna hk hp γa hs hl hz oc h.2.1 hex
  have he := outcomeOn_eq c₀ _ s _ m hdet ho
  have hlog : oc.logAfter s.2.1 = (kvEntryOn c₀ (apply.alarmChain true false false) s m).2.1 := by
    rw [← he]
  rw [hlog, hNx]
  iexact Hc

/-- `kv_certPreW_on` with `v3` (`certPreVW`), the form `apply.Apply.kvSpecL` takes. -/
theorem kv_certPreVW_on (E : apply.AEnv GF) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) (hNx : E.Nx = kvNxOn γ γk st₀) (c₀ : w64)
    (s : OnState) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainReqL γk.lm rq)
    (hlm : E.lg = false → γk.lm = .none)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (hdet : entryDetOn c₀ s m) :
    kvNxOn (GF := GF) γ γk st₀ (kvEntryOn c₀ (apply.alarmChain true false false) s m).2.1 ⊢
      apply.certPreVW true E (apply.alarmChain true false false) rq s.2.1
        (apply.kvOutLT (.on γa) E.lg hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2.1 s.2.2.ids) := by
  simp only [apply.certPreVW, ↓reduceIte]
  exact kv_certPreW_on E γ γk st₀ hNx c₀ s m rq ht hd hdec hv hna hk hp hlm γa hs hl hz hdet

/-- **Before `apply.Apply` on a KV entry, in the mode `on`** (the apply thread's ghost step ahead of
the call, `kv_applied_step_on`): the next committed entry `m`, a KV request, is plain
(`plainCover`: the mode-`on` log's entries of a KV kind are), with no range end `"\x00"`
(`noZeroEnds`: since E3o the log keeps it), determinate at the apply thread's state, the chain the start's; the model's state after it certified, and so the certificates the
latest-state triple asks (`certPreVW`, `kv_certPreVW_on`). -/
theorem kv_entry_pre_on (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : apply.ApplyKV) (st : auth.AuthState)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z γr.kv.c0 < uint.Z m.index)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log, kvLeasesOn γr.kv st₀ A) m).2.1.length < 2 ^ 63) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st (kvLeasesOn γr.kv st₀ A) -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainReqL γr.kv.lm rq ∧ apply.needAdminPermission rq = false ∧
        entryDetOn γr.kv.c0 (st, x.log, kvLeasesOn γr.kv st₀ A) m ∧ x.chain = apply.alarmChain true false false ∧
        noZeroEnds rq⌝ ∗
      apply.certPreVW true E x.chain rq x.log
        (apply.kvOutLT (.on γa) E.lg hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          x.log (kvLeasesOn γr.kv st₀ A).ids) ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) (kvEntryOn γr.kv.c0 x.chain (st, x.log, kvLeasesOn γr.kv st₀ A) m) := by
  iintro #Hinvs Ha #Hlb
  ihave #Hinvs' := Hinvs
  iunfold srvKVInvsOn at Hinvs'
  icases Hinvs' with ⟨-, -, -, -, -, -, %HNx, %Hrows, -⟩
  imod kv_applied_step_on E γr st₀ A m x st _ hlen $$ Hinvs Ha Hlb with ⟨%Hp, Ha⟩
  obtain ⟨Hpl, hdet, -, hch⟩ := Hp
  -- (auth-lease S3a2) a KV request of the auth-on log at its lease mode (a leased put or transaction too)
  have hpz : plainReqL γr.kv.lm rq ∧ noZeroEnds rq := by
    rcases Hpl ht hd rq hdec with ((⟨h1, h2⟩ | h | h) | h)
    · exact ⟨h1, h2⟩
    · exfalso; rw [h.2.1] at hk; simp [apply.isKVKind] at hk
    · exfalso; rw [h.2.1] at hk; simp [apply.isKVKind] at hk
    · exfalso
      obtain ⟨h, -⟩ := h
      unfold apply.adminKindOk at h
      split at h <;> rename_i hkd <;> simp_all [apply.isKVKind]
  obtain ⟨hp, hz⟩ := hpz
  have hna : apply.needAdminPermission rq = false := (plainReqL_facts _ rq hp).2.1
  have hlm : E.lg = false → γr.kv.lm = .none := fun hg => by
    rw [Hrows.2.1]; exact apply.AEnv.lm_of_lg_false hg
  ihave #Hinvs'' := Hinvs
  iunfold srvKVInvsOn at Hinvs''
  icases Hinvs'' with ⟨#HkI, -, #HrI, -⟩
  imod (kvInvOn_keysA γr st₀ (A ++ [m])) $$ HkI HrI Hlb with %Hkeys
  ihave #Hc : iprop(kvNxOn γr.raft γr.kv st₀ (kvEntryOn γr.kv.c0 x.chain (st, x.log, kvLeasesOn γr.kv st₀ A) m).2.1) $$ [Ha]
  · iunfold kvAppliedLOn at Ha; icases Ha with ⟨#HA, -, -, %HAs⟩
    iunfold kvNxOn; iexists A ++ [m]; iframe HA; ipureintro; rw [HAs]; exact ⟨rfl, Hkeys⟩
  imodintro
  iframe Ha
  isplitr
  · ipureintro; exact ⟨hp, hna, hdet, hch, hz⟩
  ihave #Hc' : iprop(kvNxOn γr.raft γr.kv st₀
      (kvEntryOn γr.kv.c0 (apply.alarmChain true false false) (st, x.log, kvLeasesOn γr.kv st₀ A) m).2.1) $$ []
  · rw [← hch]; iexact Hc
  rw [hch]
  iapply kv_certPreVW_on E γr.raft γr.kv st₀ HNx γr.kv.c0 (st, x.log, kvLeasesOn γr.kv st₀ A) m rq ht hd hdec hv hna hk hp
    hlm γa hs hl hz hdet $$ Hc'

/-- **After `apply.Apply` on a KV entry, in the mode `on`** (`kvOn_after_kv` on the apply thread's
ghost state): the model's state after `m`, certified ahead (`kv_entry_pre_on`), is the apply
thread's at its new state `x'`, at the same auth state `st`. -/
theorem kv_entry_post_on (γr : ReadNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (m : EntryModel) (x x' : apply.ApplyKV) (st : auth.AuthState)
    (lt' : LeaseTable) (hc : x'.chain = x.chain)
    (hx : (st, x'.log, lt') = kvEntryOn γr.kv.c0 x.chain (st, x.log, kvLeasesOn γr.kv st₀ A) m)
    (hch : x.chain = γr.kv.ch0) :
    kvAppliedLOn (GF := GF) γr.raft γr.kv st₀ (A ++ [m])
        (kvEntryOn γr.kv.c0 x.chain (st, x.log, kvLeasesOn γr.kv st₀ A) m) ⊢
      kvAppliedOn γr.raft γr.kv st₀ (A ++ [m]) x' st (kvLeasesOn γr.kv st₀ (A ++ [m])) := by
  rw [← hx]
  iintro Ha
  ihave %Heq : ⌜(st, x'.log, lt') = kvRaftOfOn γr.kv.c0 γr.kv.ch0 (st₀, γr.kv.log0, []) (A ++ [m])⌝ $$ [Ha]
  · iunfold kvAppliedLOn at Ha; icases Ha with ⟨-, -, -, %h⟩; ipureintro; exact h
  have hl : kvLeasesOn γr.kv st₀ (A ++ [m]) = lt' := by unfold kvLeasesOn; rw [← Heq]
  rw [hl]
  iunfold kvAppliedOn
  iframe Ha
  ipureintro; rw [hc, hch]

end lemmas

end EtcdGrove
end Perennial
