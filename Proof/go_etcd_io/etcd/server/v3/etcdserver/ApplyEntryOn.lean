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

/-- **After `apply.Apply` on a KV entry in the mode `on`, the apply thread's state is the model's**
(`apply.Apply.kvSpecL`'s post): a plain KV request of the entry `m` above `c₀`, applied with `v3` at
the start chain with auth on, its dispatched outcome decided at the latest state of `hs` (whose
latest state is the model's `st`), determinate there: the chain kept, and the auth state and the
log after the model's step (`kvEntryOn`). -/
theorem kvOn_after_kv (c₀ : w64) (st : auth.AuthState) (x x' : apply.ApplyKV) (m : EntryModel)
    (rq : apply.IRRModel) (out : apply.ApplyOut)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hz : noZeroEnds rq)
    (hdet : entryDetOn c₀ (st, x.log) m) (hch : x.chain = apply.alarmChain true false false)
    (hstep : apply.applyStep rq true x x' out)
    (hout : ∀ o b, out = .dispatched o b →
      apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o) :
    x'.chain = x.chain ∧ (st, x'.log) = kvEntryOn c₀ x.chain (st, x.log) m := by
  have hc := (applyStep_plain [] rq true x x' out hp hstep).1
  refine ⟨hc, ?_⟩
  cases out with
  | skipped =>
    obtain ⟨hn, -⟩ := hstep
    have := hp; unfold plainCover at this
    have hk' := hk
    unfold apply.isKVKind at hk'
    split at this <;> simp_all
  | rejected =>
    obtain ⟨hn, -⟩ := hstep; rw [hna] at hn; cases hn
  | dispatched o b =>
    obtain ⟨-, -, hlog, -⟩ := hstep
    have ho := outcomeOn_of_kvOutL c₀ (st, x.log) m rq ht hd hdec hv hna hk hp γa hs hl hz o
      (hout o b rfl)
    rw [hlog, hch]
    exact outcomeOn_eq c₀ _ (st, x.log) _ m hdet ho

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The certificates a KV entry's latest-state outcomes need, in the mode `on`** (see the file
header): for a plain KV request of the entry `m` above `c₀`, at the start chain with auth on and
no alarm, determinate at the model's state `s` (whose auth part is the latest state of `hs`),
without `"\x00"` range ends (a transaction's verdict on its own permissions by
`txnVerdictOwn_of`, E3e), every outcome the verdict at the latest
state admits leaves the model's log after `m`, which `kvCert` certifies. -/
theorem kv_certPreW_on (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (s : auth.AuthState × mvcc.Log) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (hdet : entryDetOn c₀ s m) :
    kvCert (GF := GF) γk (kvEntryOn c₀ (apply.alarmChain true false false) s m).2 ⊢
      apply.certPreW E (apply.alarmChain true false false) rq s.2
        (apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2) := by
  iintro #Hc
  iunfold apply.certPreW
  iintro !> %oc %h
  have ho := outcomeOn_of_kvOutL c₀ s m rq ht hd hdec hv hna hk hp γa hs hl hz oc h.2
  have he := outcomeOn_eq c₀ _ s _ m hdet ho
  have hlog : oc.logAfter s.2 = (kvEntryOn c₀ (apply.alarmChain true false false) s m).2 := by
    rw [← he]
  rw [hlog]
  iapply kvCert_certOk γk E.γ hγ $$ Hc

/-- `kv_certPreW_on` with `v3` (`certPreVW`), the form `apply.Apply.kvSpecL` takes. -/
theorem kv_certPreVW_on (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (s : auth.AuthState × mvcc.Log) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (hdet : entryDetOn c₀ s m) :
    kvCert (GF := GF) γk (kvEntryOn c₀ (apply.alarmChain true false false) s m).2 ⊢
      apply.certPreVW true E (apply.alarmChain true false false) rq s.2
        (apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2) := by
  simp only [apply.certPreVW, ↓reduceIte]
  exact kv_certPreW_on E γk hγ c₀ s m rq ht hd hdec hv hna hk hp γa hs hl hz hdet

/-- **Before `apply.Apply` on a KV entry, in the mode `on`** (the apply thread's ghost step ahead of
the call, `kv_applied_step_on`): the next committed entry `m`, a KV request, is plain
(`plainCover`: the mode-`on` log's entries of a KV kind are), with no range end `"\x00"` and its
checks of the cache's shape (`noZeroEnds`, `kvShapeAll`: since E3o the log keeps them), determinate at the apply thread's
state, the chain the start's; the model's state after it certified, and so the certificates the
latest-state triple asks (`certPreVW`, `kv_certPreVW_on`). -/
theorem kv_entry_pre_on (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : apply.ApplyKV) (st : auth.AuthState)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z γr.kv.c0 < uint.Z m.index)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log) m).2.length < 2 ^ 63) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainCover rq ∧ apply.needAdminPermission rq = false ∧
        entryDetOn γr.kv.c0 (st, x.log) m ∧ x.chain = apply.alarmChain true false false ∧
        noZeroEnds rq ∧ kvShapeAll rq⌝ ∗
      apply.certPreVW true E x.chain rq x.log
        (apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          x.log) ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) (kvEntryOn γr.kv.c0 x.chain (st, x.log) m) := by
  iintro #Hinvs Ha #Hlb
  ihave #Hinvs' := Hinvs
  iunfold srvKVInvsOn at Hinvs'
  icases Hinvs' with ⟨-, -, -, %Hcok⟩
  imod kv_applied_step_on E γr st₀ A m x st hlen $$ Hinvs Ha Hlb with ⟨%Hp, Ha⟩
  obtain ⟨Hpl, hdet, -, hch⟩ := Hp
  have hpz : plainCover rq ∧ noZeroEnds rq ∧ kvShapeAll rq := by
    rcases Hpl ht hd rq hdec with h | h
    · exact ⟨h.1.1, h.2⟩
    · exfalso
      obtain ⟨h, -⟩ := h
      unfold apply.adminKindOk at h
      split at h <;> rename_i hkd <;> simp_all [apply.isKVKind]
  obtain ⟨hp, hz, hsa⟩ := hpz
  have hna : apply.needAdminPermission rq = false := by
    have h := hp
    unfold plainCover at h
    split at h <;> simp_all [apply.isKVKind]
  ihave #Hc : iprop(kvCert γr.kv (kvEntryOn γr.kv.c0 x.chain (st, x.log) m).2) $$ [Ha]
  · iunfold kvAppliedLOn at Ha; icases Ha with ⟨-, -, #Hc, -⟩; iexact Hc
  imodintro
  iframe Ha
  isplitr
  · ipureintro; exact ⟨hp, hna, hdet, hch, hz, hsa⟩
  ihave #Hc' : iprop(kvCert γr.kv
      (kvEntryOn γr.kv.c0 (apply.alarmChain true false false) (st, x.log) m).2) $$ []
  · rw [← hch]; iexact Hc
  rw [hch]
  iapply kv_certPreVW_on E γr.kv Hcok γr.kv.c0 (st, x.log) m rq ht hd hdec hv hna hk hp γa hs hl
    hz hdet $$ Hc'

/-- **After `apply.Apply` on a KV entry, in the mode `on`** (`kvOn_after_kv` on the apply thread's
ghost state): the model's state after `m`, certified ahead (`kv_entry_pre_on`), is the apply
thread's at its new state `x'`, at the same auth state `st`. -/
theorem kv_entry_post_on (γr : ReadNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (m : EntryModel) (x x' : apply.ApplyKV) (st : auth.AuthState)
    (hc : x'.chain = x.chain) (hx : (st, x'.log) = kvEntryOn γr.kv.c0 x.chain (st, x.log) m)
    (hch : x.chain = γr.kv.ch0) :
    kvAppliedLOn (GF := GF) γr.raft γr.kv st₀ (A ++ [m])
        (kvEntryOn γr.kv.c0 x.chain (st, x.log) m) ⊢
      kvAppliedOn γr.raft γr.kv st₀ (A ++ [m]) x' st := by
  rw [← hx]
  iintro Ha
  iunfold kvAppliedOn
  iframe Ha
  ipureintro; rw [hc, hch]

end lemmas

end EtcdGrove
end Perennial
