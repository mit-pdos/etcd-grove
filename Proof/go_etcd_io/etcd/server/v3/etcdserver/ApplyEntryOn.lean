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

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The certificates a KV entry's latest-state outcomes need, in the mode `on`** (see the file
header): for a plain KV request of the entry `m` above `c₀`, at the start chain with auth on and
no alarm, determinate at the model's state `s` (whose auth part is the latest state of `hs`),
without `"\x00"` range ends and with `txnVerdictOwn`, every outcome the verdict at the latest
state admits leaves the model's log after `m`, which `kvCert` certifies. -/
theorem kv_certPreW_on (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (s : auth.AuthState × mvcc.Log) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (htx : txnVerdictOwn (.on γa) hs rq) (hdet : entryDetOn c₀ s m) :
    kvCert (GF := GF) γk (kvEntryOn c₀ (apply.alarmChain true false false) s m).2 ⊢
      apply.certPreW E (apply.alarmChain true false false) rq s.2
        (apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2) := by
  iintro #Hc
  iunfold apply.certPreW
  iintro !> %oc %h
  have ho := outcomeOn_of_kvOutL c₀ s m rq ht hd hdec hv hna hk hp γa hs hl hz htx oc h.2
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
    (hz : noZeroEnds rq) (htx : txnVerdictOwn (.on γa) hs rq) (hdet : entryDetOn c₀ s m) :
    kvCert (GF := GF) γk (kvEntryOn c₀ (apply.alarmChain true false false) s m).2 ⊢
      apply.certPreVW true E (apply.alarmChain true false false) rq s.2
        (apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2) := by
  simp only [apply.certPreVW, ↓reduceIte]
  exact kv_certPreW_on E γk hγ c₀ s m rq ht hd hdec hv hna hk hp γa hs hl hz htx hdet

end lemmas

end EtcdGrove
end Perennial
