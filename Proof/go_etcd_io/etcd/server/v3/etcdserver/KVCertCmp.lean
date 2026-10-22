/-
**Two members' certified logs are in prefix order** (W2 of `notes/watch-cut-plan.md`, the lifting
lemma; `notes/decisions.md` D32): a store log a member certified (`mvcc.certOk`, at its own
certificates' map) is the KV model of a committed prefix of the raft log (`kv_cert_read`); the
members share the raft names, so their committed prefixes are comparable (`srvRLogLb_prefix`), and
they agree on what the model reads (`c0`, `ch0`, `log0`), so the models of comparable prefixes are
comparable (`kvRaftOf_prefix`). A revision's changes, and so a watch's events at it, are then the
same at every member: what lets a watch resumed at another member continue one history. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section cmp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Two KV names that agree on what the model reads have the same model. -/
theorem kvModel_congr (γk γk' : KVNames) (hc0 : γk'.c0 = γk.c0) (hch : γk'.ch0 = γk.ch0)
    (hlog : γk'.log0 = γk.log0) (A : List EntryModel) : kvModel γk' A = kvModel γk A := by
  unfold kvModel; rw [hc0, hch, hlog]

/-- **Two members' certified logs are in prefix order** (see the file header): the stores `γs`
and `γs'` of two members, certified at their KV names `γk` and `γk'` (each its own certificates'
map), over the same raft names `γ`, the names agreeing on what the model reads; logs of more than
two revisions (`NewStore`'s free certificates are of at most two). -/
theorem kv_cert_cmp (γ : ServerRaftNames) (γk γk' : KVNames) (γs γs' : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (hγ' : γs'.cok = γk'.cok) (hc0 : γk'.c0 = γk.c0)
    (hch : γk'.ch0 = γk.ch0) (hlog : γk'.log0 = γk.log0) (E : CoPset) (hE : ↑kvcN ⊆ E)
    (l l' : mvcc.Log) (h2 : 2 < l.length) (h2' : 2 < l'.length) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ kvCertInv γ γk' -∗ mvcc.certOk γs l -∗ mvcc.certOk γs' l' ={E}=∗
      ⌜l <+: l' ∨ l' <+: l⌝ := by
  iintro #Hinv #Hinv' #Hc #Hc'
  imod kv_cert_read γ γk γs hγ E hE l $$ Hinv Hc with (%hl | ⟨%A, #HA, %hA⟩)
  · exfalso; omega
  imod kv_cert_read γ γk' γs' hγ' E hE l' $$ Hinv' Hc' with (%hl' | ⟨%A', #HA', %hA'⟩)
  · exfalso; omega
  ihave %Hp := srvRLogLb_prefix γ A A' $$ [$HA $HA']
  imodintro
  ipureintro
  rw [kvModel_congr γk γk' hc0 hch hlog] at hA'
  subst hA hA'
  rcases Hp with h | h
  · exact Or.inl (kvRaftOf_prefix _ _ _ _ _ h)
  · exact Or.inr (kvRaftOf_prefix _ _ _ _ _ h)

/-- **A revision is the same at two members**: the `r`th revision of two members' certified logs
(of more than two revisions), both having it, is the same change list. -/
theorem kv_cert_rev (γ : ServerRaftNames) (γk γk' : KVNames) (γs γs' : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (hγ' : γs'.cok = γk'.cok) (hc0 : γk'.c0 = γk.c0)
    (hch : γk'.ch0 = γk.ch0) (hlog : γk'.log0 = γk.log0) (E : CoPset) (hE : ↑kvcN ⊆ E)
    (l l' : mvcc.Log) (h2 : 2 < l.length) (h2' : 2 < l'.length) (r : Nat)
    (hr : r < l.length) (hr' : r < l'.length) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ kvCertInv γ γk' -∗ mvcc.certOk γs l -∗ mvcc.certOk γs' l' ={E}=∗
      ⌜l[r]? = l'[r]?⌝ := by
  iintro #Hinv #Hinv' #Hc #Hc'
  imod kv_cert_cmp γ γk γk' γs γs' hγ hγ' hc0 hch hlog E hE l l' h2 h2' $$ Hinv Hinv' Hc Hc'
    with %Hp
  imodintro
  ipureintro
  rcases Hp with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.getElem?_append_left hr]
  · rw [List.getElem?_append_left hr']

end cmp

end EtcdGrove
end Perennial
