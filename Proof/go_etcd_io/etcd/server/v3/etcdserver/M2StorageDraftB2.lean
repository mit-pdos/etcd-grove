/-
**M2, the storage side: B2, the receipt bound of a compacting cluster (Draft)** (`notes/m2-storage-plan.md`,
"The restore chain, mvcc part"; the user's decision B2 after review round 5, 2026-10-30: Q8 (b), a
configuration bound, "a stated premise at `NewServer` that a log's changes stay below the receipt
bound, covering every restored image", in place of Q8 (a)'s `restoreBoundM` from the apply side).
Imported by nothing; no `axiom`, no `sorry`; `NewServer`'s statement is trusted: the premise is a
draft for the user's approval.

**Why a premise.** The bound every seal certifies (`idxSealed`'s `logCh log < receiptBound`, and from
it the apply side's `2 ^ 48`: `txn.soleWriter_small'`) comes from the index writer's receipt per
change (`idxWriter`'s `⧗ (logCh ilog + pend.length)`, `idxWriter_lt`). `restore()` over a bucket a
compaction thinned takes one step per *surviving* entry (`restoreDone`'s `⧗ ents.length`), so a
member that installs a compacted image (the leader's log, made by the leader's writer) cannot refill
its writer's receipts, and counting from the restore gives `< 2·receiptBound` at the next seal
(review round 5's B2). A member's receipts never bound another member's log.

**The premise drafted (`srvChBound`)**: the KV model of every prefix of the cluster's log of
requested entries (the server's request log, `srvReqLogLb`, whose committed prefixes are raft's:
`srvReqLogLb_of_rlogLb`) has fewer changes than the time receipts' bound. Of `NewServer.specCompact`
only (`E₀.cmp = true`; off, every restored image is a whole bucket and the rebuild's receipts are the
writer's, as today), beside its `receiptBound GF ≤ 2 ^ 48`:

    srvChBound ρ.rd.raft ρ.rd.kv srvAuthSt0 ∗   -- in `specCompact`'s pre

**What it gives (proved below, against today's statements):**
- `Restore.specM`'s `restoreBoundM` for every image the walk installs: the image's log is the KV
  model of a committed log `A` (`srvRLogLb`), so `srvChBound_committed` bounds it
  (`restoreBoundM_of_chBound`);
- the seal bound after a compacted restore: every log the member's store reaches is the model of a
  committed prefix (the apply invariant's), so `srvChBound_committed` gives `idxSealed`'s
  `logCh log < receiptBound` without the writer's receipts, and `srvChBound_small` the apply side's
  `logCh log < 2 ^ 48` (`soleWriter_small'`'s conclusion) from `receiptBound GF ≤ 2 ^ 48`.
The mvcc side's use: in compaction mode the writer's handle is the one without receipts
(`idxWriterNR`, which `restoreDone`'s `⧗ ents.length` cannot refill), and a seal takes the bound from
the caller (`mvcc.idxWriterNR_seal`, drafted and proved below: the sealed log is today's `idxSealed`,
so `idxSealed_small` and `soleWriter_small'` read as before). Moving the handle (`idxWriter` by the
mode, `idxWriter_lt` replaced by the caller's bound in compaction mode) is the restore chain's next
step, with `store.Restore` in compaction mode (item 15).

**Its source** (open, for the user): the premise is a persistent Iris fact about the cluster's future
committed history, as the user's "configuration bound" asks. The closed theorems' hypotheses are pure
(`putgetc/Adequacy.lean`), and `putgetc`'s `Main`, the one compacting example (`specCompact`, one
member), cannot establish it from what it has: it needs either a pure form (a bound on the cluster's
committed log in terms of a workload descriptor) or a gate that excludes it where no image is ever
installed. See the plan's B2 section.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The cluster's KV history stays below the receipt bound** (draft of B2's premise, Q8 (b)): the
KV model (`kvModelOn`, from the start's auth state `st₀` and log) of every prefix of the cluster's
log of requested entries has fewer changes than the time receipts' bound. Persistent. -/
def srvChBound (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  iprop(□ ∀ L : List EntryModel, srvReqLogLb γ L -∗
    ⌜mvcc.logCh (kvModelOn γk st₀ L) < receiptBound GF⌝)

instance srvChBound_persistent (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    Persistent (srvChBound (GF := GF) γ γk st₀) := by
  unfold srvChBound; infer_instance

/-- **A committed log's model is below the bound** (glue): raft's committed log `A` has the
requested entries of a prefix of the request log (`srvReqLogLb_of_rlogLb`), whose model is `A`'s
(`kvRaftOfOn_eqv`). -/
theorem srvChBound_committed (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (E : CoPset) (hE : ↑srvRaftN ⊆ E) (A : List EntryModel) (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvChBound γ γk st₀ -∗ srvRLogLb γ A ={E}=∗
      ⌜mvcc.logCh (kvModelOn γk st₀ A) < receiptBound GF⌝ := by
  iintro #Hinv #Hb #HA
  imod srvReqLogLb_of_rlogLb γ E hE A $$ Hinv HA with ⟨%L₀, #HL, %Heqv⟩
  iunfold srvChBound at Hb
  ihave %h := Hb $$ %L₀ HL
  imodintro
  ipureintro
  have he : kvModelOn γk st₀ A = kvModelOn γk st₀ L₀ := by
    unfold kvModelOn
    rw [kvRaftOfOn_eqv γ γk.c0 γk.ch0 (st₀, γk.log0) A L₀ Heqv hc]
  rw [he]; exact h

/-- **It gives `Restore.specM`'s `restoreBoundM`** for an image that is a committed log's model
(the walk's image: the snapshot's committed entries `A`). -/
theorem restoreBoundM_of_chBound (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (E : CoPset) (hE : ↑srvRaftN ⊆ E) (A : List EntryModel) (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0)
    (d' : mvcc.KBReal) :
    ⊢ srvRaftLogInv (GF := GF) γ -∗ srvChBound γ γk st₀ -∗ srvRLogLb γ A ={E}=∗
      ⌜mvcc.restoreBoundM (GF := GF) d' (kvModelOn γk st₀ A)⌝ := by
  iintro #Hinv #Hb #HA
  imod srvChBound_committed γ γk st₀ E hE A hc $$ Hinv Hb HA with %h
  imodintro
  ipureintro
  exact fun _ => h

/-- **The seal bound and the apply side's smallness without the writer's receipts** (glue): a
prefix of the request log (every log the member's store reaches, after a compacted restore as
before it) has fewer changes than the receipts' bound, and, under `NewServer`'s
`receiptBound GF ≤ 2 ^ 48`, fewer than `2 ^ 48` (`txn.soleWriter_small'`'s conclusion). -/
theorem srvChBound_small (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (L : List EntryModel) (hrb : receiptBound GF ≤ 2 ^ 48) :
    srvChBound (GF := GF) γ γk st₀ ∗ srvReqLogLb γ L ⊢
      ⌜mvcc.logCh (kvModelOn γk st₀ L) < receiptBound GF ∧
        mvcc.logCh (kvModelOn γk st₀ L) < 2 ^ 48⌝ := by
  iintro ⟨#Hb, #HL⟩
  iunfold srvChBound at Hb
  ihave %h := Hb $$ %L HL
  ipureintro
  exact ⟨h, by omega⟩

/-! ## The mvcc side: a seal with the caller's bound (drafted)

After a compacted restore the writer's handle cannot hold a receipt per change of its log
(`restoreDone`'s `⧗ ents.length`); in compaction mode it is the handle without its receipts
(`idxWriterNR`), and a seal takes the bound from the caller (the apply thread, from
`srvChBound_committed` at the log it applies). The sealed log is today's `idxSealed`, so its
consumers (`idxSealed_small`, `txn.soleWriter_small'`, `srvApplyKV_small'`) are unchanged. -/

/-- The sealed handle without its receipts (`idxWriterSealed`'s other conjuncts). -/
def mvcc.idxWriterSealedNR (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) :
    IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (mvcc.histOf (ilog ++ [pend])) ∗
    monoNatLbOwn γ.nev (mvcc.evsOf (ilog ++ [pend])).length ∗ ⌜mvcc.IdxWf ilog pend ∧ pend ≠ []⌝ ∗
    mvcc.idxLogAuth γ (1 : Qp).half ilog)

/-- **The seal with the caller's bound** (drafted, proved): `idxWriter_seal` without the
receipts, the sealed log's `logCh < receiptBound` the caller's. -/
theorem mvcc.idxWriterNR_seal (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (hne : pend ≠ []) (hb : mvcc.logCh (ilog ++ [pend]) < receiptBound GF) :
    mvcc.idxWriterNR (GF := GF) γ ilog pend ==∗
      mvcc.idxWriterSealedNR γ ilog pend ∗ mvcc.idxSealed γ (ilog ++ [pend]) := by
  unfold mvcc.idxWriterNR mvcc.idxWriterSealedNR mvcc.idxSealed
  iintro ⟨Hauth, #Hnev, %Hwf, Hlauth⟩
  imod monoListAuthOwn_update_app [mvcc.HistItem.commit] $$ Hauth with ⟨Hauth, #Hlb⟩
  imodintro
  rw [mvcc.histShape_seal]
  iframe Hauth Hlauth Hlb Hnev
  isplitl
  · ipureintro; exact ⟨Hwf, hne⟩
  isplitl
  · ipureintro; exact Hwf.sealed
  ipureintro; exact hb

end draft

end EtcdGrove
end Perennial
