/-
**A linearizable read's result** (unit T1, 2026-10-14; `notes/decisions.md`, "Put and Get as
persistent atomic updates linearized by raft"): a read served by the read loop (`readServed`: its
client registered in a round whose read index `ci` the applied index reached, and raft's witness of
the round's update) reads, from mvcc, a certified log extending the log applied through an index at
least `ci` (`readServed_logR`); that log is the KV model of a committed raft log through an index at
least `ci` (`kv_read_log`), at which raft's witness gives the client's result (`readWit_fire`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a served read knows of the log it will read** (persistent): the round's read index
`ci`, a log `L₀` applied through an index at least `ci` that `logR` extends, raft's witness of the
round's update at `ci`, the client's place in the round and its result predicate. -/
def readWitAt (γr : ReadNames) (Q : List EntryModel → IProp GF) (g : GName) (logR : mvcc.Log) :
    IProp GF :=
  iprop(∃ (ci ci₀ : w64) (L₀ : mvcc.Log) (gs : List GName) (k : Nat),
    ⌜uint.Z ci ≤ uint.Z ci₀ ∧ gs[k]? = some g ∧ L₀ <+: logR⌝ ∗ appliedLogAt γr ci₀ L₀ ∗
    srvReadWit γr.raft (readQs gs) ci ∗ savedPredOwn g DFrac.discard Q)

instance readWitAt_persistent (γr : ReadNames) (Q : List EntryModel → IProp GF) (g : GName)
    (logR : mvcc.Log) : Persistent (readWitAt (GF := GF) γr Q g logR) := by
  unfold readWitAt; infer_instance

theorem readWitAt_mono (γr : ReadNames) (Q : List EntryModel → IProp GF) (g : GName)
    (logR l : mvcc.Log) (h : logR <+: l) :
    readWitAt (GF := GF) γr Q g logR ⊢ readWitAt γr Q g l := by
  unfold readWitAt
  iintro ⟨%ci, %ci₀, %L₀, %gs, %k, %Hp, #HL, #HW, #HQ⟩
  iexists ci, ci₀, L₀, gs, k
  iframe HL HW HQ
  ipureintro; exact ⟨Hp.1, Hp.2.1, Hp.2.2.trans h⟩

variable [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A served read's lower bound** (as `readIndexOk_logR`, at the round's read index): a certified
log `logR` extending the reader's `log₀`, read after the read index (`readLogOk γr c logR`), and
what the read will know of it (`readWitAt`). -/
theorem readServed_logR (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (g : GName)
    (Q : List EntryModel → IProp GF) (log₀ : mvcc.Log) :
    ⊢ srvAppliedInv s E γr -∗ readServed γr c g -∗ savedPredOwn g DFrac.discard Q -∗
      mvcc.idxCert E.γ.idx log₀ ={⊤}=∗
      ∃ logR : mvcc.Log, mvcc.idxCert E.γ.idx logR ∗ ⌜log₀ <+: logR⌝ ∗ readLogOk γr c logR ∗
        readWitAt γr Q g logR := by
  iintro #Hinv #Hsv #HQ #Hc0
  iunfold readServed at Hsv
  icases Hsv with ⟨%ci, %ai, %gs, %k, %Hp, #Hai, #HW⟩
  ihave #Hri : readIndexOk γr ci $$ []
  · iunfold readIndexOk; iexists ai; iframe Hai; ipureintro; exact Hp.2.1
  imod readIndexOk_logR s E γr ci log₀ $$ Hinv Hri Hc0 with ⟨%logR, #HcR, %HpR, #HrlR⟩
  imodintro
  iexists logR
  iframe HcR
  isplitr
  · ipureintro; exact HpR
  iunfold readLogOk at HrlR
  icases HrlR with ⟨#Hri', %ci₀, %L₀, %Hc, #HL, %HpL⟩
  isplitr
  · iunfold readLogOk
    isplitr
    · iunfold readIndexOk at Hri'
      icases Hri' with ⟨%c1, %Hc1, #Hl1⟩
      iunfold readIndexOk
      iexists c1; iframe Hl1; ipureintro; omega
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨by omega, HpL⟩
  iunfold readWitAt
  iexists ci, ci₀, L₀, gs, k
  iframe HL HW HQ
  ipureintro; exact ⟨Hc, Hp.2.2, HpL⟩

/-- **A served read's result at the log it read** (`l`, certified, extending the lower bound):
`l` is the KV model of a committed raft log `L` through an index at least the round's read
index, and raft's witness gives the client's `□ Q L` (three credits: two for raft's witness,
one for the saved predicate's agreement). -/
theorem readWit_fire (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Q : List EntryModel → IProp GF)
    (g : GName) (l : mvcc.Log) :
    ⊢ srvAppliedInv s E γr -∗ srvKVInvs E γr -∗ readWitAt γr Q g l -∗ mvcc.certOk E.γ l -∗ £ 3
      ={⊤}=∗ ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = l⌝ ∗ □ Q L := by
  iintro #Hainv #Hkvi #Hw #Hc Hlc
  iunfold srvKVInvs at Hkvi
  icases Hkvi with ⟨-, #HcI, -, %Hcok⟩
  iunfold readWitAt at Hw
  icases Hw with ⟨%ci, %ci₀, %L₀, %gs, %k, %Hp, #HL, #HW, #HQ⟩
  imod appliedLogAt_kvLogAt s E γr ci₀ L₀ $$ Hainv HL with #HkL
  imod kv_read_log γr E.γ Hcok ⊤ (fun _ _ => CoPset.mem_full) ci₀ L₀ l Hp.2.2 $$ HcI HkL Hc
    with ⟨%A, #HA, %HAp⟩
  iunfold srvReadWit at HW
  icases (lc_split (n := 2) (m := 1)).1 $$ Hlc with ⟨Hlc2, Hlc1⟩
  imod HW $$ %A HA %(by omega) Hlc2 with #HQs
  ihave HQL := readQs_get gs A k g Q Hp.2.1 $$ HQs HQ
  imod lc_fupd_elim_later $$ Hlc1 HQL with #HQL
  imodintro
  iexists A
  iframe HA HQL
  ipureintro; exact HAp.1

end lemmas

end EtcdGrove
end Perennial
