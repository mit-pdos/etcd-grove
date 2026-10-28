/-
**The writers' log** (`examples/common/watch.go`; 2026-10-22, D33; watchkv's `Writes.lean` until
then, which cachekv's repeated). Lean-first (no Rocq counterpart).

* `okFact E p`: what the program knows of a successful Put it logged, `p` (its reply's header
  revision, key and value): the revision is at least `2` and is the put of the key and value
  (`revAt`), from the reply (`okFact_of_reply`: `putReplied`'s certificate of the log after, whose
  last revision is the put's change, `client.put_applied_log`).
* `wsInv w E`: the lock invariant of the log `w` (a `Writes`): its slice of successful Puts, each
  with `okFact`.
* `checkOk_of`: `Check`'s premise from what `Collect` returns at the store's `revAt` and the
  successful Puts' `okFact`s (watchkv's and cachekv's `Main`s' until then).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **What the program knows of a successful Put it logged** (persistent; see the file header). -/
def okFact (E : apply.AEnv GF) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.Rev'⌝ ∗ revAt E (sint.Z p.Rev').toNat p.Key' p.Val')

instance okFact_persistent (E : apply.AEnv GF) (p : wrec) : Persistent (okFact (GF := GF) E p) := by
  unfold okFact; infer_instance

/-- **A successful Put's reply gives `okFact`** of its revision, key and value. -/
theorem okFact_of_reply (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (k v : GoString)
    (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) :
    client.putReplied E γr F (client.putKeyOp k v) Q cid mid m ⊢
      okFact E ⟨m.hdr.revision, k, v⟩ := by
  iintro H
  unfold client.putReplied
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hc, -, -, -, -⟩
  obtain ⟨hstep, hrev, -, -, -, -, h2, h4⟩ := Hp
  have hlog := client.put_applied_log _ hm x x' l skip hstep
  unfold okFact revAt
  simp only
  rw [hrev]
  have hz : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
  isplitr
  · ipureintro; rw [hz]; omega
  iexists x'.log
  isplitr
  · iapply mvcc.idxCert_sealed; iexact Hc
  ipureintro
  rw [hz, hlog]
  simp [client.putKeyOp, txn.putOpOf, txn.putChangeOf, txn.putValOf, txn.putLeaseOf]

/-- **The log's lock invariant** (see the file header). -/
def wsInv (w : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Ok" w ↦ sl ∗ sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗
    □ [∗list] p ∈ oks, okFact E p)

/-- **The check's premise** (`CheckOk`), from what `collect` returns at `upTo` (`collectOk`) and
the successful Puts' facts (`okFact`), their revisions at most `upTo`: each Put's revision is a
watched event's (`collectOk`: the events reach `upTo`), whose key and value are the Put's
(`revAt_agree`). -/
theorem checkOk_of
    (E : apply.AEnv GF) (trs : List wkv) (upTo : w64) (evs : List wev) (oks : List wrec)
    (hup : ∀ p ∈ oks, sint.Z p.Rev' ≤ sint.Z upTo) :
    common.collectOk (revAt E) (trs.map pairOf) upTo evs ∗ □ ([∗list] p ∈ oks, okFact E p) ⊢
      ⌜CheckOk evs trs oks⌝ := by
  unfold common.collectOk
  iintro ⟨⟨%Hc, #Hrevs⟩, #Hoks⟩
  obtain ⟨hup0, hlen, hevs⟩ := Hc
  ihave %H : ⌜∀ p, p ∈ oks → 2 ≤ sint.Z p.Rev' ∧ ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e ∧
      e.Key' = p.Key' ∧ e.Val' = p.Val'⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %p
    by_cases hp : p ∈ oks
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
      ihave Hf := BigSepL.bigSepL_lookup (Φ := fun _ p => okFact (GF := GF) E p) hk $$ Hoks
      iunfold okFact at Hf
      icases Hf with ⟨%h2, #Hra⟩
      have hle := hup p hp
      have hlt : (sint.Z p.Rev' - 2).toNat < evs.length := by
        rcases hup0 with h0 | h0
        · rw [h0] at hle; simp at hle; omega
        · omega
      obtain ⟨e, he⟩ : ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : 2 + (sint.Z p.Rev' - 2).toNat = (sint.Z p.Rev').toNat := by omega
      ihave #He : revAt E (sint.Z p.Rev').toNat e.Key' e.Val' $$ []
      · rw [← hidx]; iapply Hrevs; ipureintro; exact he
      ihave %Hag := revAt_agree E (sint.Z p.Rev').toNat e.Key' e.Val' p.Key' p.Val' $$ [He Hra]
      · iframe #
      ipureintro; intro _; exact ⟨h2, e, he, Hag.1, Hag.2⟩
    · ipureintro; intro h; exact absurd h hp
  ipureintro
  exact ⟨hlen, hevs, H⟩

end defs

end common
end EtcdGrove
end Perennial
