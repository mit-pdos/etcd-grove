/-
`executeRange`'s bridge from mvcc's range read (`rangeOutcome`: the index's answers and the
bucket's key-values) to the server's model (`RangeModel.lean`: `srvPre`, `srvCount`), unit 2.
Lean-first.

* `rangeKvs_kvsAt`: the key-values mvcc's read fills (`rangeKvs`, one per answer, each the
  state's key-value of the answer's key) are the owned key-values of the selection, as read
  (`kvRead`: a fast keys-only read's have no value and lease);
* `taken_stateAt`, `total_stateAt`: the answers taken and the count, against the state at the
  revision read (`Lemmas.lean`'s `rangeAnswers_stateAt` at a word revision);
* `srvPre_small`: the sort's premise from a small state (`stateAt_small`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode mvcc

/-! ## Pure -/

/-- The answers a read takes are the state's key-values in the range, up to the limit (at a
non-negative word revision). -/
theorem taken_stateAt (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (atRev limit : w64) (h0 : 0 ≤ sint.Z atRev) :
    List.Forall₂ (AnsKv log (stateAt log (sint.nat atRev))) (rangeTaken log endNil k e atRev limit)
      (takeLimit (limitOf limit) (srvSel (stateAt log (sint.nat atRev)) endNil k e)) := by
  rw [rangeTaken_eq]
  exact forall2_takeLimit _ (rangeAnswers_stateAt_w log hok endNil k e atRev h0)

/-- The count a read returns, against the state at the revision read. -/
theorem total_stateAt (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (atRev limit : w64) (wt : Bool) (h0 : 0 ≤ sint.Z atRev) :
    rangeTotal log endNil k e atRev limit wt =
      totalOf (limitOf limit) wt (srvSel (stateAt log (sint.nat atRev)) endNil k e).length := by
  have hr : sint.nat atRev < 2 ^ 63 := by
    unfold sint.nat sint.Z at *; have := BitVec.toInt_lt (x := atRev); simp at this; omega
  have h := rangeTotal_stateAt log hok endNil k e (sint.nat atRev) hr limit wt
  rwa [W64_sint_nat atRev h0] at h

/-- The number of answers, against the state at the revision read. -/
theorem answers_length_stateAt (log : Log) (hok : LogOk log) (endNil : Bool) (k e : GoString)
    (atRev : w64) (h0 : 0 ≤ sint.Z atRev) :
    (rangeAnswers log endNil k e atRev).length =
      (srvSel (stateAt log (sint.nat atRev)) endNil k e).length :=
  forall2_length (rangeAnswers_stateAt_w log hok endNil k e atRev h0)

theorem kvOk_kvRead (f : Bool) (v : EtcdKv) (h : kvOk v) : kvOk (kvRead f v) := by
  unfold kvRead; cases f <;> exact h

/-- **The sort's premise** from a small state: the key-values sorted are at most `2 ^ 62`, with
non-negative revisions and versions. -/
theorem srvPre_small (o : OpFull) (st : List EtcdKv)
    (h : st.length ≤ 2 ^ 62 ∧ ∀ v ∈ st, kvOk v) :
    (srvPre o st).length ≤ 2 ^ 62 ∧ ∀ v ∈ srvPre o st, kvOk v := by
  unfold srvPre
  split
  · simp
  · have hin : (rangeIn st o).length ≤ st.length := List.length_filter_le _ _
    have htk : ∀ (lim : Option Nat) (l : List EtcdKv), (takeLimit lim l).length ≤ l.length := by
      intro lim l; cases lim <;> simp [takeLimit]; omega
    have hmem : ∀ (lim : Option Nat) (l : List EtcdKv) (x : EtcdKv), x ∈ takeLimit lim l → x ∈ l := by
      intro lim l x hx; cases lim with
      | none => exact hx
      | some n => exact List.mem_of_mem_take hx
    refine ⟨?_, ?_⟩
    · have := List.length_filter_le (kvFilterOk o)
        ((takeLimit (limitOf (rangeLimitOf o)) (rangeIn st o)).map (kvRead (fastKeysOnly o)))
      have := htk (limitOf (rangeLimitOf o)) (rangeIn st o)
      simp only [List.length_map] at *
      omega
    · intro v hv
      obtain ⟨hv, _⟩ := List.mem_filter.1 hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      exact kvOk_kvRead _ _ (h.2 w (List.mem_filter.1 (hmem _ _ _ hw)).1)

/-! ## The key-values read -/

section iris
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **mvcc's key-values are the selection's**: one per answer, each the state's key-value of the
answer's key, are the owned key-values of the selection (`sel`, one for one with the answers),
as read. -/
theorem rangeKvs_kvsAt (full : Bool) (st : List EtcdKv) :
    ∀ (ps : List Loc) (answers : List (GoString × Rev × Rev × w64)) (sel : List EtcdKv),
    List.Forall₂ (fun a v => findKey a.1 st = some v) answers sel → ps.length = answers.length →
    ([∗list] pa ∈ ps.zip answers, ∃ kv : EtcdKv, ⌜findKey pa.2.1 st = some kv⌝ ∗
        mvcc.kvPtrIs (GF := GF) full pa.1 kv) ⊢
      |==> kvsAt (ps.zip (sel.map (kvRead (!full))))
  | [], _, _, _, _ => by
    iintro -
    imodintro
    simp only [List.zip_nil_left]
    iapply kvsAt_nil
  | _ :: _, [], _, _, hlen => by simp at hlen
  | p :: ps, a :: answers, sel, h, hlen => by
    cases h with
    | cons hv hrest =>
      rename_i v sel'
      simp only [List.zip_cons_cons, List.map_cons]
      refine (BigSepL.bigSepL_cons (PROP := IProp GF)).1.trans ?_
      iintro ⟨⟨%kv, %hkv, Hp⟩, Hrest⟩
      have hkv' : kv = v := by rw [hv] at hkv; exact (Option.some.inj hkv).symm
      subst hkv'
      imod rangeKvs_kvsAt full st ps answers sel' hrest (by simpa using hlen) $$ Hrest with Hrest
      iapply (kvsAt_cons (GF := GF) (p, kvRead (!full) kv) _).2
      iframe Hrest
      cases full with
      | true => simp only [Bool.not_true, kvRead, Bool.false_eq_true, ↓reduceIte]; imodintro; iexact Hp
      | false =>
        simp only [Bool.not_false]
        iapply kvPtrIs_false
        iexact Hp

theorem zip_map_fst {α β : Type} :
    ∀ (ps : List α) (xs : List β), ps.length = xs.length → (ps.zip xs).map Prod.fst = ps
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | p :: ps, _ :: xs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact zip_map_fst ps xs (by simpa using h)

theorem zip_map_snd {α β : Type} :
    ∀ (ps : List α) (xs : List β), ps.length = xs.length → (ps.zip xs).map Prod.snd = xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, x :: xs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact zip_map_snd ps xs (by simpa using h)

section txn_read
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A read transaction's log is well formed (its certificate), not empty, and its revision is
the log's last. -/
theorem isTxnRead_pure (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) :
    mvcc.isTxnRead (GF := GF) mw s γ log rev ⊢
      mvcc.isTxnRead mw s γ log rev ∗ ⌜LogOk log ∧ log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ := by
  iintro H
  iunfold mvcc.isTxnRead at H
  iNamed H
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  ihave #HcT := HcertT
  iunfold mvcc.idxCert at HcT
  icases HcT with ⟨-, -, %Hp, -⟩
  isplitl
  · iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti, rt, ranges
    iframe
    iframe #
  · ipureintro
    exact ⟨LogOk.of_cert Hp HneT, HneT, HrevT⟩

/-- A read transaction's certificate. -/
theorem isTxnRead_cert (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) :
    mvcc.isTxnRead (GF := GF) mw s γ log rev ⊢ mvcc.isTxnRead mw s γ log rev ∗ mvcc.idxCert γ.idx log := by
  iintro H
  iunfold mvcc.isTxnRead at H
  iNamed H
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  isplitl
  · iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti, rt, ranges
    iframe
    iframe #
  · iexact HcertT

end txn_read

end iris

/-! ## In the client's terms (`Results.lean`) -/

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open go_etcd_io.etcd.server.v3.storage.mvcc in
/-- **`rangeResult` in the client model's terms**: a success's key-values are `rangeKvsOk` of
the client's selection `rangeSel` of the state read, up to the lease of a fast keys-only read
(`leaseZ`), and `More` is the client's below the largest limit; the other outcomes as in
`rangeResult`. -/
def rangeResultClient (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (o : OpFull)
    (withTotal : Bool) : IProp GF :=
  iprop(
    (⌜sint.Z rev < sint.Z o.base.rev ∧ resp = null⌝ ∗
      ∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∨
    (⌜sint.Z o.base.rev ≤ sint.Z rev ∧ o.base.countOnly = false ∧ fastKeysOnly o = false ∧
      resp = null ∧ err ≠ GoInterface.nil⌝) ∨
    (⌜sint.Z o.base.rev ≤ sint.Z rev ∧ err = GoInterface.nil⌝ ∗
      ∃ (kvs : List EtcdKv) (more : Bool) (kvs' : List EtcdKv),
      rangeResponseIs resp rev kvs more
        (srvCount o (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev o.base.rev))) withTotal) ∗
      ⌜rangeKvsOk o (rangeSel (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev o.base.rev))) o) kvs' ∧
        kvs = kvs'.map (leaseZ (fastKeysOnly o)) ∧
        (o.base.countOnly = false → sint.Z o.base.limit < 2 ^ 63 - 1 →
          more = decide (0 < sint.Z o.base.limit ∧ sint.Z o.base.limit <
            ((rangeSel (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev o.base.rev))) o).length : Int)))⌝))

/-- A range request's `sortSet` is the client's (`rangeOpOf`). -/
theorem rangeRequestIs_sortSet (r : Loc) (o : OpFull) :
    rangeRequestIs (GF := GF) r o ⊢
      ⌜o.base.sortSet = decide (o.sortOrder ≠ W64 0 ∨ o.sortTarget ≠ W64 0)⌝ := by
  iintro Hr
  iunfold rangeRequestIs at Hr
  icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM,
    %maxM, %minC, %maxC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %Ho⟩
  ipureintro
  subst Ho
  simp only [rangeOpOf, ne_eq, sext32_eq order 0 (by omega) (by omega),
    sext32_eq target 0 (by omega) (by omega)]

/-- **The server's range in the client's terms**, unless the sort is cut early. -/
theorem rangeResult_client (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64)
    (o : OpFull) (withTotal : Bool)
    (hset : o.base.sortSet = decide (o.sortOrder ≠ W64 0 ∨ o.sortTarget ≠ W64 0))
    (hcut : ¬ cutEarly o) :
    rangeResult (GF := GF) resp err log rev o withTotal ⊢
      rangeResultClient resp err log rev o withTotal := by
  unfold rangeResult rangeResultClient
  iintro (H | H | ⟨%H, %kvs, %more, Hresp, %Hok⟩)
  · ileft; iexact H
  · iright; ileft; iexact H
  · iright; iright
    obtain ⟨kvs', h1, h2, h3⟩ := srvRangeOk_rangeKvsOk o _ kvs more hset Hok hcut
    isplitr
    · ipureintro; exact H
    iexists kvs, more, kvs'
    iframe Hresp
    ipureintro
    exact ⟨h1, h2, h3⟩

end client

end txn
end EtcdGrove
end Perennial
