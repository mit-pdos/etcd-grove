/-
**The KV ghost state's updates** (unit T1, 2026-10-14; unit T2, 2026-10-15: the whole state;
`notes/decisions.md`, "Every KV operation as a persistent atomic update on the whole state"): the
persistent updates the server hands raft are built from the KV invariant (`kvInv`,
`InvRequest.lean`), which they keep:

- `kv_prop_au`: a proposal's (`srvPropAu1`), for a request with no KV write, or a client's plain
  write (a put, a delete, a transaction: firing the client's `kvOpAu` at the commit, the state
  stepped by `kvOpStep`);
- `kv_qinv`: the server's result predicates, of the KV model of the log, are ones the server's
  two logs agree on (`srvQInv`; 2026-10-27, `kvModel_eqv`); (`kv_noop_au`, raft's own entries'
  standing update, is gone with raft's node API: its fillers commit without the client);
- `kv_read_compose`: one read update (`srvReadAu`) for a list of clients' read updates
  (`kvReadAu`), fired in turn at every firing (`readQs`: their results), and `readQs_get`, a
  client's own result out of the list.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Spec.google_golang_org.protobuf.proto.MarshalIRR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

/-! ## Pure facts of the model at the server's start -/

/-- The model of a committed log is not empty (the start log is not). -/
theorem kvModel_ne_nil (γk : KVNames) (L : List EntryModel) (h : γk.log0 ≠ []) :
    kvModel γk L ≠ [] := by
  intro he
  apply h
  have hp := kvRaftOf_extends γk.c0 γk.ch0 γk.log0 L
  unfold kvModel at he
  rw [he] at hp
  exact List.prefix_nil.1 hp

/-- **A request's entry steps the state** by its request (`kvReqStep`), at the start's chain,
above the consistent index (unit T3, L3a: any request, the table too). -/
theorem kvModel_snoc_state (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (rq : apply.IRRModel) (hch : γk.ch0 = apply.alarmChain false false false)
    (h0 : γk.log0 ≠ []) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index) :
    kvModelSt γk (L ++ [e]) = kvReqStep rq (kvModelSt γk L) := by
  have h1 : kvModel γk (L ++ [e]) = kvEntry γk.c0 γk.ch0 (kvLeases γk L) (kvModel γk L) e := by
    unfold kvModel kvLeases; rw [kvRaftOf_snoc]
  have h2 : kvLeases γk (L ++ [e]) = kvTable γk.c0 γk.ch0 (kvLeases γk L) e := by
    unfold kvLeases; rw [kvTableOf_snoc]
  unfold kvModelSt
  rw [h1, h2, hch, kvEntry_base γk.c0 _ _ e rq ht hd hdec hidx,
    kvTable_base γk.c0 _ e rq ht hd hdec hidx]
  exact kvStateOf_backendLog _ rq _ (kvModel_ne_nil γk L h0)

/-- **A plain committed log's state has no lease** (unit T3, L3a). -/
theorem kvModelSt_plain (γk : KVNames) (L : List EntryModel) (h : plainLog L) :
    kvModelSt γk L = kvStateOf (kvModel γk L) := by
  unfold kvModelSt kvLeases; rw [kvTableOf_plain _ _ L h]

/-- A write-free entry keeps the model's log. -/
theorem kvModel_snoc_nonwrite (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
    kvModel γk (L ++ [e]) = kvModel γk L := by
  unfold kvModel; rw [kvRaftOf_snoc]
  exact kvEntry_nonwrite _ _ _ _ e h

/-- A write-free entry keeps the model's lease table (unit T3, L3a). -/
theorem kvLeases_snoc_nonwrite (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
    kvLeases γk (L ++ [e]) = kvLeases γk L := by
  unfold kvLeases; rw [kvTableOf_snoc]
  exact kvTable_nonwrite _ _ _ e h

/-- A write-free entry keeps the model's state (unit T3, L3a). -/
theorem kvModelSt_snoc_nonwrite (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
    kvModelSt γk (L ++ [e]) = kvModelSt γk L := by
  unfold kvModelSt; rw [kvModel_snoc_nonwrite γk L e h, kvLeases_snoc_nonwrite γk L e h]

/-! ## The model reads only the requested entries (2026-10-27) -/

section opsModel
variable [GooseExts]

/-- **A requested entry's effect** on the model's state, above the consistent index. -/
def kvOpSt (ch : apply.Chain) (s : mvcc.Log × LeaseTable) (x : LogEntry) :
    mvcc.Log × LeaseTable :=
  kvEntrySt (W64 0) ch s ⟨x.term, W64 1, x.type, x.data⟩

theorem kvEntrySt_above (c₀ : w64) (ch : apply.Chain) (s : mvcc.Log × LeaseTable)
    (m : EntryModel) (h : uint.Z c₀ < uint.Z m.index) :
    kvEntrySt c₀ ch s m = kvOpSt ch s m.toLE := by
  have h1 : decide (uint.Z c₀ < uint.Z m.index) = true := decide_eq_true h
  have h2 : decide (uint.Z (W64 0) < uint.Z (W64 1)) = true := by decide
  unfold kvOpSt kvEntrySt kvEntry kvTable EntryModel.toLE
  simp only [h1, h2]

theorem kvEntrySt_filler (c₀ : w64) (ch : apply.Chain) (s : mvcc.Log × LeaseTable)
    (m : EntryModel) (h : m.toLE.isFiller) : kvEntrySt c₀ ch s m = s := by
  obtain ⟨hd, ht⟩ := h
  simp only [EntryModel.toLE] at hd ht
  unfold kvEntrySt kvEntry kvTable
  simp [ht, hd]

theorem kvRaftSt_ops (c₀ : w64) (ch : apply.Chain) :
    ∀ (A : List EntryModel) (s : mvcc.Log × LeaseTable),
      (∀ m ∈ A, uint.Z c₀ < uint.Z m.index) →
      kvRaftSt c₀ ch s A = (opsOf (A.map EntryModel.toLE)).foldl (kvOpSt ch) s
  | [], _, _ => rfl
  | m :: A, s, h => by
    have hA : ∀ m' ∈ A, uint.Z c₀ < uint.Z m'.index := fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    unfold kvRaftSt
    rw [List.foldl_cons]
    by_cases hf : m.toLE.isFiller
    · rw [kvEntrySt_filler c₀ ch s m hf]
      have : opsOf ((m :: A).map EntryModel.toLE) = opsOf (A.map EntryModel.toLE) := by
        simp [opsOf, hf]
      rw [this]
      exact kvRaftSt_ops c₀ ch A s hA
    · rw [kvEntrySt_above c₀ ch s m (h m (List.mem_cons_self ..))]
      have : opsOf ((m :: A).map EntryModel.toLE) =
          m.toLE :: opsOf (A.map EntryModel.toLE) := by
        simp [opsOf, hf]
      rw [this, List.foldl_cons]
      exact kvRaftSt_ops c₀ ch A _ hA

/-- Every entry of a log consecutive after `ai₀` is above a consistent index at most `ai₀`. -/
theorem srvIdxOkW_above (ai₀ c₀ : w64) (A : List EntryModel) (h : srvIdxOkW ai₀ A)
    (hc : uint.Z c₀ ≤ uint.Z ai₀) : ∀ m ∈ A, uint.Z c₀ < uint.Z m.index := by
  intro m hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  have := (h n m hn).1
  omega

/-- **The KV model of two logs with the same requested entries** is the same (2026-10-27): the
server's two logs (`srvEqv`), its start's consistent index at most the start index. -/
theorem kvModel_eqv (γ : ServerRaftNames) (γk : KVNames) (A B : List EntryModel)
    (h : srvEqv γ A B) (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) :
    kvModel γk A = kvModel γk B ∧ kvLeases γk A = kvLeases γk B := by
  obtain ⟨hA, hB, hops⟩ := h
  have eA := kvRaftSt_ops γk.c0 γk.ch0 A (γk.log0, []) (srvIdxOkW_above _ _ A hA hc)
  have eB := kvRaftSt_ops γk.c0 γk.ch0 B (γk.log0, []) (srvIdxOkW_above _ _ B hB hc)
  have hst : kvRaftSt γk.c0 γk.ch0 (γk.log0, []) A = kvRaftSt γk.c0 γk.ch0 (γk.log0, []) B := by
    rw [eA, eB, hops]
  refine ⟨by unfold kvModel kvRaftOf; rw [hst], ?_⟩
  unfold kvLeases
  have a := kvRaftSt_snd γk.c0 γk.ch0 A (γk.log0, [])
  have b := kvRaftSt_snd γk.c0 γk.ch0 B (γk.log0, [])
  simp only at a b
  rw [← a, ← b, hst]

end opsModel

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- An entry with data that decode to a plain request is plain. -/
theorem plainEntry_of_data (e : EntryModel) (d : List w8) (rq : apply.IRRModel)
    (hd : e.data = d) (hdec : apply.irrDecode d = some rq) (hp : plainReq rq) :
    plainEntry e := by
  intro _ _ rq' h
  rw [hd, hdec] at h
  cases h
  exact hp

/-- The KV invariant's pure facts, one entry on (`hpl`: the entry plain). -/
theorem kvInv_facts_snoc (γ : ServerRaftNames) (γk : KVNames) (L : List EntryModel)
    (e : EntryModel)
    (hok : plainLog L ∧ srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [])
    (hidx' : srvIdxOkW γ.ai0 (L ++ [e])) (hpl : plainEntry e) :
    plainLog (L ++ [e]) ∧ srvIdxOkW γ.ai0 (L ++ [e]) ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [] := by
  obtain ⟨hplog, -, hc0, hch, h0⟩ := hok
  refine ⟨?_, hidx', hc0, hch, h0⟩
  rw [plainLog_append]
  refine ⟨hplog, fun m hm => ?_⟩
  rw [List.mem_singleton] at hm
  subst hm
  exact hpl

/-- **The workload facts, one entry on** (D19c): the entry of a good shape, its id claimed. -/
theorem kvWork_snoc (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (hs : entryShape e) (hc : e.typ ≠ W32 0 → ccPolOk cfg e.data) :
    ⊢ kvWork (GF := GF) cfg γk L -∗ entryClaim γk.ids e -∗ kvWork cfg γk (L ++ [e]) := by
  iintro Hw #He
  iunfold kvWork at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  iunfold kvWork
  isplitr
  · ipureintro
    rw [logShape_append]
    refine ⟨⟨Hsh.1, fun m hm => ?_⟩, fun m hm => ?_⟩
    · rw [List.mem_singleton] at hm; subst hm; exact hs
    · rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Hsh.2 m hm
      · subst hm; exact hc
  iapply BigSepL.bigSepL_snoc.2
  iframe Hcl He

/-- **A proposal's update, from the KV invariant** (see the file header): since D19c
(2026-10-18) for data claimed under the request's id (`idClaim`), which the invariant keeps with
the request's shape (`reqPropOk`'s `rqShape`). -/
theorem kv_prop_au (γ : ServerRaftNames) (γk : KVNames) (d : List w8) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (hd : d ≠ []) (hdec : apply.irrDecode d = some rq)
    (id : w64) (γf : GName) (hid : apply.irrId rq = some id)
    (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInv (GF := GF) γ γk -∗ idClaim γk.ids id d γf -∗ idRegd γk.ids id -∗ reqPropOk γk rq Qr ={E}=∗
      srvPropAu1 γ d Qr := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hcl #Hreg Hok
  -- the entry's workload facts, whichever case
  have hsh : ∀ e : EntryModel, e.typ = W32 0 → e.data = d → rqShape rq → entryShape e := by
    intro e het hed hs
    refine ⟨fun _ => Or.inr ⟨rq, by rw [hed]; exact hdec, ⟨id, hid⟩, hs⟩, fun h => absurd het h⟩
  ihave #Hecl : iprop(∀ e : EntryModel, ⌜e.data = d⌝ -∗ entryClaim γk.ids e) $$ []
  · iintro %e %hed
    iunfold entryClaim
    iright
    iexists rq, id, γf
    rw [hed]
    iframe Hcl Hreg
    ipureintro; exact ⟨hdec, hid⟩
  iunfold reqPropOk at Hok
  icases Hok with (%Hno | ⟨%op, %Q, %Hop, #Hau⟩ | ⟨%op, %Q, %γc, %Hop, Hau⟩)
  · -- no KV write
    obtain ⟨hplain, hnw, -, hshape, hQr⟩ := Hno
    subst hQr
    imodintro
    unfold srvPropAu1
    iauintro
    unfold atomic_acc
    iunfold kvInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
    iintro Hmask
    iexists L
    iframe HL
    isplit
    · iintro HL
      imod Hmask with -
      imod Hclose $$ [HL Hσ] with -
      · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
      imodintro
      itrivial
    · iintro %e ⟨%He, HL⟩
      imod Hmask with -
      obtain ⟨het, hed, hidx⟩ := He
      have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.1 hidx (Or.inl het)
      have hent : kvModelSt γk (L ++ [e]) = kvModelSt γk L := by
        apply kvModelSt_snoc_nonwrite
        right; right
        intro rq' h
        rw [hed, hdec] at h
        cases h
        exact hnw
      ihave #Hw' := kvWork_snoc γ.raft γk L e (hsh e het hed hshape)
        (fun h => absurd het h) $$ Hw (Hecl $$ %e %hed)
      imod Hclose $$ [HL Hσ] with -
      · inext
        iexists L ++ [e]
        rw [hent]
        iframe HL Hσ Hw'
        ipureintro
        exact kvInv_facts_snoc γ γk L e Hok hidx' (plainEntry_of_data _ d rq hed hdec hplain)
      imodintro
      iintro !>
      itrivial
  · -- a plain write, with its client's update
    obtain ⟨hplain, hop, -, hshape, hQr⟩ := Hop
    subst hQr
    iunfold kvOpAu at Hau
    iunfold kvAu at Hau
    imodintro
    unfold srvPropAu1
    iauintro
    unfold atomic_acc
    iunfold kvInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hc, Hucl⟩
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ Hc
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    imodintro
    iexists L
    iframe HL
    isplit
    · iintro HL
      icases Hucl with ⟨Habort, -⟩
      imod Habort $$ [Hc] with -
      · iunfold etcdKV; iexact Hc
      imod Hclose $$ [HL Hσ] with -
      · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
      imodintro
      itrivial
    · iintro %e ⟨%He, HL⟩
      icases Hucl with ⟨-, Hcommit⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
      obtain ⟨het, hed, hidx⟩ := He
      have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.1 hidx (Or.inl het)
      imod ghostVar_update_halves (kvOpStep op σ) γk.st _ _ $$ Hσ Hc with ⟨Hσ, Hc⟩
      imod Hcommit $$ [Hc] with #HQ
      · iunfold etcdKV; iexact Hc
      have hdata : e.data ≠ [] := by rw [hed]; exact hd
      have hidxe : uint.Z γk.c0 < uint.Z e.index := by
        have := Hok.2.2.1
        omega
      have hst : kvModelSt γk (L ++ [e]) = kvOpStep op σ := by
        rw [kvModel_snoc_state γk L e rq Hok.2.2.2.1 Hok.2.2.2.2 het hdata
          (by rw [hed]; exact hdec) hidxe, Hag]
        unfold kvReqStep; rw [hop]
      ihave #Hw' := kvWork_snoc γ.raft γk L e (hsh e het hed hshape)
        (fun h => absurd het h) $$ Hw (Hecl $$ %e %hed)
      imod Hclose $$ [HL Hσ] with -
      · inext
        iexists L ++ [e]
        rw [hst]
        iframe HL Hσ Hw'
        ipureintro
        exact kvInv_facts_snoc γ γk L e Hok hidx' (plainEntry_of_data _ d rq hed hdec hplain)
      imodintro
      iintro !>
      rw [← kvModelSt_plain γk L Hok.1, Hag]
      iexact HQ
  · -- (D21 M6) a plain write, with its client's update fired at most once, the result left at
    -- its token
    obtain ⟨hplain, hop, -, hshape, hQr⟩ := Hop
    subst hQr
    iunfold kvOpAu1 at Hau
    iunfold kvAu1 at Hau
    imodintro
    unfold srvPropAu1
    iauintro
    unfold atomic_acc
    iunfold kvInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hc, Hucl⟩
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ Hc
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    imodintro
    iexists L
    iframe HL
    isplit
    · iintro HL
      icases Hucl with ⟨Habort, -⟩
      imod Habort $$ [Hc] with Hau
      · iunfold etcdKV; iexact Hc
      imod Hclose $$ [HL Hσ] with -
      · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
      imodintro
      iexact Hau
    · iintro %e ⟨%He, HL⟩
      icases Hucl with ⟨-, Hcommit⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
      obtain ⟨het, hed, hidx⟩ := He
      have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.1 hidx (Or.inl het)
      imod ghostVar_update_halves (kvOpStep op σ) γk.st _ _ $$ Hσ Hc with ⟨Hσ, Hc⟩
      imod Hcommit $$ [Hc] with HQ
      · iunfold etcdKV; iexact Hc
      imod kvRes_alloc γc Q σ _ $$ HQ with #HQ
      have hdata : e.data ≠ [] := by rw [hed]; exact hd
      have hidxe : uint.Z γk.c0 < uint.Z e.index := by
        have := Hok.2.2.1
        omega
      have hst : kvModelSt γk (L ++ [e]) = kvOpStep op σ := by
        rw [kvModel_snoc_state γk L e rq Hok.2.2.2.1 Hok.2.2.2.2 het hdata
          (by rw [hed]; exact hdec) hidxe, Hag]
        unfold kvReqStep; rw [hop]
      ihave #Hw' := kvWork_snoc γ.raft γk L e (hsh e het hed hshape)
        (fun h => absurd het h) $$ Hw (Hecl $$ %e %hed)
      imod Hclose $$ [HL Hσ] with -
      · inext
        iexists L ++ [e]
        rw [hst]
        iframe HL Hσ Hw'
        ipureintro
        exact kvInv_facts_snoc γ γk L e Hok hidx' (plainEntry_of_data _ d rq hed hdec hplain)
      imodintro
      iintro !>
      rw [← kvModelSt_plain γk L Hok.1, Hag]
      iexact HQ


/-- **A result predicate of the KV model of the log is one the server's two logs agree on**
(2026-10-27): the KV invariant keeps the start's consistent index at most the start index
(`kvModel_eqv`). -/
theorem kv_qinv (γ : ServerRaftNames) (γk : KVNames) (Q : mvcc.Log → IProp GF) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvQInv γ (fun L => Q (kvModel γk L)) := by
  iintro #Hinv
  iunfold srvQInv
  iintro !> %A %B %Hab #HA
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  inext
  rw [← (kvModel_eqv γ γk A B Hab Hok.2.2.1).1]
  iexact HA

/-- The result predicates `reqPropOk` admits are of the KV model of the log. -/
theorem reqPropOk_shape (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    reqPropOk (GF := GF) γk rq Qr ⊢ ⌜∃ Q : mvcc.Log → IProp GF, Qr = fun L => Q (kvModel γk L)⌝ := by
  iintro Hok
  iunfold reqPropOk at Hok
  icases Hok with (%Hno | ⟨%op, %Q, %Hop, -⟩ | ⟨%op, %Q, %γc, %Hop, -⟩)
  · ipureintro; exact ⟨fun _ => iprop(True), Hno.2.2.2.2⟩
  · ipureintro; exact ⟨fun l => iprop(□ Q (kvStateOf l)), Hop.2.2.2.2⟩
  · ipureintro; exact ⟨fun l => kvRes γc Q (kvStateOf l), Hop.2.2.2.2⟩

theorem reqPropOk_qinv (γ : ServerRaftNames) (γk : KVNames) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) :
    reqPropOk (GF := GF) γk rq Qr ⊢ reqPropOk γk rq Qr ∗ (kvInv γ γk -∗ srvQInv γ Qr) := by
  refine (persistent_entails_left (reqPropOk_shape γk rq Qr)).trans ?_
  iintro ⟨Hok, %Hq⟩
  obtain ⟨Q, rfl⟩ := Hq
  iframe Hok
  iintro #Hinv
  iapply kv_qinv γ γk Q $$ Hinv

/-! ## Reads: one update for many clients -/

/-- Firing every registered read update at the state of `L`'s model, the KV authority's half
agreeing. -/
theorem kv_fire_reads (γk : KVNames) (L : List EntryModel) (hpl : plainLog L) :
    ∀ gs : List GName,
      ⊢ ghostVar (GF := GF) γk.st (1 : Qp).half (kvModelSt γk L) -∗
        ([∗list] g ∈ gs, regOk γk g) -∗
        |={(⊤ \ ↑srvRaftN) \ ↑kvN}=> ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
          readQs gs L
  | [] => by
    iintro Hσ -
    imodintro
    iframe Hσ
    unfold readQs
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | g :: gs => by
    iintro Hσ #Hgs
    icases (BigSepL.bigSepL_cons (Φ := fun _ g => regOk (GF := GF) γk g)).1 $$ Hgs with
      ⟨#Hg, #Hgs'⟩
    iunfold regOk at Hg
    icases Hg with ⟨%Q, #HQ, #Hd⟩
    iunfold kvDep at Hd
    icases Hd with (⟨%Q0, %HQeq, #Hau⟩ | %HQeq)
    rotate_left
    · imod kv_fire_reads γk L hpl gs $$ Hσ Hgs' with ⟨Hσ, #Hrest⟩
      imodintro
      iframe Hσ
      unfold readQs
      iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
        savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L))).2
      isplitl []
      · iexists Q
        iframe HQ
        rw [HQeq]
        iintro !>; itrivial
      · iexact Hrest
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hc, Hucl⟩
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ Hc
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    imod Hcommit $$ [Hc] with #HQ0
    · iunfold etcdKV; iexact Hc
    imod kv_fire_reads γk L hpl gs $$ Hσ Hgs' with ⟨Hσ, #Hrest⟩
    imodintro
    iframe Hσ
    unfold readQs
    iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
      savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L))).2
    isplitl []
    · iexists Q
      iframe HQ
      rw [HQeq]
      iintro !> !>
      rw [kvStOff, ← kvModelSt_plain γk L hpl, Hag]
      iexact HQ0
    · iexact Hrest

/-- The clients' results at two logs of the same KV state (2026-10-27; the deposits' state
function `F`, the auth plan's E3r). -/
theorem readQs_eqv (γk : KVNames) (F : List EntryModel → KVState) (A B : List EntryModel)
    (h : F A = F B) :
    ∀ gs : List GName,
      ⊢ ([∗list] g ∈ gs, regOk (GF := GF) γk g F) -∗ readQs gs A -∗ ▷ readQs gs B
  | [] => by
    iintro - -
    inext
    unfold readQs
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | g :: gs => by
    iintro #Hgs #HA
    icases (BigSepL.bigSepL_cons (Φ := fun _ g => regOk (GF := GF) γk g F)).1 $$ Hgs with
      ⟨#Hg, #Hgs'⟩
    iunfold readQs at HA
    icases (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
      savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q A))).1 $$ HA with ⟨⟨%Q, #HQ, #HQA⟩, #HA'⟩
    ihave #HA'' : readQs gs A $$ []
    · iunfold readQs; iexact HA'
    ihave Hrest := readQs_eqv γk F A B h gs $$ Hgs' HA''
    iunfold regOk at Hg
    icases Hg with ⟨%Q', #HQ', #Hd⟩
    ihave #Hag := saved_pred_agree g DFrac.discard DFrac.discard Q Q' A $$ HQ HQ'
    ihave %HQ'AB : ⌜Q' A = Q' B⌝ $$ [Hd]
    · iunfold kvDep at Hd
      icases Hd with (⟨%Q0, %HQeq, -⟩ | %HQeq)
      · ipureintro; rw [HQeq]; simp only [h]
      · ipureintro; rw [HQeq]
    inext
    unfold readQs
    iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
      savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q B))).2
    iframe Hrest
    iexists Q'
    iframe HQ'
    ihave #Hiff := internalEq_iff _ _ $$ Hag
    icases Hiff with ⟨Hto, -⟩
    iintro !>
    rw [← HQ'AB]
    iapply Hto $$ HQA

/-- The clients' results are ones the server's two logs agree on (2026-10-27). -/
theorem readQs_qinv (γ : ServerRaftNames) (γk : KVNames) (gs : List GName) :
    ⊢ kvInv (GF := GF) γ γk -∗ ([∗list] g ∈ gs, regOk γk g) -∗ srvQInv γ (readQs gs) := by
  iintro #Hinv #Hgs
  iunfold srvQInv
  iintro !> %A %B %Hab #HA
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  ihave HB := readQs_eqv γk (kvStOff γk) A B
    (by simp only [kvStOff, (kvModel_eqv γ γk A B Hab Hok.2.2.1).1]) gs $$ Hgs HA
  imodintro
  inext
  iintro !>
  iexact HB

/-- **One read update for the registered clients `gs`, from the KV invariant** (see the file
header): at every firing, every client's read update is fired in turn at the current state. -/
theorem kv_read_compose (γ : ServerRaftNames) (γk : KVNames) (gs : List GName) :
    ⊢ kvInv (GF := GF) γ γk -∗ ([∗list] g ∈ gs, regOk γk g) -∗
      srvReadAu γ (readQs gs) := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hgs
  unfold srvReadAu
  isplitr
  rotate_left
  · iapply readQs_qinv γ γk gs $$ Hinv Hgs
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod kv_fire_reads γk L Hok.1 gs $$ Hσ Hgs with ⟨Hσ, #HQs⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    iintro !>
    iexact HQs

/-- **A client's own result out of the list** (`n`-th registered, its result predicate `Q` at
`g`): a later for the saved predicate's agreement. -/
theorem readQs_get (gs : List GName) (L : List EntryModel) (n : Nat) (g : GName)
    (Q : List EntryModel → IProp GF) (hg : gs[n]? = some g) :
    ⊢ readQs gs L -∗ savedPredOwn g DFrac.discard Q -∗ ▷ □ Q L := by
  iintro #HQs #HQ
  iunfold readQs at HQs
  ihave Hn := (BigSepL.bigSepL_lookup (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
    savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L)) hg) $$ HQs
  icases Hn with ⟨%Q', #HQ', #HQL⟩
  ihave #Hag := saved_pred_agree g DFrac.discard DFrac.discard Q' Q L $$ HQ' HQ
  inext
  ihave #Hiff := internalEq_iff _ _ $$ Hag
  iintro !>
  icases Hiff with ⟨Hto, -⟩
  iapply Hto $$ HQL


/-! ## A proposal's permission through the wire -/

/-- `dispatchKind` ignores the header. -/
theorem dispatchKind_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    apply.dispatchKind (apply.withHeader rq hm) = apply.dispatchKind rq := rfl

/-- **A proposal's permission carries to the request the wire decodes.** -/
theorem reqPropOk_wire (γk : KVNames) (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) (hw : irrWireOf (apply.withHeader rq hm) rq') :
    reqPropOk γk rq Qr ⊢ reqPropOk γk rq' Qr := by
  obtain ⟨-, -, hk, hrq⟩ := hw
  rw [dispatchKind_withHeader] at hk
  unfold reqPropOk
  iintro (%Hno | ⟨%op, %Q, %Hop, #Hau⟩ | ⟨%op, %Q, %γc, %Hop, Hau⟩)
  · ileft
    obtain ⟨hp, hnw, hnz, hs, hQ⟩ := Hno
    have he := hrq hnz
    subst he
    ipureintro
    exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hnw, hnz, hs, hQ⟩
  · iright; ileft
    obtain ⟨hp, hop, hnz, hs, hQ⟩ := Hop
    have he := hrq hnz
    subst he
    iexists op, Q
    iframe Hau
    ipureintro
    exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hop, hnz, hs, hQ⟩
  · iright; iright
    obtain ⟨hp, hop, hnz, hs, hQ⟩ := Hop
    have he := hrq hnz
    subst he
    iexists op, Q, γc
    iframe Hau
    ipureintro
    exact ⟨⟨hp.1, putgetKind_header _ _ hp.2⟩, hop, hnz, hs, hQ⟩

/-! ### The KV logs' certificates (2026-10-14, unit T1) -/

theorem w64_len_inj (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h' := congrArg (fun w : w64 => uint.Z w) h
  have e1 : uint.Z (W64 (a : Int)) = a := by word
  have e2 : uint.Z (W64 (b : Int)) = b := by word
  omega

/-- **The apply thread certifies the log after an entry** (`kv_cert_step`): from its state at the
raft log `A` and the KV log `l`, the entry `m` committed after `A`, the model `l'` of `A ++ [m]`
(`l` itself, or `l` and one revision) is certified, at a length above every certified one. -/
theorem kv_cert_step (γ : ServerRaftNames) (γk : KVNames) (E : CoPset) (hE : ↑kvcN ⊆ E)
    (A : List EntryModel) (m : EntryModel) (l l' : mvcc.Log)
    (hl' : l' = kvModel γk (A ++ [m])) (hg : l' = l ∨ ∃ cs, l' = l ++ [cs])
    (hlen : l'.length < 2 ^ 63) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ kvAppliedL γ γk A l -∗ srvRLogLb γ (A ++ [m]) ={E}=∗
      kvAppliedL γ γk (A ++ [m]) l' := by
  iintro #Hinv Ha #Hlb
  iunfold kvAppliedL at Ha
  icases Ha with ⟨#HA, Hhi, #Hc, %Hl⟩
  rcases hg with rfl | ⟨cs, rfl⟩
  · imodintro
    iunfold kvAppliedL
    iframe Hlb Hhi Hc
    ipureintro; exact hl'
  · iunfold kvCertInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hhe := ghostVar_agree γk.hi _ _ _ _ $$ Hhi Hhi'
    have hfresh : C.lookup (W64 ((l ++ [cs]).length : Int)) = none := by
      cases h : C.lookup (W64 ((l ++ [cs]).length : Int)) with
      | none => rfl
      | some l'' =>
        obtain ⟨h1, h2, h3, -⟩ := Hok.1 _ _ h
        have := w64_len_inj _ _ hlen h3 h2
        simp only [List.length_append, List.length_singleton] at this
        omega
    imod ghost_map_insert_persist _ (l ++ [cs]) hfresh $$ HC with ⟨HC, #He⟩
    imod ghostVar_update_halves (l ++ [cs]).length γk.hi _ _ $$ Hhi Hhi' with ⟨Hhi, Hhi'⟩
    ihave %Hcmp := srvRLogLb_prefix γ (A ++ [m]) Lb $$ [Hlb HLb]
    · iframe Hlb HLb
    have hold : ∀ n l2, C.lookup n = some l2 → l2.length ≤ (l ++ [cs]).length := by
      intro n l2 hn
      have := (Hok.1 n l2 hn).1
      simp only [List.length_append, List.length_singleton]
      omega
    imod Hclose $$ [HC Hhi'] with -
    · inext
      rcases Hcmp with h | h
      · iexists C.insert (W64 ((l ++ [cs]).length : Int)) (l ++ [cs]), (l ++ [cs]).length, Lb
        iframe HC Hhi' HLb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A ++ [m], h, hl'.symm⟩
        · obtain ⟨-, h2, h3, A', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A', h4, h5⟩
      · iexists C.insert (W64 ((l ++ [cs]).length : Int)) (l ++ [cs]), (l ++ [cs]).length, A ++ [m]
        iframe HC Hhi' Hlb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A ++ [m], List.prefix_refl _, hl'.symm⟩
        · obtain ⟨-, h2, h3, A', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A', h4.trans h, h5⟩
    imodintro
    iunfold kvAppliedL
    iframe Hlb Hhi
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; exact hl'

/-- **A store log's certificate, read at the server** (`kv_cert_read`): the log has at most two
revisions, or it is the KV model of a committed raft log (the store's free certificate `0 ↦ []`
is not the server's: the start log is not empty). -/
theorem kv_cert_read (γ : ServerRaftNames) (γk : KVNames) (γs : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (E : CoPset) (hE : ↑kvcN ⊆ E) (l : mvcc.Log) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ mvcc.certOk γs l ={E}=∗
      ⌜l.length ≤ 2⌝ ∨ ∃ A, srvRLogLb γ A ∗ ⌜kvModel γk A = l⌝ := by
  unfold mvcc.certOk
  rw [hγ]
  iintro #Hinv (%h | #He | #He)
  · imodintro; ileft; ipureintro; exact h
  · iunfold kvCertInv at Hinv
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
  · iunfold kvCertInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hm := ghost_map_lookup $$ HC He
    obtain ⟨-, -, -, A, -, hm⟩ := Hok.1 _ _ Hm
    have h0 := kvRaftOf_extends γk.c0 γk.ch0 γk.log0 A
    unfold kvModel at hm
    rw [hm] at h0
    have := h0.length_le
    simp only [List.length_nil] at this
    omega

/-- **What a linearizable read reads** (2026-10-14, unit T1): a certified log `l` extending the
log `L₀` applied through `i` (at least two revisions) is the KV model of a committed raft log
through an index at least `i`. -/
theorem kv_read_log (γr : ReadNames) (γs : mvcc.StoreNames) (hγ : γs.cok = γr.kv.cok)
    (E : CoPset) (hE : ↑kvcN ⊆ E) (i : w64) (L₀ l : mvcc.Log) (hp : L₀ <+: l) :
    ⊢ kvCertInv (GF := GF) γr.raft γr.kv -∗ kvLogAt γr i L₀ -∗ mvcc.certOk γs l ={E}=∗
      ∃ A, srvRLogLb γr.raft A ∗
        ⌜kvModel γr.kv A = l ∧ uint.Z i ≤ uint.Z γr.raft.ai0 + A.length⌝ := by
  iintro #Hinv #Hat #Hc
  iunfold kvLogAt at Hat
  icases Hat with ⟨%AR, #HAR, %HR⟩
  ihave #Hinv' := Hinv
  iunfold kvCertInv at Hinv'
  iinv Hinv' with >Hi Hclose
  icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
  imod Hclose $$ [HC Hhi'] with -
  · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
  have h0 := Hok.2
  have h2 : 2 ≤ L₀.length := by
    have := (kvRaftOf_extends γr.kv.c0 γr.kv.ch0 γr.kv.log0 AR).length_le
    rw [HR.2]; unfold kvModel; omega
  imod kv_cert_read γr.raft γr.kv γs hγ E hE l $$ Hinv Hc with (%hl | ⟨%A', #HA', %hA'⟩)
  · have heq : L₀ = l := hp.eq_of_length (by have := hp.length_le; omega)
    imodintro
    iexists AR
    iframe HAR
    ipureintro; exact ⟨by rw [← heq]; exact HR.2.symm, by omega⟩
  · ihave %Hcmp := srvRLogLb_prefix γr.raft AR A' $$ [HAR HA']
    · iframe HAR HA'
    imodintro
    rcases Hcmp with h | h
    · iexists A'
      iframe HA'
      ipureintro
      exact ⟨hA', by have := h.length_le; omega⟩
    · have hk := kvRaftOf_prefix γr.kv.c0 γr.kv.ch0 γr.kv.log0 A' AR h
      have hk' : l <+: L₀ := by
        unfold kvModel at hA' HR
        rw [hA', ← HR.2] at hk; exact hk
      have heq : L₀ = l := hp.eq_of_length (Nat.le_antisymm hp.length_le hk'.length_le)
      iexists AR
      iframe HAR
      ipureintro; exact ⟨by rw [← heq]; exact HR.2.symm, by omega⟩

end lemmas

end EtcdGrove
end Perennial
