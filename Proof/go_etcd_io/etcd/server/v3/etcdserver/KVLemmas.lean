/-
**The KV ghost state's updates** (unit T1, 2026-10-14; unit T2, 2026-10-15: the whole state;
`notes/decisions.md`, "Every KV operation as a persistent atomic update on the whole state"): the
persistent updates the server hands raft are built from the KV invariant (`kvInv`,
`InvRequest.lean`), which they keep:

- `kv_prop_au`: a proposal's (`srvPropAu`), for a request with no KV write, or a client's plain
  write (a put, a delete, a transaction: firing the client's `kvOpAu` at the commit, the state
  stepped by `kvOpStep`);
- `kv_noop_au`: the standing update for raft's own entries (`srvNoopAu`);
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

/-- **A plain write's entry steps the state** by its request (`kvReqStep`), at the start's chain,
above the consistent index. -/
theorem kvModel_snoc_state (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (rq : apply.IRRModel) (hch : γk.ch0 = apply.alarmChain false false false)
    (h0 : γk.log0 ≠ []) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index) :
    kvStateOf (kvModel γk (L ++ [e])) = kvReqStep rq (kvStateOf (kvModel γk L)) := by
  have h1 : kvModel γk (L ++ [e]) = kvEntry γk.c0 γk.ch0 (kvModel γk L) e := by
    unfold kvModel; rw [kvRaftOf_snoc]
  rw [h1, hch, kvEntry_base γk.c0 _ e rq ht hd hdec hidx]
  exact kvStateOf_backendLog rq _ (kvModel_ne_nil γk L h0)

/-- A write-free entry keeps the model's state. -/
theorem kvModel_snoc_nonwrite (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
    kvModel γk (L ++ [e]) = kvModel γk L := by
  unfold kvModel; rw [kvRaftOf_snoc]
  exact kvEntry_nonwrite _ _ _ e h

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An entry with data that decode to a plain request is plain. -/
theorem plainEntry_of_data (e : EntryModel) (d : List w8) (rq : apply.IRRModel)
    (hd : e.data = d) (hdec : apply.irrDecode d = some rq) (hp : plainReq rq) : plainEntry e := by
  intro _ _ rq' h
  rw [hd, hdec] at h
  cases h
  exact hp

/-- The next entry of a consecutive log is above every index the log reached. -/
theorem srvIdxOk_last (ai0 : w64) (L : List EntryModel) (e : EntryModel)
    (h : srvIdxOk ai0 (L ++ [e])) : uint.Z e.index = uint.Z ai0 + 1 + L.length := by
  have := (h.2 L.length e (by simp)).1
  exact this

/-- The KV invariant's pure facts, one entry on (`hpl`: the entry plain). -/
theorem kvInv_facts_snoc (γ : ServerRaftNames) (γk : KVNames) (L : List EntryModel)
    (e : EntryModel)
    (hok : plainLog L ∧ srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 + L.length ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [])
    (hidx' : srvIdxOkW γ.ai0 (L ++ [e])) (hpl : plainEntry e) :
    plainLog (L ++ [e]) ∧ srvIdxOkW γ.ai0 (L ++ [e]) ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 + (L ++ [e]).length ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [] := by
  obtain ⟨hplog, -, hc0, hch, h0⟩ := hok
  refine ⟨?_, hidx', ?_, hch, h0⟩
  · rw [plainLog_append]
    refine ⟨hplog, fun m hm => ?_⟩
    rw [List.mem_singleton] at hm
    subst hm
    exact hpl
  · simp only [List.length_append, List.length_singleton]; push_cast; omega

/-- **The workload facts, one entry on** (D19c): the entry of a good shape, its id claimed. -/
theorem kvWork_snoc (cfg : GSet w64) (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (hs : entryShape e) (hc : e.typ ≠ W32 0 → ccBootOk cfg e.data) :
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

/-- An entry of raft's own (an empty entry, a conf change of id `0`) has a good shape and nothing
to claim (D19c). -/
theorem noop_shape (cfg : GSet w64) (e : EntryModel) (h : srvNoopEntry cfg e) : entryShape e := by
  rcases h with ⟨ht, hd⟩ | ⟨ht, -, hid, -⟩
  · exact ⟨fun _ => Or.inl hd, fun h' => absurd ht h'⟩
  · refine ⟨fun h' => ?_, fun _ => hid⟩
    rw [ht] at h'; exact absurd h' (by decide)

/-- A conf change of raft's own is one `applyConfChange` takes (audit phase B3). -/
theorem noop_cc (cfg : GSet w64) (e : EntryModel) (h : srvNoopEntry cfg e) :
    e.typ ≠ W32 0 → ccBootOk cfg e.data := by
  intro ht
  rcases h with ⟨ht0, -⟩ | ⟨-, -, -, hb⟩
  · exact absurd ht0 ht
  · exact hb

theorem noop_claim (γi : IdNames) (cfg : GSet w64) (e : EntryModel) (h : srvNoopEntry cfg e) :
    ⊢ entryClaim (GF := GF) γi e := by
  iunfold entryClaim
  ileft
  ipureintro
  rcases h with ⟨-, hd⟩ | ⟨ht, -, -, -⟩
  · exact Or.inr hd
  · left; rw [ht]; decide

/-- **The KV invariant and the client's `etcdKV`, allocated** (2026-10-15, unit T2): from the
server's half of raft's committed log at the start (empty), a start log not empty and a start
consistent index at most the start index, the KV invariant at the base chain with auth disabled
and the client's half of the state at the start log's state. -/
theorem kvInv_alloc (γ : ServerRaftNames) (c0 : w64) (log0 : mvcc.Log) (cok hi : GName)
    (ids : IdNames) (E : CoPset) (hc0 : uint.Z c0 ≤ uint.Z γ.ai0) (h0 : log0 ≠ []) :
    ⊢ srvRLog (GF := GF) γ [] ={E}=∗ ∃ st : GName,
      kvInv γ ⟨st, c0, apply.alarmChain false false false, log0, cok, hi, ids⟩ ∗
      etcdKV ⟨st, c0, apply.alarmChain false false false, log0, cok, hi, ids⟩ (kvStateOf log0) := by
  iintro HL
  imod ghostVar_alloc (GF := GF) (kvStateOf log0) with ⟨%st, Hv⟩
  have hs : ⊢ ghostVar (GF := GF) st 1 (kvStateOf log0) -∗
      ghostVar st (1 : Qp).half (kvStateOf log0) ∗ ghostVar st (1 : Qp).half (kvStateOf log0) := by
    have := ghostVar_split (GF := GF) st (kvStateOf log0) (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at this
    exact this
  icases hs $$ Hv with ⟨Hv1, Hv2⟩
  imod inv_alloc kvN E (iprop(∃ L : List EntryModel,
      srvRLog γ L ∗ ghostVar st (1 : Qp).half
        (kvStateOf (kvModel ⟨st, c0, apply.alarmChain false false false, log0, cok, hi, ids⟩ L)) ∗
      ⌜plainLog L ∧ srvIdxOkW γ.ai0 L ∧ uint.Z c0 ≤ uint.Z γ.ai0 + L.length ∧
        apply.alarmChain false false false = apply.alarmChain false false false ∧ log0 ≠ []⌝ ∗
      kvWork γ.raft.reCfg ⟨st, c0, apply.alarmChain false false false, log0, cok, hi, ids⟩ L))
    $$ [HL Hv1] with #Hinv
  · inext
    iexists []
    iframe HL
    isplitl [Hv1]
    · simp only [kvModel, kvRaftOf_nil]; iexact Hv1
    isplitr
    · ipureintro
      refine ⟨fun m hm => by simp at hm, srvIdxOkW_nil _, by simpa using hc0, rfl, h0⟩
    iunfold kvWork
    isplitr
    · ipureintro; exact ⟨fun m hm => by simp at hm, fun m hm => by simp at hm⟩
    iapply BigSepL.bigSepL_nil.2
    itrivial
  imodintro
  iexists st
  isplitl []
  · iunfold kvInv; iexact Hinv
  iunfold etcdKV; iexact Hv2

/-- **A proposal's update, from the KV invariant** (see the file header): since D19c
(2026-10-18) for data claimed under the request's id (`idClaim`), which the invariant keeps with
the request's shape (`reqPropOk`'s `rqShape`). -/
theorem kv_prop_au (γ : ServerRaftNames) (γk : KVNames) (d : List w8) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (hd : d ≠ []) (hdec : apply.irrDecode d = some rq)
    (id : w64) (γf : GName) (hid : apply.irrId rq = some id)
    (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInv (GF := GF) γ γk -∗ idClaim γk.ids id d γf -∗ reqPropOk γk rq Qr ={E}=∗
      srvPropAu γ d Qr := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hcl Hok
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
    iframe Hcl
    ipureintro; exact ⟨hdec, hid⟩
  iunfold reqPropOk at Hok
  icases Hok with (%Hno | ⟨%op, %Q, %Hop, #Hau⟩)
  · -- no KV write
    obtain ⟨hplain, hnw, -, hshape, hQr⟩ := Hno
    subst hQr
    imodintro
    unfold srvPropAu
    iintro !>
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
      have hent : kvModel γk (L ++ [e]) = kvModel γk L := by
        apply kvModel_snoc_nonwrite
        right; right
        intro rq' h
        rw [hed, hdec] at h
        cases h
        exact hnw
      ihave #Hw' := kvWork_snoc γ.raft.reCfg γk L e (hsh e het hed hshape)
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
    unfold srvPropAu
    iintro !>
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
      have hst : kvStateOf (kvModel γk (L ++ [e])) = kvOpStep op σ := by
        rw [kvModel_snoc_state γk L e rq Hok.2.2.2.1 Hok.2.2.2.2 het hdata
          (by rw [hed]; exact hdec) hidxe, Hag]
        unfold kvReqStep; rw [hop]
      ihave #Hw' := kvWork_snoc γ.raft.reCfg γk L e (hsh e het hed hshape)
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
      rw [Hag]
      iexact HQ

/-- **The standing update for raft's own entries, from the KV invariant.** -/
theorem kv_noop_au (γ : ServerRaftNames) (γk : KVNames) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvNoopAu γ := by
  have Hdisj := kvN_raftN
  iintro #Hinv
  unfold srvNoopAu
  iintro !>
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
    obtain ⟨He, hidx⟩ := He
    have h10 : W32 1 ≠ W32 0 := by decide
    have hidx' : srvIdxOkW γ.ai0 (L ++ [e]) := by
      refine srvIdxOkW_snoc γ.ai0 L e Hok.2.1 hidx ?_
      rcases He with h | h
      · left; exact h.1
      · right; exact ⟨h.1, h.2.1⟩
    have hent : kvModel γk (L ++ [e]) = kvModel γk L := by
      apply kvModel_snoc_nonwrite
      rcases He with h | h
      · left; exact h.2
      · right; left; rw [h.1]; exact h10
    ihave #Hnc := noop_claim (GF := GF) γk.ids γ.raft.reCfg e He
    ihave #Hw' := kvWork_snoc γ.raft.reCfg γk L e (noop_shape γ.raft.reCfg e He)
      (noop_cc γ.raft.reCfg e He) $$ Hw Hnc
    imod Hclose $$ [HL Hσ] with -
    · inext
      iexists L ++ [e]
      rw [hent]
      iframe HL Hσ Hw'
      ipureintro
      refine kvInv_facts_snoc γ γk L e Hok hidx' ?_
      intro ht hd'
      rcases He with h | h
      · exact absurd h.2 hd'
      · exact absurd ht (by rw [h.1]; exact h10)
    imodintro
    itrivial

/-! ## Reads: one update for many clients -/

/-- Firing every registered read update at the state of `L`'s model, the KV authority's half
agreeing. -/
theorem kv_fire_reads (γk : KVNames) (L : List EntryModel) :
    ∀ gs : List GName,
      ⊢ ghostVar (GF := GF) γk.st (1 : Qp).half (kvStateOf (kvModel γk L)) -∗
        ([∗list] g ∈ gs, regOk γk g) -∗
        |={(⊤ \ ↑srvRaftN) \ ↑kvN}=> ghostVar γk.st (1 : Qp).half (kvStateOf (kvModel γk L)) ∗
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
    · imod kv_fire_reads γk L gs $$ Hσ Hgs' with ⟨Hσ, #Hrest⟩
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
    imod kv_fire_reads γk L gs $$ Hσ Hgs' with ⟨Hσ, #Hrest⟩
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
      rw [Hag]
      iexact HQ0
    · iexact Hrest

/-- **One read update for the registered clients `gs`, from the KV invariant** (see the file
header): at every firing, every client's read update is fired in turn at the current state. -/
theorem kv_read_compose (γ : ServerRaftNames) (γk : KVNames) (gs : List GName) :
    ⊢ kvInv (GF := GF) γ γk -∗ ([∗list] g ∈ gs, regOk γk g) -∗
      srvReadAu γ (readQs gs) := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hgs
  unfold srvReadAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod kv_fire_reads γk L gs $$ Hσ Hgs with ⟨Hσ, #HQs⟩
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

/-- Whether a request that is no write is plain depends only on its kind. -/
theorem plainReq_of_kind (rq rq' : apply.IRRModel) (hk : apply.dispatchKind rq' = apply.dispatchKind rq)
    (hnw : ¬ writeKind (apply.dispatchKind rq)) (hp : plainReq rq) : plainReq rq' := by
  unfold writeKind at hnw
  unfold plainReq at hp ⊢
  rw [hk]
  revert hp hnw
  cases apply.dispatchKind rq <;> simp

/-- **A proposal's permission carries to the request the wire decodes.** -/
theorem reqPropOk_wire (γk : KVNames) (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) (hw : irrWireOf (apply.withHeader rq hm) rq') :
    reqPropOk γk rq Qr ⊢ reqPropOk γk rq' Qr := by
  obtain ⟨-, -, hk, hrq⟩ := hw
  rw [dispatchKind_withHeader] at hk
  unfold reqPropOk
  iintro (%Hno | ⟨%op, %Q, %Hop, #Hau⟩)
  · ileft
    obtain ⟨hp, hnw, hnz, hs, hQ⟩ := Hno
    have he := hrq hnz
    subst he
    ipureintro
    exact ⟨hp, hnw, hnz, hs, hQ⟩
  · iright
    obtain ⟨hp, hop, hnz, hs, hQ⟩ := Hop
    have he := hrq hnz
    subst he
    iexists op, Q
    iframe Hau
    ipureintro
    exact ⟨hp, hop, hnz, hs, hQ⟩

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
