/-
**The KV ghost state's updates** (unit T1, 2026-10-14; `notes/decisions.md`, "Put and Get as
persistent atomic updates linearized by raft"): the persistent updates the server hands raft are
built from the KV invariant (`kvInv`, `InvRequest.lean`), which they keep:

- `kv_prop_au`: a proposal's (`srvPropAu`), for a request with no KV effect, a client's plain put
  (firing the client's `kvPutAu` at the commit), or none at all (the non-plain credit, which no
  one has: `kv_nonplain_false`);
- `kv_noop_au`: the standing update for raft's own entries (`srvNoopAu`);
- `kv_read_compose`: one read update (`srvReadAu`) for a list of clients' `Get` updates
  (`kvGetAu`), fired in turn at every firing (`readQs`: their results), and `readQs_get`, a
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

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **No one holds the non-plain credit**: its only token is in the KV invariant. -/
theorem kv_nonplain_false (γ : ServerRaftNames) (γk : KVNames) (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvNonPlain γk ={E}=∗ False := by
  iintro #Hinv Hnp
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, %M, -, -, Htok, -⟩
  iunfold srvNonPlain at Hnp
  iexfalso
  iapply token_exclusive γk.np $$ Htok Hnp

/-- A plain put's request keeps no ignore flag. -/
theorem plainReq_put (rq : apply.IRRModel) (op : OpFull) (hp : plainReq rq)
    (hk : apply.dispatchKind rq = .put) (hop : rq.put = some op) :
    op.leaseID = W64 0 ∧ op.ignoreValue = false ∧ op.ignoreLease = false := by
  unfold plainReq at hp
  rw [hk] at hp
  obtain ⟨-, -, h⟩ := hp
  obtain ⟨h1, h2⟩ := h op hop
  unfold txn.needsPrev at h2
  simp only [Bool.or_eq_false_iff] at h2
  exact ⟨h1, h2⟩

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

/-- **A proposal's update, from the KV invariant** (see the file header). -/
theorem kv_prop_au (γ : ServerRaftNames) (γk : KVNames) (d : List w8) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (hd : d ≠ []) (hdec : apply.irrDecode d = some rq)
    (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInv (GF := GF) γ γk -∗ reqPropOk γk rq Qr ={E}=∗ srvPropAu γ d Qr := by
  have Hdisj := kvN_raftN
  iintro #Hinv Hok
  iunfold reqPropOk at Hok
  icases Hok with (%Hno | ⟨%op, %Q, %Hput, #Hau⟩ | Hnp)
  · -- no KV effect
    obtain ⟨hplain, hk1, hk2, hQr⟩ := Hno
    subst hQr
    imodintro
    unfold srvPropAu
    iintro !>
    iauintro
    unfold atomic_acc
    iunfold kvInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, %M, HL, HM, Htok, %Hok⟩
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
    iintro Hmask
    iexists L
    iframe HL
    isplit
    · iintro HL
      imod Hmask with -
      imod Hclose $$ [HL HM Htok] with -
      · inext; iexists L, M; iframe HL HM Htok; ipureintro; exact Hok
      imodintro
      itrivial
    · iintro %e ⟨%He, HL⟩
      imod Hmask with -
      obtain ⟨hplog, hidx, hc0, hch, hM⟩ := Hok
      obtain ⟨het, hed, hidx'⟩ := He
      have hent : kvEntry γk.c0 γk.ch0 (kvModel γk L) e = kvModel γk L := by
        apply kvEntry_nonwrite
        right; right
        intro rq' h
        rw [hed, hdec] at h
        cases h
        exact ⟨hk1, hk2⟩
      imod Hclose $$ [HL HM Htok] with -
      · inext
        iexists L ++ [e], M
        iframe HL HM Htok
        ipureintro
        refine ⟨?_, hidx', ?_, hch, ?_⟩
        · rw [plainLog_append]
          refine ⟨hplog, fun m hm => ?_⟩
          rw [List.mem_singleton] at hm
          subst hm
          exact plainEntry_of_data _ d rq hed hdec hplain
        · simp only [List.length_append, List.length_singleton]; push_cast; omega
        · intro k vo hk
          unfold kvModel
          rw [kvRaftOf_snoc]
          unfold kvModel at hent
          rw [hent]
          exact hM k vo hk
      imodintro
      iintro !>
      itrivial
  · -- a plain put, with its client's update
    obtain ⟨hplain, hk, hop, -, -, hQr⟩ := Hput
    subst hQr
    obtain ⟨hlease, hiv, hil⟩ := plainReq_put rq op hplain hk hop
    iunfold kvPutAu at Hau
    imodintro
    unfold srvPropAu
    iintro !>
    iauintro
    unfold atomic_acc
    iunfold kvInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, %M, HL, HM, Htok, %Hok⟩
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%vo, Hpt, Hucl⟩
    iunfold kvPt at Hpt
    ihave %Hlk := ghost_map_lookup $$ HM Hpt
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    imodintro
    iexists L
    iframe HL
    isplit
    · iintro HL
      icases Hucl with ⟨Habort, -⟩
      imod Habort $$ [Hpt] with -
      · iunfold kvPt; iexact Hpt
      imod Hclose $$ [HL HM Htok] with -
      · inext; iexists L, M; iframe HL HM Htok; ipureintro; exact Hok
      imodintro
      itrivial
    · iintro %e ⟨%He, HL⟩
      icases Hucl with ⟨-, Hcommit⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
      obtain ⟨hplog, hidx, hc0, hch, hM⟩ := Hok
      obtain ⟨het, hed, hidx'⟩ := He
      imod ghost_map_update (some op.val) $$ HM Hpt with ⟨HM, Hpt⟩
      imod Hcommit $$ [Hpt] with #HQ
      · iunfold kvPt; iexact Hpt
      have hdata : e.data ≠ [] := by rw [hed]; exact hd
      have hidxe : uint.Z γk.c0 < uint.Z e.index := by
        have := srvIdxOk_last γ.ai0 L e hidx'
        omega
      have hent : kvEntry γk.c0 γk.ch0 (kvModel γk L) e =
          kvModel γk L ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter (kvModel γk L)))]] := by
        rw [hch]
        exact kvEntry_put γk.c0 _ e rq op het hdata (by rw [hed]; exact hdec) hk hop hidxe
      have hvo : vo = kvVal (kvModel γk L) op.key := hM op.key vo Hlk
      imod Hclose $$ [HL HM Htok] with -
      · inext
        iexists L ++ [e], M.insert op.key (some op.val)
        iframe HL HM Htok
        ipureintro
        refine ⟨?_, hidx', ?_, hch, ?_⟩
        · rw [plainLog_append]
          refine ⟨hplog, fun m hm => ?_⟩
          rw [List.mem_singleton] at hm
          subst hm
          exact plainEntry_of_data _ d rq hed hdec hplain
        · simp only [List.length_append, List.length_singleton]; push_cast; omega
        · intro k vo' hk'
          unfold kvModel
          rw [kvRaftOf_snoc]
          unfold kvModel at hent
          rw [hent]
          rw [GMap.lookup_insert_Some] at hk'
          rcases hk' with ⟨rfl, rfl⟩ | ⟨hne, hk'⟩
          · rw [kvVal_put _ op _ hiv]
          · rw [kvVal_put_other _ op _ k hne]
            exact hM k vo' hk'
      imodintro
      iintro !>
      rw [← hvo]
      iexact HQ
  · -- the non-plain credit: no one has it
    imod kv_nonplain_false γ γk E hE $$ Hinv Hnp with %Hf
    exact Hf.elim

/-- **The standing update for raft's own entries, from the KV invariant.** -/
theorem kv_noop_au (γ : ServerRaftNames) (γk : KVNames) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvNoopAu γ := by
  have Hdisj := kvN_raftN
  iintro #Hinv
  unfold srvNoopAu
  iintro !> %e %He
  iauintro
  unfold atomic_acc
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, %M, HL, HM, Htok, %Hok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL HM Htok] with -
    · inext; iexists L, M; iframe HL HM Htok; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro ⟨%hidx', HL⟩
    imod Hmask with -
    obtain ⟨hplog, hidx, hc0, hch, hM⟩ := Hok
    have hent : kvEntry γk.c0 γk.ch0 (kvModel γk L) e = kvModel γk L := by
      apply kvEntry_nonwrite
      rcases He with h | h
      · left; exact h
      · right; left; exact h
    imod Hclose $$ [HL HM Htok] with -
    · inext
      iexists L ++ [e], M
      iframe HL HM Htok
      ipureintro
      refine ⟨?_, hidx', ?_, hch, ?_⟩
      · rw [plainLog_append]
        refine ⟨hplog, fun m hm => ?_⟩
        rw [List.mem_singleton] at hm
        subst hm
        intro ht hd'
        rcases He with h | h
        · exact absurd h hd'
        · exact absurd ht h
      · simp only [List.length_append, List.length_singleton]; push_cast; omega
      · intro k vo hk
        unfold kvModel
        rw [kvRaftOf_snoc]
        unfold kvModel at hent
        rw [hent]
        exact hM k vo hk
    imodintro
    itrivial

/-! ## Reads: one update for many clients -/

/-- Firing every registered `Get` update at the model of `L`, the KV authority agreeing. -/
theorem kv_fire_reads (γk : KVNames) (L : List EntryModel) (M : GMap GoString (Option GoString))
    (hM : ∀ k vo, M.lookup k = some vo → vo = kvVal (kvModel γk L) k) :
    ∀ gs : List GName,
      ⊢ ghostMapAuth (GF := GF) γk.map 1 M -∗ ([∗list] g ∈ gs, regOk γk g) -∗
        |={(⊤ \ ↑srvRaftN) \ ↑kvN}=> ghostMapAuth γk.map 1 M ∗ readQs gs L
  | [] => by
    iintro HM -
    imodintro
    iframe HM
    unfold readQs
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | g :: gs => by
    iintro HM #Hgs
    icases (BigSepL.bigSepL_cons (Φ := fun _ g => regOk (GF := GF) γk g)).1 $$ Hgs with
      ⟨#Hg, #Hgs'⟩
    iunfold regOk at Hg
    icases Hg with ⟨%Q, #HQ, #Hd⟩
    iunfold kvDep at Hd
    icases Hd with (⟨%k, %Q0, %HQeq, #Hau⟩ | %HQeq)
    rotate_left
    · imod kv_fire_reads γk L M hM gs $$ HM Hgs' with ⟨HM, #Hrest⟩
      imodintro
      iframe HM
      unfold readQs
      iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
        savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L))).2
      isplitl []
      · iexists Q
        iframe HQ
        rw [HQeq]
        iintro !>; itrivial
      · iexact Hrest
    iunfold kvGetAu at Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%vo, Hpt, Hucl⟩
    iunfold kvPt at Hpt
    ihave %Hlk := ghost_map_lookup $$ HM Hpt
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    imod Hcommit $$ [Hpt] with #HQ0
    · iunfold kvPt; iexact Hpt
    imod kv_fire_reads γk L M hM gs $$ HM Hgs' with ⟨HM, #Hrest⟩
    imodintro
    iframe HM
    unfold readQs
    iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
      savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L))).2
    isplitl []
    · iexists Q
      iframe HQ
      rw [HQeq]
      iintro !> !>
      rw [← hM k vo Hlk]
      iexact HQ0
    · iexact Hrest

/-- **One read update for the registered clients `gs`, from the KV invariant** (see the file
header): at every firing, every client's `Get` update is fired in turn at the current value. -/
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
  icases Hi with ⟨%L, %M, HL, HM, Htok, %Hok⟩
  imod kv_fire_reads γk L M Hok.2.2.2.2 gs $$ HM Hgs with ⟨HM, #HQs⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL HM Htok] with -
    · inext; iexists L, M; iframe HL HM Htok; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL HM Htok] with -
    · inext; iexists L, M; iframe HL HM Htok; ipureintro; exact Hok
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

/-- A put's request has no range set. -/
theorem range_none_of_put (rq : apply.IRRModel) (hk : apply.dispatchKind rq = .put) :
    rq.range = none := by
  cases h : rq.range with
  | none => rfl
  | some r =>
    exfalso
    unfold apply.dispatchKind at hk
    simp only [h, Option.isSome_some, ↓reduceIte] at hk
    repeat' (split at hk)
    all_goals (cases hk)

/-- Whether a request that is neither a put nor a delete is plain depends only on its kind. -/
theorem plainReq_of_kind (rq rq' : apply.IRRModel) (hk : apply.dispatchKind rq' = apply.dispatchKind rq)
    (h1 : apply.dispatchKind rq ≠ .put) (h2 : apply.dispatchKind rq ≠ .deleteRange)
    (hp : plainReq rq) : plainReq rq' := by
  unfold plainReq at hp ⊢
  rw [hk]
  revert hp h1 h2
  cases apply.dispatchKind rq <;> simp

/-- **A proposal's permission carries to the request the wire decodes.** -/
theorem reqPropOk_wire (γk : KVNames) (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) (hw : irrWireOf (apply.withHeader rq hm) rq') :
    reqPropOk γk rq Qr ⊢ reqPropOk γk rq' Qr := by
  obtain ⟨-, -, hk, hrq⟩ := hw
  rw [dispatchKind_withHeader] at hk
  unfold reqPropOk
  iintro (%Hno | ⟨%op, %Q, %Hput, #Hau⟩ | Hnp)
  · ileft
    obtain ⟨hp, h1, h2, hQ⟩ := Hno
    ipureintro
    exact ⟨plainReq_of_kind rq rq' hk h1 h2 hp, by rw [hk]; exact h1, by rw [hk]; exact h2, hQ⟩
  · iright; ileft
    obtain ⟨hp, hkp, hop, hd, ht, hQ⟩ := Hput
    have hnz : irrNoZeroEnd (apply.withHeader rq hm) := by
      refine ⟨?_, ?_, ?_⟩
      · intro o h; simp [apply.withHeader, range_none_of_put rq hkp] at h
      · intro o h; simp [apply.withHeader, hd] at h
      · intro t h; simp [apply.withHeader, ht] at h
    have he := hrq hnz
    subst he
    iexists op, Q
    iframe Hau
    ipureintro
    exact ⟨hp, hkp, hop, hd, ht, hQ⟩
  · iright; iright; iexact Hnp

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
    · iunfold srvRLogLb at HLb; iunfold srvRLogLb; iapply monoListLbOwn_le A hA $$ HLb
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
