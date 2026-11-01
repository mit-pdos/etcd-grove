/-
**The apply thread's KV ghost state in the auth mode `on`** (the auth plan's E2t, 2026-10-26;
`notes/decisions.md`, "E2t of the auth plan"): `kv_applied_step`'s counterpart over E2q's mode-`on`
model (`KVAuthModel.lean`). The apply thread is at the committed raft log `A`, its auth state and KV
log the mode-`on` model of `A` (`kvAppliedOn`); the KV invariant `kvInvOn` keeps the committed log
a mode-`on` log, determinate (`detLogOn`), so the next entry `m` is admitted (`plainEntryOn`) and
determinate at the apply thread's state (`entryDetOn`), and the state after `m` is the model's
(`kvEntryOn`), whose log the apply thread certifies before applying `m` (`kv_cert_step_on`, at the
mode-`on` certificates' invariant `kvCertInvOn`).

What the apply thread does with `m` is the auth applier's (the auth plan's E2s): `outcomeOn` is the
relation its triples give (an admin entry: its step, the log kept; a KV entry the auth layer
refuses at the latest state: nothing; otherwise the entry's write), and at a determinate entry
every such outcome is the model's (`outcomeOn_eq`): the step's outcome is then the next state of
`kvAppliedOn` (`kv_applied_out_on`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A mode-`on` entry grows the log by at most one revision** (`kvEntry_grow`'s counterpart). -/
theorem kvEntryOn_grow (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) :
    (kvEntryOn c₀ ch s m).2 = s.2 ∨ ∃ cs, (kvEntryOn c₀ ch s m).2 = s.2 ++ [cs] := by
  unfold kvEntryOn
  split
  · split
    · split
      · left; rfl
      · split
        · left; rfl
        · exact kvEntry_grow c₀ ch [] s.2 m
    · left; rfl
  · exact kvEntry_grow c₀ ch [] s.2 m

open Classical in
/-- **What the apply thread may make of entry `m` at the state `s`, in the mode `on`** (the
relation the auth applier's triples give, the auth plan's E2s): a normal entry with data that
decodes to `rq` is, above `c₀` and of an admin kind, a successor of its admin step
(`adminStateR`), the log kept; a KV request the auth layer refuses at `s.1` (the latest state:
`auth.isOpPermitted.specL`, E2r), nothing; otherwise the entry's write at `s.1` (`kvEntry`). -/
def outcomeOn (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log) (m : EntryModel)
    (o : auth.AuthState × mvcc.Log) : Prop :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      if uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true then
        adminStateR rq s.1 o.1 ∧ o.2 = s.2
      else if apply.isKVKind (apply.dispatchKind rq) = true ∧ ¬ kvGranted s.1 rq then o = s
      else o = (s.1, kvEntry c₀ ch [] s.2 m)
    | none => o = s
  else o = (s.1, kvEntry c₀ ch [] s.2 m)

/-- **At a determinate entry, every outcome the apply thread may reach is the model's**
(`kvEntryOn`): an admin entry's successor is the unique one (`adminNext_of_det`). -/
theorem outcomeOn_eq (c₀ : w64) (ch : apply.Chain) (s o : auth.AuthState × mvcc.Log)
    (m : EntryModel) (hd : entryDetOn c₀ s m) (ho : outcomeOn c₀ ch s m o) :
    o = kvEntryOn c₀ ch s m := by
  unfold outcomeOn at ho
  unfold kvEntryOn
  split
  · rename_i hm
    rw [if_pos hm] at ho
    split
    · rename_i rq hdec
      rw [hdec] at ho
      simp only at ho
      split
      · rename_i ha
        rw [if_pos ha] at ho
        have hdet := (hd hm.1 hm.2 rq hdec).1 ha.1 ha.2
        obtain ⟨h1, h2⟩ := ho
        exact Prod.ext (adminNext_of_det rq s.1 o.1 hdet h1).symm h2
      · rename_i ha
        rw [if_neg ha] at ho
        split
        · rename_i hr; rw [if_pos hr] at ho; exact ho
        · rename_i hr; rw [if_neg hr] at ho; exact ho
    · rename_i hdec
      rw [hdec] at ho
      exact ho
  · rename_i hm
    rw [if_neg hm] at ho
    exact ho

/-- **The model's outcome is one the apply thread may reach** (`outcomeOn_eq`'s converse, at a
determinate entry): so `outcomeOn` at a determinate entry is exactly the model's step. -/
theorem outcomeOn_model (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (hd : entryDetOn c₀ s m) : outcomeOn c₀ ch s m (kvEntryOn c₀ ch s m) := by
  by_cases hm : m.typ = W32 0 ∧ m.data ≠ []
  · cases hdec : apply.irrDecode m.data with
    | none => simp only [outcomeOn, kvEntryOn, if_pos hm, hdec]
    | some rq =>
      by_cases ha : uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true
      · have hdet := (hd hm.1 hm.2 rq hdec).1 ha.1 ha.2
        simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_pos ha]
        refine ⟨?_, trivial⟩
        simp only [adminNext, dif_pos hdet]
        exact (Classical.choose_spec hdet).1
      · by_cases hr : apply.isKVKind (apply.dispatchKind rq) = true ∧ ¬ kvGranted s.1 rq
        · simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_neg ha, if_pos hr]
        · simp only [outcomeOn, kvEntryOn, if_pos hm, hdec, if_neg ha, if_neg hr]
  · simp only [outcomeOn, kvEntryOn, if_neg hm]

/-! ## The committer's side (the workload's and the proposers' obligation)

When raft's commit extends `kvInvOn`'s committed log `L` by `m`, the invariant asks `m` to be
admitted (`plainEntryOn`) and determinate at the model's state after `L` (`entryDetOn`):
`commitOkOn`, which the workload's entry claims and the proposers establish, as `plainEntry` today.
Then the log stays a mode-`on` log, determinate (`logOn_snoc`), and the client's update fires at
the model's new state: a granted write steps the KV state by its request (`kvModelOn_snoc_granted`),
an admin entry or a refused one keeps it (`kvModelOn_snoc_admin`, `kvModelOn_snoc_refused`). -/

/-- **What a newly committed entry `m` must be, after the committed log `L`, in the mode `on`**:
admitted and determinate at the model's state after `L`. -/
def commitOkOn (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (L : List EntryModel) (m : EntryModel) : Prop :=
  plainEntryOn m ∧ entryDetOn c₀ (kvRaftOfOn c₀ ch s₀ L) m

/-- **The committed log stays a mode-`on` log, determinate**, extended by an entry meeting the
committer's obligation. -/
theorem logOn_snoc (c₀ : w64) (ch : apply.Chain)
    (s₀ : auth.AuthState × mvcc.Log) (L : List EntryModel) (m : EntryModel)
    (hp : plainLogOn L) (hd : detLogOn c₀ ch s₀ L) (hc : commitOkOn c₀ ch s₀ L m) :
    plainLogOn (L ++ [m]) ∧ detLogOn c₀ ch s₀ (L ++ [m]) := by
  refine ⟨fun x hx => ?_, detLogOn_snoc c₀ ch s₀ L m hd hc.2⟩
  rcases List.mem_append.1 hx with h | h
  · exact hp x h
  · simp only [List.mem_singleton] at h; subst h; exact hc.1

/-- The auth layer does not change an entry's write (`chainLog`): the start's chain with auth on
writes as the one with auth off. -/
theorem kvEntry_alarmChain_on (c₀ : w64) (lt : LeaseTable) (log : mvcc.Log) (e : EntryModel) :
    kvEntry c₀ (apply.alarmChain true false false) lt log e =
      kvEntry c₀ (apply.alarmChain false false false) lt log e := by
  have hc : ∀ rq, chainLog (apply.alarmChain true false false) rq lt log =
      chainLog (apply.alarmChain false false false) rq lt log := by
    intro rq
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainLog]
  unfold kvEntry dispatchLog
  split
  · split
    · rfl
    · split
      · rename_i rq _; rw [hc rq]
      · rfl
  · rfl

/-- **The mode-`on` model's log extends the start's** (`kvRaftOf_extends`'s counterpart). -/
theorem kvRaftOfOn_extends (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (A : List EntryModel) : s₀.2 <+: (kvRaftOfOn c₀ ch s₀ A).2 := by
  induction A generalizing s₀ with
  | nil => exact List.prefix_refl _
  | cons m A ih =>
    show s₀.2 <+: (kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s₀ m) A).2
    refine List.IsPrefix.trans ?_ (ih _)
    rcases kvEntryOn_grow c₀ ch s₀ m with h | ⟨cs, h⟩
    · rw [h]; exact List.prefix_refl _
    · rw [h]; exact List.prefix_append _ _

end pure

section commit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The mode-`on` model after `L ++ [e]` is the step of `e` from the model after `L`. -/
theorem kvModelOn_snoc (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) :
    kvModelOn γk st₀ (L ++ [e]) =
      (kvEntryOn γk.c0 γk.ch0 (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L) e).2 := by
  unfold kvModelOn; rw [kvRaftOfOn_snoc]

/-- **A granted plain write's entry steps the KV state by its request** (`kvModel_snoc_state`'s
counterpart), at the start's chain with auth on, above the consistent index: the auth state after
`L` lets it through (`kvGranted`). -/
theorem kvModelOn_snoc_granted (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (hch : γk.ch0 = apply.alarmChain true false false)
    (h0 : γk.log0 ≠ []) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (hna : apply.needAdminPermission rq = false)
    (hg : kvGranted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1 rq)
    (hpc : plainCover rq) :
    kvStateOf (kvModelOn γk st₀ (L ++ [e])) = kvReqStep rq (kvStateOf (kvModelOn γk st₀ L)) := by
  rw [kvModelOn_snoc, kvEntryOn_of_granted _ _ _ e rq hdec hna hg]
  have hm : (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).2 = kvModelOn γk st₀ L := rfl
  simp only
  rw [hm, hch, kvEntry_alarmChain_on, kvEntry_base γk.c0 _ _ e rq ht hd hdec hidx]
  rw [← kvStateOf_backendLog [] rq _ ?_, backendTable_plain rq [] hpc]
  intro he
  apply h0
  have hp := kvRaftOfOn_extends γk.c0 γk.ch0 (st₀, γk.log0) L
  unfold kvModelOn at he
  rw [he] at hp
  exact List.prefix_nil.1 hp

/-- **An admin entry keeps the KV log** (the auth state steps, `kvEntryOn_admin`). -/
theorem kvModelOn_snoc_admin (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (ha : apply.needAdminPermission rq = true) :
    kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
  rw [kvModelOn_snoc, kvEntryOn_admin _ _ _ e rq ht hd hdec hidx ha]
  rfl

/-- **A KV entry the auth state after `L` refuses keeps the KV log.** -/
theorem kvModelOn_snoc_refused (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true)
    (hr : ¬ kvGranted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1 rq) :
    kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
  rw [kvModelOn_snoc, kvEntryOn_of_refused _ _ _ e rq ht hd hdec hna hk hr]
  rfl

end commit

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The certificates' map `C` in the mode `on` (`certMapOk`'s, with the mode-`on` model from the
start's auth state `st₀`). -/
def certMapOkOn (γk : KVNames) (st₀ : auth.AuthState) (C : GMap w64 mvcc.Log) (hi : Nat)
    (Lb : List EntryModel) : Prop :=
  ∀ n l, C.lookup n = some l → l.length ≤ hi ∧ n = W64 (l.length : Int) ∧ l.length < 2 ^ 63 ∧
    ∃ A, A <+: Lb ∧ kvModelOn γk st₀ A = l

/-- **The certificates' invariant in the mode `on`** (`kvCertInv`'s, over `certMapOkOn`). -/
def kvCertInvOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) : IProp GF :=
  inv kvcN iprop(∃ (C : GMap w64 mvcc.Log) (hi : Nat) (Lb : List EntryModel),
    ghostMapAuth γk.cok 1 C ∗ ghostVar γk.hi (1 : Qp).half hi ∗ srvRLogLb γ Lb ∗
    ⌜certMapOkOn γk st₀ C hi Lb ∧ 2 ≤ γk.log0.length⌝)

instance kvCertInvOn_persistent (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    Persistent (kvCertInvOn (GF := GF) γ γk st₀) := by
  unfold kvCertInvOn; infer_instance

/-- **The apply thread's KV ghost state in the mode `on`** at the applied raft log `A` and its auth
state and KV log `s`: `A` committed, `s` its mode-`on` model, the log certified, the longest
certified length (`kvAppliedL`'s). -/
def kvAppliedLOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (s : auth.AuthState × mvcc.Log) : IProp GF :=
  iprop(srvRLogLb γ A ∗ ghostVar γk.hi (1 : Qp).half s.2.length ∗ kvCert γk s.2 ∗
    ⌜s = kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) A⌝)

/-- `kvAppliedLOn` of the apply thread's state `x` and its latest auth state `st`, at the start's
chain (`kvApplied`'s). -/
def kvAppliedOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (x : apply.ApplyKV) (st : auth.AuthState) : IProp GF :=
  iprop(kvAppliedLOn γ γk st₀ A (st, x.log) ∗ ⌜x.chain = γk.ch0⌝)

/-- The namespace of the server's tie of the auth store's history to the log (H5). -/
def authTieN : Namespace := nroot .@ "auth_tie"

/-- **The auth store's history tied to the log** (H5, 2026-10-29; persistent): in the mode
`on γa`, the store's invariant (`auth.authInv`, which keeps its history below the cap,
`auth.authOwn_capped`), and an invariant holding the cap's authority (`auth.capAuth`) at the
history some committed log `A` records (the boot state, then `admStates` from `st₀`): the store's
history is always a prefix of a history of the committed log, and the apply thread raises the cap
by the entry it applies (`authHistTie_raise`). `True` in the other modes. -/
def authHistTie (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) : IProp GF :=
  match E.authMode with
  | .on γa => iprop((∃ (stl : Loc) (R : IProp GF), auth.authInv stl R (.on γa)) ∗
      inv authTieN iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
        auth.capAuth γa (auth.bootState :: admStates γr.kv st₀ A)))
  | _ => iprop(True)

instance authHistTie_persistent (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) :
    Persistent (authHistTie (GF := GF) E γr st₀) := by
  unfold authHistTie; split <;> infer_instance

/-- **The apply thread's KV invariants in the mode `on`** (`srvKVInvs`'s); (H5) with the auth
store's history's tie to the log (`authHistTie`). -/
def srvKVInvsOn (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) : IProp GF :=
  iprop(kvInvOn γr.raft γr.kv st₀ ∗ kvCertInvOn γr.raft γr.kv st₀ ∗ srvRaftLogInv γr.raft ∗
    authHistTie E γr st₀ ∗ ⌜E.γ.cok = γr.kv.cok⌝)

instance srvKVInvsOn_persistent (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) :
    Persistent (srvKVInvsOn (GF := GF) E γr st₀) := by
  unfold srvKVInvsOn; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The apply thread certifies the mode-`on` model's log after the next committed entry**
(`kv_cert_step`'s counterpart). -/
theorem kv_cert_step_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (E : CoPset)
    (hE : ↑kvcN ⊆ E) (A : List EntryModel) (m : EntryModel) (s s' : auth.AuthState × mvcc.Log)
    (hs' : s' = kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) (A ++ [m]))
    (hg : s'.2 = s.2 ∨ ∃ cs, s'.2 = s.2 ++ [cs]) (hlen : s'.2.length < 2 ^ 63) :
    ⊢ kvCertInvOn (GF := GF) γ γk st₀ -∗ kvAppliedLOn γ γk st₀ A s -∗ srvRLogLb γ (A ++ [m]) ={E}=∗
      kvAppliedLOn γ γk st₀ (A ++ [m]) s' := by
  iintro #Hinv Ha #Hlb
  iunfold kvAppliedLOn at Ha
  icases Ha with ⟨#HA, Hhi, #Hc, %Hl⟩
  have hm' : kvModelOn γk st₀ (A ++ [m]) = s'.2 := by unfold kvModelOn; rw [hs']
  rcases hg with hg | ⟨cs, hg⟩
  · imodintro
    iunfold kvAppliedLOn
    rw [hg]
    iframe Hlb Hhi Hc
    ipureintro; exact hs'
  · iunfold kvCertInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hhe := ghostVar_agree γk.hi _ _ _ _ $$ Hhi Hhi'
    rw [hg] at hlen hm'
    have hfresh : C.lookup (W64 ((s.2 ++ [cs]).length : Int)) = none := by
      cases h : C.lookup (W64 ((s.2 ++ [cs]).length : Int)) with
      | none => rfl
      | some l'' =>
        obtain ⟨h1, h2, h3, -⟩ := Hok.1 _ _ h
        have := w64_len_inj _ _ hlen h3 h2
        simp only [List.length_append, List.length_singleton] at this
        omega
    imod ghost_map_insert_persist _ (s.2 ++ [cs]) hfresh $$ HC with ⟨HC, #He⟩
    imod ghostVar_update_halves (s.2 ++ [cs]).length γk.hi _ _ $$ Hhi Hhi' with ⟨Hhi, Hhi'⟩
    ihave %Hcmp := srvRLogLb_prefix γ (A ++ [m]) Lb $$ [Hlb HLb]
    · iframe Hlb HLb
    have hold : ∀ n l2, C.lookup n = some l2 → l2.length ≤ (s.2 ++ [cs]).length := by
      intro n l2 hn
      have := (Hok.1 n l2 hn).1
      simp only [List.length_append, List.length_singleton]
      omega
    imod Hclose $$ [HC Hhi'] with -
    · inext
      rcases Hcmp with h | h
      · iexists C.insert (W64 ((s.2 ++ [cs]).length : Int)) (s.2 ++ [cs]), (s.2 ++ [cs]).length, Lb
        iframe HC Hhi' HLb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A ++ [m], h, hm'⟩
        · obtain ⟨-, h2, h3, A', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A', h4, h5⟩
      · iexists C.insert (W64 ((s.2 ++ [cs]).length : Int)) (s.2 ++ [cs]), (s.2 ++ [cs]).length,
          A ++ [m]
        iframe HC Hhi' Hlb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A ++ [m], List.prefix_refl _, hm'⟩
        · obtain ⟨-, h2, h3, A', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A', h4.trans h, h5⟩
    imodintro
    iunfold kvAppliedLOn
    rw [hg]
    iframe Hlb Hhi
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; exact hs'

/-- **The apply thread's step on the next committed entry `m`, in the mode `on`**
(`kv_applied_step`'s counterpart): `m` admitted (`plainEntryOn`) and determinate at the apply
thread's state (`entryDetOn`), the chain the start's (auth on), and the state after `m` the
model's (`kvEntryOn`), certified. -/
theorem kv_applied_step_on (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : apply.ApplyKV) (st : auth.AuthState)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log) m).2.length < 2 ^ 63) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainEntryOn m ∧ entryDetOn γr.kv.c0 (st, x.log) m ∧ x.chain = γr.kv.ch0 ∧
        x.chain = apply.alarmChain true false false⌝ ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) (kvEntryOn γr.kv.c0 x.chain (st, x.log) m) := by
  iintro #Hinvs Ha #Hlb
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, -, %Hcok⟩
  iunfold kvAppliedOn at Ha
  icases Ha with ⟨Ha, %Hch⟩
  imod kv_log_plain_on γr.raft γr.kv st₀ (A ++ [m]) $$ HkI HrI Hlb with %Hpc
  obtain ⟨Hpl, Hdet, Hch0⟩ := Hpc
  ihave %Hl : iprop(⌜(st, x.log) = kvRaftOfOn γr.kv.c0 γr.kv.ch0 (st₀, γr.kv.log0) A⌝) $$ [Ha]
  · iunfold kvAppliedLOn at Ha; icases Ha with ⟨-, -, -, %h⟩; ipureintro; exact h
  have hs' : kvEntryOn γr.kv.c0 x.chain (st, x.log) m =
      kvRaftOfOn γr.kv.c0 γr.kv.ch0 (st₀, γr.kv.log0) (A ++ [m]) := by
    rw [kvRaftOfOn_snoc, ← Hl, Hch]
  have hd : entryDetOn γr.kv.c0 (st, x.log) m := by
    have h := Hdet A.length m (by simp)
    rw [List.take_left' rfl, ← Hl] at h
    exact h
  imod kv_cert_step_on γr.raft γr.kv st₀ ⊤ (fun _ _ => CoPset.mem_full) A m (st, x.log) _ hs'
    (kvEntryOn_grow γr.kv.c0 x.chain (st, x.log) m) hlen $$ HcI Ha Hlb with Ha
  imodintro
  iframe Ha
  ipureintro
  exact ⟨Hpl m (by simp), hd, Hch, Hch.trans Hch0⟩

/-- **The apply thread's outcome is the model's** (`kv_applied_step_on` with the auth applier's
outcome, E2s): any outcome `o` the apply thread reaches on `m` (`outcomeOn`) is the next state of
`kvAppliedLOn`. -/
theorem kv_applied_out_on (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) (x : apply.ApplyKV) (st : auth.AuthState)
    (o : auth.AuthState × mvcc.Log)
    (hlen : (kvEntryOn γr.kv.c0 x.chain (st, x.log) m).2.length < 2 ^ 63)
    (hout : entryDetOn γr.kv.c0 (st, x.log) m → outcomeOn γr.kv.c0 x.chain (st, x.log) m o) :
    ⊢ srvKVInvsOn (GF := GF) E γr st₀ -∗ kvAppliedOn γr.raft γr.kv st₀ A x st -∗
      srvRLogLb γr.raft (A ++ [m]) ={⊤}=∗
      ⌜plainEntryOn m ∧ x.chain = apply.alarmChain true false false⌝ ∗
      kvAppliedLOn γr.raft γr.kv st₀ (A ++ [m]) o := by
  iintro #Hinvs Ha #Hlb
  imod kv_applied_step_on E γr st₀ A m x st hlen $$ Hinvs Ha Hlb with ⟨%Hp, Ha⟩
  obtain ⟨Hpl, hd, -, hch⟩ := Hp
  have ho := hout hd
  rw [outcomeOn_eq γr.kv.c0 x.chain (st, x.log) o m hd ho]
  imodintro
  iframe Ha
  ipureintro
  exact ⟨Hpl, hch⟩

end lemmas

end EtcdGrove
end Perennial
