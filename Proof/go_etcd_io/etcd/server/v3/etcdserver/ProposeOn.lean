/-
**A proposal's update in the auth mode `on`** (the auth plan's E2w, 2026-10-26;
`notes/decisions.md`, "E2w of the auth plan"): `kv_prop_au`'s counterpart over the mode-`on` KV
invariant (`kvInvOn`, E2q), which a proposer of the server in the mode `on` hands raft. The design
(decided 2026-10-26): **a client's KV update fires at the commit only if the auth state after the
committed log grants the request** (`kvGranted`, at the model's auth state: `grantedAt`); otherwise
nothing fires, the KV state is kept (`kvModelOn_snoc_refused`), and the proposer's result says the
request was refused (`⌜¬ grantedAt …⌝`), which the apply thread's refusal answers to the client.

- `reqPropOkOn`: what a proposal of `rq` needs in the mode `on` (`reqPropOk`'s first and third
  cases: no KV write; a plain write with its client's update fired at most once, `kvOpAu1`), with
  the request's permissions all of the shape the permission cache decides (`kvShapeAll`), so the
  entry is determinate at any state (`commitOkOn_plain`, the committer's obligation `commitOkOn`).
- `kv_prop_au_on`: the proposal's update from `kvInvOn`: the invariant extended by the entry
  (`kvInvOn_facts_snoc`, `kvWorkOn_snoc`), the client's update fired when granted
  (`kvModelOn_snoc_granted`), the state kept when refused or write-free.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthShape

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- A plain request needs no admin permission (`plainCover`'s clause of each kind). -/
theorem plainReq_noAdminP (rq : apply.IRRModel) (h : plainReq rq) :
    apply.needAdminPermission rq = false := by
  obtain ⟨hc, -⟩ := h
  unfold plainCover at hc
  split at hc <;> first | exact hc.2.1 | exact hc.2 | exact hc.elim

/-- A covered request with a KV operation is of a KV kind (unit T3: a lease's grant or revocation
has a KV operation too, but is not covered). -/
theorem reqKVOp_isKV (rq : apply.IRRModel) (op : KVOp) (h : reqKVOp rq = some op)
    (hp : plainCover rq) : apply.isKVKind (apply.dispatchKind rq) = true := by
  unfold reqKVOp at h
  unfold plainCover at hp
  cases hk : apply.dispatchKind rq <;> rw [hk] at h hp <;> first | rfl | exact (hp : False).elim | (simp at h)

theorem kvDet_of_shapeAll (st : auth.AuthState) (rq : apply.IRRModel) (h : kvShapeAll rq) :
    kvDet st rq := fun _ => h

/-- **The committer's obligation for a plain request's entry** (`commitOkOn`): admitted (plain), and
determinate at any state (no admin permission needed; its check decided, `kvShapeAll`). -/
theorem commitOkOn_plain (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (L : List EntryModel) (e : EntryModel) (d : List w8) (rq : apply.IRRModel)
    (hed : e.data = d) (hdec : apply.irrDecode d = some rq) (hp : plainReq rq)
    (hz : irrNoZeroEnd rq) (hs : kvShapeAll rq) : commitOkOn c₀ ch s₀ L e := by
  refine ⟨fun _ _ rq' h => ?_, fun _ _ rq' h => ?_⟩
  · rw [hed, hdec] at h; cases h; exact Or.inl ⟨hp, noZeroEnds_of_irr rq hz, hs⟩
  · rw [hed, hdec] at h
    cases h
    refine ⟨fun _ ha => ?_, fun _ => kvDet_of_shapeAll _ _ hs⟩
    rw [plainReq_noAdminP rq hp] at ha
    cases ha

/-- An admitted admin request is not a KV request. -/
theorem adminKindOk_nonKV' (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.isKVKind (apply.dispatchKind rq) = false := by
  unfold apply.adminKindOk at h
  split at h <;> simp_all [apply.isKVKind]

/-- **What an admin proposal needs in the mode `on`** (the auth plan's E3m; `KVAuthShape.lean`): an
admitted admin request (`adminKindOk`: one needing the admin permission, or (C1's A3) an
`Authenticate`, which needs none and leaves the model's state), whose `UserAdd` (if any) has a
password choice that cannot fail, from a start whose users' roles are sorted; and (E3o) with no read
field set (`noSideEffect`: `plainEntryOn`'s). (Until E3z it also excluded `RoleGrantPermission`,
determinate then only at a role with no permission; until C1's A3 it required the admin
permission, excluding `Authenticate`. For an `Authenticate` the name is wider than the request:
it needs no admin permission, and its `adminPropRes` holds trivially, the model's state kept.) -/
def adminPropOk (st₀ : auth.AuthState) (rq : apply.IRRModel) : Prop :=
  apply.adminKindOk rq ∧ apply.noSideEffect rq = false ∧
    (∀ m, rq.authUserAdd = some m → m.pwSure) ∧ rolesSorted st₀

/-- **The committer's obligation for an admin entry** (`commitOkOn`): admitted, and determinate
at the state after any log (the users' roles sorted along the model, `rolesSorted_kvRaftOfOn`;
`authDet_of_sorted`). -/
theorem commitOkOn_admin (c₀ : w64) (ch : apply.Chain) (st₀ : auth.AuthState) (log₀ : mvcc.Log)
    (L : List EntryModel) (e : EntryModel) (d : List w8) (rq : apply.IRRModel)
    (hed : e.data = d) (hdec : apply.irrDecode d = some rq) (ha : adminPropOk st₀ rq) :
    commitOkOn c₀ ch (st₀, log₀) L e := by
  obtain ⟨hk, hns, hpw, hsort⟩ := ha
  refine ⟨fun _ _ rq' h => ?_, fun _ _ rq' h => ?_⟩
  · rw [hed, hdec] at h; cases h; exact Or.inr ⟨hk, hns⟩
  · rw [hed, hdec] at h
    cases h
    refine ⟨fun _ _ => ?_, fun hkv => ?_⟩
    · apply authDet_of_sorted
      · exact rolesSorted_kvRaftOfOn c₀ ch _ L hsort
      · exact hpw
    · rw [adminKindOk_nonKV' rq hk] at hkv; cases hkv

/-- **A write-free entry keeps the mode-`on` model's state** (auth state and log): a request that
needs no admin permission and writes nothing, let through or refused. -/
theorem kvEntryOn_nonwrite (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (e : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode e.data = some rq)
    (hna : apply.needAdminPermission rq = false)
    (hnw : ¬ writeKind (apply.dispatchKind rq)) :
    kvEntryOn c₀ ch s e = s := by
  have hk : kvEntry c₀ ch [] s.2 e = s.2 := by
    apply kvEntry_nonwrite
    right; right
    intro rq' h
    rw [hdec] at h
    cases h
    exact hnw
  unfold kvEntryOn
  split
  · rw [hdec]
    simp only [hna, Bool.false_eq_true, and_false, ↓reduceIte]
    split
    · rfl
    · rw [hk]
  · rw [hk]

/-- **The request is granted after the committed log `L`**: the mode-`on` model's auth state after
`L` lets it through. -/
def grantedAt (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel) (L : List EntryModel) :
    Prop :=
  kvGranted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1 rq

/-- **The auth state after the committed log `L`** in the server's mode-`on` model (from the
start's state `st₀`). -/
def srvAuthAtLog (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) : auth.AuthState :=
  (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1

/-- `grantedAt` is the auth layer's verdict at the auth state after `L` (a law, so a client of
`writeGrantG` need not unfold the model; the auth-mode merge's step 5). -/
theorem grantedAt_iff (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel)
    (L : List EntryModel) : grantedAt γk st₀ rq L ↔ kvGranted (srvAuthAtLog γk st₀ L) rq :=
  Iff.rfl

theorem admStates_nil (γk : KVNames) (st₀ : auth.AuthState) : admStates γk st₀ [] = [st₀] := rfl

theorem admStates_snoc_adm (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (m : EntryModel) (h : admEntry γk.c0 (srvAuthAtLog γk st₀ L) m) :
    admStates γk st₀ (L ++ [m]) = admStates γk st₀ L ++ [srvAuthAtLog γk st₀ (L ++ [m])] :=
  admStatesR_snoc_adm _ _ _ _ _ h

theorem admStates_snoc_other (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (m : EntryModel) (h : ¬ admEntry γk.c0 (srvAuthAtLog γk st₀ L) m) :
    admStates γk st₀ (L ++ [m]) = admStates γk st₀ L :=
  admStatesR_snoc_other _ _ _ _ _ h

/-- The history's last state is the auth state after the log. -/
theorem admStates_last (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) :
    (admStates γk st₀ L).getLast? = some (srvAuthAtLog γk st₀ L) :=
  admStatesR_last _ _ _ _

theorem admStates_ne_nil (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) :
    admStates γk st₀ L ≠ [] := by
  intro h; have := admStates_last γk st₀ L; rw [h] at this; cases this

theorem admStates_prefix (γk : KVNames) (st₀ : auth.AuthState) (L₁ L₂ : List EntryModel)
    (h : L₁ <+: L₂) : admStates γk st₀ L₁ <+: admStates γk st₀ L₂ :=
  admStatesR_prefix _ _ _ _ _ h

/-- **Logs with the same history have the same auth state.** -/
theorem srvAuthAtLog_of_admStates (γk : KVNames) (st₀ : auth.AuthState) (L₁ L₂ : List EntryModel)
    (h : admStates γk st₀ L₁ = admStates γk st₀ L₂) :
    srvAuthAtLog γk st₀ L₁ = srvAuthAtLog γk st₀ L₂ := by
  have h1 := admStates_last γk st₀ L₁
  rw [h, admStates_last] at h1
  exact (Option.some.inj h1).symm

/-- The history's last state, with the start's as the default. -/
theorem admStates_getLastD (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (d : auth.AuthState) : (admStates γk st₀ L).getLastD d = srvAuthAtLog γk st₀ L := by
  rw [List.getLastD_eq_getLast?, admStates_last]; rfl

/-- **An entry of `rq` after `L` is recorded in the history** (the auth-mode merge's 5b): the
auth state after `L` admits its principal and its step changes the state. -/
def admRec (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel) (L : List EntryModel) :
    Prop :=
  auth.adminOk (srvAuthAtLog γk st₀ L) (some (auth.authInfoM (apply.principalOf rq))) ∧
    adminNext rq (srvAuthAtLog γk st₀ L) ≠ srvAuthAtLog γk st₀ L

/-- An entry of a request needing the admin permission is recorded exactly when `admRec`. -/
theorem admEntry_iff_admRec (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hv : uint.Z γk.c0 < uint.Z e.index)
    (ha : apply.needAdminPermission rq = true) :
    admEntry γk.c0 (srvAuthAtLog γk st₀ L) e ↔ admRec γk st₀ rq L := by
  unfold admEntry admRec
  constructor
  · rintro ⟨-, -, rq', hdec', -, -, h1, h2⟩
    rw [hdec] at hdec'; cases hdec'; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨ht, hd, rq, hdec, hv, ha, h1, h2⟩

/-- **An admitted admin entry steps the auth state by the model's step.** -/
theorem srvAuthAtLog_snoc_adm (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z γk.c0 < uint.Z m.index)
    (ha : apply.needAdminPermission rq = true) :
    srvAuthAtLog γk st₀ (L ++ [m]) = adminNext rq (srvAuthAtLog γk st₀ L) := by
  unfold srvAuthAtLog
  rw [kvRaftOfOn_snoc, kvEntryOn_admin _ _ _ m rq ht hd hdec hv ha]

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Logs with the same requested entries have the same history. -/
theorem admStates_eqv (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A B : List EntryModel) (h : srvEqv γ A B) (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) :
    admStates γk st₀ A = admStates γk st₀ B :=
  admStatesR_eqv γ _ _ _ A B h hc


/-- **A plain write's result in the mode `on`** at the committed log `L` before its entry: granted,
with the client's result at the state after `L` (left at the token `γc`, `kvRes`); or refused. -/
def grantedRes (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel) (γc : GName)
    (Q : KVState → IProp GF) (L : List EntryModel) : IProp GF :=
  iprop((⌜grantedAt γk st₀ rq L⌝ ∗ kvRes γc Q (kvStateOf (kvModelOn γk st₀ L))) ∨
    ⌜¬ grantedAt γk st₀ rq L⌝)

instance grantedRes_persistent (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel)
    (γc : GName) (Q : KVState → IProp GF) (L : List EntryModel) :
    Persistent (grantedRes (GF := GF) γk st₀ rq γc Q L) := by
  unfold grantedRes; infer_instance

/-- **An admin proposal's result in the mode `on`** at the committed log `L` before its entry: the
users' roles sorted there and the entry determinate, so the auth state after it is the model's step
`adminNext rq` of the state after `L` (the auth plan's E3m). -/
def adminPropRes (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel) (L : List EntryModel) :
    IProp GF :=
  iprop(⌜rolesSorted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1 ∧
    authDet rq (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1⌝)

/-- **A write's grant, as the server tells its client's update at the commit** (persistent; the
auth-mode merge's step 5, 2026-10-29): for some header `hm` the server stamped on the request
`rq₀`, one the caller's binding admits (`Gb hm`: with the server's, `hdrBoundM true`), the
committed prefix `L` of the server's requested log before the write's entry extends the caller's
lower bound `L₀` (`srvReqLogLb`), the model grants the stamped request there (`grantedAt`), and
`L`'s KV state is the one the update linearizes at; (5b) and a lower bound of the auth history
along `L` (`authHistLb`). The margin: stated in the server's model of
the log (`grantedAt`), not in a client's vocabulary (`grantedAt_iff`). -/
def writeGrantG (γk : KVNames) (st₀ : auth.AuthState) (Gb : apply.HeaderModel → IProp GF)
    (rq₀ : apply.IRRModel) (L₀ : List EntryModel) (σ : KVState) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (L : List EntryModel), Gb hm ∗
    authHistLb γk (admStates γk st₀ L) ∗
    ⌜L₀ <+: L ∧ grantedAt γk st₀ (apply.withHeader rq₀ hm) L ∧
      kvStateOf (kvModelOn γk st₀ L) = σ⌝)

/-- A grant at a binding `Gb'` that gives `Gb` is one at `Gb` (the contexts a server derives from
a request's bind the same headers, `hdrBoundM_ctx`). -/
theorem writeGrantG_mono (γk : KVNames) (st₀ : auth.AuthState) (Gb Gb' : apply.HeaderModel → IProp GF)
    (rq₀ : apply.IRRModel) (L₀ : List EntryModel) (σ : KVState) (h : ∀ hm, Gb' hm ⊢ Gb hm) :
    writeGrantG γk st₀ Gb' rq₀ L₀ σ ⊢ writeGrantG γk st₀ Gb rq₀ L₀ σ := by
  unfold writeGrantG
  iintro ⟨%hm, %L, Hb, #Hh, %Hp⟩
  iexists hm, L
  isplitl
  · iapply h $$ Hb
  iframe Hh
  ipureintro; exact Hp

/-- **A client's update of the auth history by the admin request `rq₀`** (persistent; the
auth-mode merge's 5b): fired at the commit of each entry of `rq₀` the model records in the history
(`admEntry`), from the view `hs` (`authHistView`) to the view after the entry. It is told the
header `hm` the server stamped (one the caller's binding admits, `Gb hm`), the logs `L` before the
entry and `L ++ [e]` after it, the entry's admission at `hs`'s last state (`auth.adminOk`) and its
step's determinacy there (`authDet`), and the history after it; `□ Q hs`. -/
def histAu (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (hs : List auth.AuthState), authHistView γk hs }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
    <{ ∃ (hm : apply.HeaderModel) (L : List EntryModel) (e : EntryModel),
         Gb hm ∗ srvReqLogLb γ L ∗ srvReqLogLb γ (L ++ [e]) ∗
         ⌜apply.irrDecode e.data = some (apply.withHeader rq₀ hm) ∧ admStates γk st₀ L = hs ∧
          auth.adminOk (hs.getLastD st₀)
            (some (auth.authInfoM (apply.principalOf (apply.withHeader rq₀ hm)))) ∧
          authDet (apply.withHeader rq₀ hm) (hs.getLastD st₀) ∧
          admStates γk st₀ (L ++ [e]) =
            hs ++ [adminNext (apply.withHeader rq₀ hm) (hs.getLastD st₀)]⌝ ∗
         authHistView γk (hs ++ [adminNext (apply.withHeader rq₀ hm) (hs.getLastD st₀)]),
       COMM □ Q hs }>)

instance histAu_persistent (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) : Persistent (histAu (GF := GF) γ γk st₀ Gb rq₀ Q) := by
  unfold histAu; infer_instance

/-- An update told a weaker header bound (`Gb ⊢ Gb'`) is one told the stronger. -/
theorem histAu_mono (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb Gb' : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) (h : ∀ hm, Gb hm ⊢ Gb' hm) :
    histAu (GF := GF) γ γk st₀ Gb' rq₀ Q ⊢ histAu γ γk st₀ Gb rq₀ Q := by
  unfold histAu
  refine intuitionistically_mono (aupd_post_mono (fun x y => ?_))
  rcases x with ⟨hs, ⟨⟩⟩
  simp only [Std.Tele.app, ULift.down]
  iintro ⟨%hm, %L, %e, Hb, Hr⟩
  iexists hm, L, e
  iframe Hr
  iapply h $$ Hb

/-- **An admin request's result for its client's history update** at the log `L` before its
entry (persistent; 5b): a lower bound of the history along `L` (`authHistLb`: what ties a reply's
state to its client's view), and recorded (`admRec`) with the update's result at the history along
`L`, or not recorded (the auth state kept). -/
def adminRecRes (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) (L : List EntryModel) : IProp GF :=
  iprop(authHistLb γk (admStates γk st₀ L) ∗
    ((⌜admRec γk st₀ rq L⌝ ∗ □ Q (admStates γk st₀ L)) ∨ ⌜¬ admRec γk st₀ rq L⌝))

instance adminRecRes_persistent (γk : KVNames) (st₀ : auth.AuthState) (rq : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) (L : List EntryModel) :
    Persistent (adminRecRes (GF := GF) γk st₀ rq Q L) := by
  unfold adminRecRes; infer_instance

/-- **What a proposal of `rq₀` stamped with the header `hm` needs in the mode `on`**
(`reqPropOk`'s, see the header): a plain request with no KV write (`Qr` trivial); or a plain
request of the KV operation `op` with its client's update fired at most once, `Qr` its result if
granted (`grantedRes`), the update told its grant when it fires (`writeGrantG`, at the client's
lower bound `L₀` of the requested log; the auth-mode merge's step 5). Either with every permission
of the cache's shape (`kvShapeAll`). Or (E3m) an admin request meeting `adminPropOk`, `Qr` its
step's determinacy at the commit (`adminPropRes`): one needing no admin permission (C1's
`Authenticate`) with nothing else; one needing it (5b) with its client's update of the auth
history (`histAu`), `Qr` also its result if recorded (`adminRecRes`). -/
def reqPropOkOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop((⌜plainReq (apply.withHeader rq₀ hm) ∧ ¬ writeKind (apply.dispatchKind (apply.withHeader rq₀ hm)) ∧
      irrNoZeroEnd (apply.withHeader rq₀ hm) ∧ rqShape (apply.withHeader rq₀ hm) ∧
      kvShapeAll (apply.withHeader rq₀ hm) ∧ Qr = fun _ => iprop(True)⌝) ∨
    (∃ (op : KVOp) (Q : KVState → IProp GF) (γc : GName) (L₀ : List EntryModel),
      ⌜plainReq (apply.withHeader rq₀ hm) ∧ reqKVOp (apply.withHeader rq₀ hm) = some op ∧
        irrNoZeroEnd (apply.withHeader rq₀ hm) ∧ rqShape (apply.withHeader rq₀ hm) ∧
        kvShapeAll (apply.withHeader rq₀ hm) ∧ Qr = grantedRes γk st₀ (apply.withHeader rq₀ hm) γc Q⌝ ∗
      srvReqLogLb γ L₀ ∗ kvAu1G γk (kvOpStep op) (writeGrantG γk st₀ Gb rq₀ L₀) Q) ∨
    ⌜adminPropOk st₀ (apply.withHeader rq₀ hm) ∧ irrNoZeroEnd (apply.withHeader rq₀ hm) ∧
      apply.needAdminPermission (apply.withHeader rq₀ hm) = false ∧
      Qr = adminPropRes γk st₀ (apply.withHeader rq₀ hm)⌝ ∨
    (∃ Q : List auth.AuthState → IProp GF,
      ⌜adminPropOk st₀ (apply.withHeader rq₀ hm) ∧ irrNoZeroEnd (apply.withHeader rq₀ hm) ∧
        apply.needAdminPermission (apply.withHeader rq₀ hm) = true ∧
        Qr = fun L => iprop(adminPropRes γk st₀ (apply.withHeader rq₀ hm) L ∗
          adminRecRes γk st₀ (apply.withHeader rq₀ hm) Q L)⌝ ∗
      histAu γ γk st₀ Gb rq₀ Q))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem kvModelOn_snoc_nonwrite (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode e.data = some rq)
    (hna : apply.needAdminPermission rq = false)
    (hnw : ¬ writeKind (apply.dispatchKind rq)) :
    kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
  rw [kvModelOn_snoc, kvEntryOn_nonwrite _ _ _ e rq hdec hna hnw]
  rfl

/-- **The mode-`on` workload facts, one entry on** (`kvWork_snoc`'s). -/
theorem kvWorkOn_snoc (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (hs : entryShapeOn e) (hc : e.typ ≠ W32 0 → ccPolOk cfg e.data) :
    ⊢ kvWorkOn (GF := GF) cfg γk L -∗ entryClaim γk.ids e -∗ kvWorkOn cfg γk (L ++ [e]) := by
  iintro Hw #He
  iunfold kvWorkOn at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  iunfold kvWorkOn
  isplitr
  · ipureintro
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Hsh.1 m hm
      · subst hm; exact hs
    · rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Hsh.2 m hm
      · subst hm; exact hc
  iapply BigSepL.bigSepL_snoc.2
  iframe Hcl He

/-- **A proposal's update in the mode `on`, from the mode-`on` KV invariant** (`kv_prop_au`'s; see
the header): for data claimed under the request's id. -/
theorem kv_prop_au_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (d : List w8)
    (Gb : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) (hd : d ≠ [])
    (hdec : apply.irrDecode d = some (apply.withHeader rq₀ hm)) (id : w64) (γf : GName)
    (hid : apply.irrId (apply.withHeader rq₀ hm) = some id) (E : CoPset) (hE : ↑kvN ⊆ E) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ idClaim γk.ids id d γf -∗ idRegd γk.ids id -∗ □ Gb hm -∗
      reqPropOkOn γ γk st₀ Gb rq₀ hm Qr ={E}=∗ srvPropAu1 γ d Qr := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hcl #Hreg #Hgb Hok
  have hsh : ∀ e : EntryModel, e.typ = W32 0 → e.data = d → rqShape (apply.withHeader rq₀ hm) → entryShapeOn e := by
    intro e het hed hs
    refine ⟨fun _ => Or.inr ⟨(apply.withHeader rq₀ hm), by rw [hed]; exact hdec, ⟨id, hid⟩, Or.inl hs⟩,
      fun h => absurd het h⟩
  ihave #Hecl : iprop(∀ e : EntryModel, ⌜e.data = d⌝ -∗ entryClaim γk.ids e) $$ []
  · iintro %e %hed
    iunfold entryClaim
    iright
    iexists (apply.withHeader rq₀ hm), id, γf
    rw [hed]
    iframe Hcl Hreg
    ipureintro; exact ⟨hdec, hid⟩
  iunfold reqPropOkOn at Hok
  icases Hok with (%Hno | ⟨%op, %Q, %γc, %L₀, %Hop, #HL₀, Hau⟩ | Had)
  · -- no KV write: the state kept, granted or refused
    obtain ⟨hplain, hnw, hz, hshape, hsa, hQr⟩ := Hno
    subst hQr
    imodintro
    unfold srvPropAu1
    iauintro
    unfold atomic_acc
    iunfold kvInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
    iintro Hmask
    iexists L
    iframe HL
    isplit
    · iintro HL
      imod Hmask with -
      imod Hclose $$ [HL Hσ Hh] with -
      · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
      imodintro
      itrivial
    · iintro %e ⟨%He, HL⟩
      imod Hmask with -
      obtain ⟨het, hed, hidx⟩ := He
      have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.2.1 hidx (Or.inl het)
      have hent : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L :=
        kvModelOn_snoc_nonwrite γk st₀ L e (apply.withHeader rq₀ hm) (by rw [hed]; exact hdec)
          (plainReq_noAdminP (apply.withHeader rq₀ hm) hplain) hnw
      ihave #Hw' := kvWorkOn_snoc γ.raft γk L e (hsh e het hed hshape)
        (fun h => absurd het h) $$ Hw (Hecl $$ %e %hed)
      imod Hclose $$ [HL Hσ Hh] with -
      · inext
        iexists L ++ [e]
        rw [hent]
        rw [admStates_snoc_noadmin γk st₀ L e (apply.withHeader rq₀ hm) (by rw [hed]; exact hdec)
          (plainReq_noAdminP (apply.withHeader rq₀ hm) hplain)]
        iframe HL Hσ Hh Hw'
        ipureintro
        exact kvInvOn_facts_snoc γ γk st₀ L e Hok hidx'
          (commitOkOn_plain _ _ _ L e d (apply.withHeader rq₀ hm) hed hdec hplain hz hsa)
      imodintro
      iintro !>
      itrivial
  · -- a plain write, with its client's update fired at most once, when granted
    obtain ⟨hplain, hop, hz, hshape, hsa, hQr⟩ := Hop
    subst hQr
    have hna := plainReq_noAdminP (apply.withHeader rq₀ hm) hplain
    have hkv := reqKVOp_isKV (apply.withHeader rq₀ hm) op hop hplain.1
    iunfold kvAu1G at Hau
    imodintro
    unfold srvPropAu1
    iauintro
    unfold atomic_acc
    iunfold kvInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
    -- (step 5) the client's lower bound is a prefix of the log before the entry
    ihave ⟨HL, %HL₀p⟩ := srvReqLogLb_prefix γ L L₀ $$ [HL HL₀]
    · iframe HL HL₀
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
      imod Hclose $$ [HL Hσ Hh] with -
      · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
      imodintro
      iexact Hau
    · iintro %e ⟨%He, HL⟩
      obtain ⟨het, hed, hidx⟩ := He
      have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.2.1 hidx (Or.inl het)
      have hdata : e.data ≠ [] := by rw [hed]; exact hd
      ihave #Hw' := kvWorkOn_snoc γ.raft γk L e (hsh e het hed hshape)
        (fun h => absurd het h) $$ Hw (Hecl $$ %e %hed)
      have hfacts := kvInvOn_facts_snoc γ γk st₀ L e Hok hidx'
        (commitOkOn_plain _ _ _ L e d (apply.withHeader rq₀ hm) hed hdec hplain hz hsa)
      by_cases hg : grantedAt γk st₀ (apply.withHeader rq₀ hm) L
      · -- granted: the client's update fires at the commit
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
        imod ghostVar_update_halves (kvOpStep op σ) γk.st _ _ $$ Hσ Hc with ⟨Hσ, Hc⟩
        ihave #Hhl := monoListLbOwn_get γk.hist _ _ $$ Hh
        imod Hcommit $$ [Hc] with HQ
        · iunfold etcdKV
          iframe Hc
          -- (step 5) the update told its grant, and (5b) the history along `L`
          iunfold writeGrantG
          iexists hm, L
          iframe Hgb
          isplitr
          · iunfold authHistLb; iexact Hhl
          ipureintro
          exact ⟨HL₀p, hg, Hag⟩
        imod kvRes_alloc γc Q σ _ $$ HQ with #HQ
        have hidxe : uint.Z γk.c0 < uint.Z e.index := by
          have := Hok.2.2.2.1
          omega
        have hst : kvStateOf (kvModelOn γk st₀ (L ++ [e])) = kvOpStep op σ := by
          rw [kvModelOn_snoc_granted γk st₀ L e (apply.withHeader rq₀ hm) Hok.2.2.2.2.1 Hok.2.2.2.2.2 het hdata
            (by rw [hed]; exact hdec) hidxe hna hg
            hplain.1, Hag]
          unfold kvReqStep; rw [hop]
        imod Hclose $$ [HL Hσ Hh] with -
        · inext
          iexists L ++ [e]
          rw [hst]
          rw [admStates_snoc_noadmin γk st₀ L e (apply.withHeader rq₀ hm) (by rw [hed]; exact hdec) hna]
          iframe HL Hσ Hh Hw'
          ipureintro
          exact hfacts
        imodintro
        iintro !>
        iunfold grantedRes
        ileft
        rw [Hag]
        iframe HQ
        ipureintro; exact hg
      · -- refused: the client's update is put back, nothing fires, the state kept
        icases Hucl with ⟨Habort, -⟩
        imod Habort $$ [Hc] with -
        · iunfold etcdKV; iexact Hc
        have hent : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L :=
          kvModelOn_snoc_refused γk st₀ L e (apply.withHeader rq₀ hm) het hdata (by rw [hed]; exact hdec) hna hkv hg
        imod Hclose $$ [HL Hσ Hh] with -
        · inext
          iexists L ++ [e]
          rw [hent]
          rw [admStates_snoc_noadmin γk st₀ L e (apply.withHeader rq₀ hm) (by rw [hed]; exact hdec) hna]
          iframe HL Hσ Hh Hw'
          ipureintro
          exact hfacts
        imodintro
        iintro !>
        iunfold grantedRes
        iright
        ipureintro; exact hg
  · -- an admin request: the KV state kept, the step determinate at the commit
    icases Had with (%Had | ⟨%Qh, %Had, #Hha⟩)
    · -- (C1's A3) an `Authenticate`: needing no admin permission, out of the history
      obtain ⟨hadm, -, hna0, hQr⟩ := Had
      subst hQr
      imodintro
      unfold srvPropAu1
      iauintro
      unfold atomic_acc
      iunfold kvInvOn at Hinv
      iinv Hinv with >Hi Hclose
      icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
      isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
      iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
      iintro Hmask
      iexists L
      iframe HL
      isplit
      · iintro HL
        imod Hmask with -
        imod Hclose $$ [HL Hσ Hh] with -
        · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
        imodintro
        itrivial
      · iintro %e ⟨%He, HL⟩
        imod Hmask with -
        obtain ⟨het, hed, hidx⟩ := He
        have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.2.1 hidx (Or.inl het)
        have hdata : e.data ≠ [] := by rw [hed]; exact hd
        have hidxe : uint.Z γk.c0 < uint.Z e.index := by
          have := Hok.2.2.2.1
          omega
        have hent : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
          cases hna : apply.needAdminPermission (apply.withHeader rq₀ hm)
          · -- (C1's A3) an `Authenticate`: no admin step, no write
            have hw : ¬ writeKind (apply.dispatchKind (apply.withHeader rq₀ hm)) := by
              have hk := hadm.1
              unfold apply.adminKindOk at hk
              split at hk <;> simp_all [writeKind]
            exact kvModelOn_snoc_nonwrite γk st₀ L e (apply.withHeader rq₀ hm) (by rw [hed]; exact hdec) hna hw
          · exact kvModelOn_snoc_admin γk st₀ L e (apply.withHeader rq₀ hm) het hdata (by rw [hed]; exact hdec) hidxe hna
        have hshe : entryShapeOn e :=
          ⟨fun _ => Or.inr ⟨(apply.withHeader rq₀ hm), by rw [hed]; exact hdec, ⟨id, hid⟩, Or.inr hadm.1⟩,
            fun h => absurd het h⟩
        ihave #Hw' := kvWorkOn_snoc γ.raft γk L e hshe (fun h => absurd het h)
          $$ Hw (Hecl $$ %e %hed)
        have hc := commitOkOn_admin γk.c0 γk.ch0 st₀ γk.log0 L e d (apply.withHeader rq₀ hm) hed hdec hadm
        imod Hclose $$ [HL Hσ Hh] with -
        · inext
          iexists L ++ [e]
          rw [hent, admStates_snoc_noadmin γk st₀ L e (apply.withHeader rq₀ hm)
            (by rw [hed]; exact hdec) hna0]
          iframe HL Hσ Hh Hw'
          ipureintro
          exact kvInvOn_facts_snoc γ γk st₀ L e Hok hidx' hc
        imodintro
        iintro !>
        iunfold adminPropRes
        ipureintro
        have hs := rolesSorted_kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L hadm.2.2.2
        exact ⟨hs, authDet_of_sorted (apply.withHeader rq₀ hm) _ hs hadm.2.2.1⟩
    · -- (5b) needing the admin permission: recorded in the history, its client's update fires
      obtain ⟨hadm, -, hna0, hQr⟩ := Had
      subst hQr
      imodintro
      unfold srvPropAu1
      iauintro
      unfold atomic_acc
      iunfold kvInvOn at Hinv
      iinv Hinv with >Hi Hclose
      icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
      isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
      iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
      iintro Hmask
      iexists L
      iframe HL
      isplit
      · iintro HL
        imod Hmask with -
        imod Hclose $$ [HL Hσ Hh] with -
        · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
        imodintro
        itrivial
      · iintro %e ⟨%He, HL⟩
        imod Hmask with -
        obtain ⟨het, hed, hidx⟩ := He
        have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.2.1 hidx (Or.inl het)
        have hdata : e.data ≠ [] := by rw [hed]; exact hd
        have hidxe : uint.Z γk.c0 < uint.Z e.index := by
          have := Hok.2.2.2.1
          omega
        have hent : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L := by
          cases hna : apply.needAdminPermission (apply.withHeader rq₀ hm)
          · -- (C1's A3) an `Authenticate`: no admin step, no write
            have hw : ¬ writeKind (apply.dispatchKind (apply.withHeader rq₀ hm)) := by
              have hk := hadm.1
              unfold apply.adminKindOk at hk
              split at hk <;> simp_all [writeKind]
            exact kvModelOn_snoc_nonwrite γk st₀ L e (apply.withHeader rq₀ hm) (by rw [hed]; exact hdec) hna hw
          · exact kvModelOn_snoc_admin γk st₀ L e (apply.withHeader rq₀ hm) het hdata (by rw [hed]; exact hdec) hidxe hna
        have hshe : entryShapeOn e :=
          ⟨fun _ => Or.inr ⟨(apply.withHeader rq₀ hm), by rw [hed]; exact hdec, ⟨id, hid⟩, Or.inr hadm.1⟩,
            fun h => absurd het h⟩
        ihave #Hw' := kvWorkOn_snoc γ.raft γk L e hshe (fun h => absurd het h)
          $$ Hw (Hecl $$ %e %hed)
        have hc := commitOkOn_admin γk.c0 γk.ch0 st₀ γk.log0 L e d (apply.withHeader rq₀ hm) hed hdec hadm
        have hdec' : apply.irrDecode e.data = some (apply.withHeader rq₀ hm) := by
          rw [hed]; exact hdec
        have hsrt := rolesSorted_kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L hadm.2.2.2
        have hdet := authDet_of_sorted (apply.withHeader rq₀ hm) _ hsrt hadm.2.2.1
        have hfacts := kvInvOn_facts_snoc γ γk st₀ L e Hok hidx' hc
        by_cases hr : admRec γk st₀ (apply.withHeader rq₀ hm) L
        · -- recorded: the history grows by the state after the entry
          have hae := (admEntry_iff_admRec γk st₀ L e _ het hdata hdec' hidxe hna0).2 hr
          have hst := admStates_snoc_adm γk st₀ L e hae
          have hnext := srvAuthAtLog_snoc_adm γk st₀ L e _ het hdata hdec' hidxe hna0
          iunfold srvRLog at HL
          ihave #Hlbe := monoListLbOwn_get γ.raft.log _ (L ++ [e]) $$ HL
          ihave #HlbL := monoListLbOwn_le L (List.prefix_append L [e]) $$ Hlbe
          ihave #HhL := monoListLbOwn_get γk.hist _ (admStates γk st₀ L) $$ Hh
          iunfold histAu at Hha
          ihave Hacc := aupd_aacc $$ Hha
          unfold atomic_acc
          imod Hacc with Hacc
          isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
          icases Hacc with ⟨%hs, Hv, Hucl⟩
          iunfold authHistView at Hv
          imod authHist_halves_update γk _ _ [srvAuthAtLog γk st₀ (L ++ [e])] $$ Hh Hv
            with ⟨%Heq, Hh, Hv⟩
          subst Heq
          icases Hucl with ⟨-, Hcommit⟩
          isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
          imod Hcommit $$ [Hv] with #HQ
          · iexists hm, L, e
            iframe Hgb
            isplitr
            · iunfold srvReqLogLb; iexact HlbL
            isplitr
            · iunfold srvReqLogLb; iexact Hlbe
            rw [admStates_getLastD, ← hnext]
            iunfold authHistView
            iframe Hv
            ipureintro
            refine ⟨hdec', rfl, hr.1, hdet, ?_⟩
            rw [hst]
          imod Hclose $$ [HL Hσ Hh] with -
          · inext
            iexists L ++ [e]
            rw [hent, hst]
            iunfold srvRLog
            iframe HL Hσ Hh Hw'
            ipureintro
            exact hfacts
          imodintro
          iintro !>
          iunfold adminPropRes
          iunfold adminRecRes
          isplitr
          · ipureintro; exact ⟨hsrt, hdet⟩
          iunfold authHistLb
          iframe HhL
          ileft
          iframe HQ
          ipureintro; exact hr
        · -- not recorded: the auth state, and so the history, kept
          have hae : ¬ admEntry γk.c0 (srvAuthAtLog γk st₀ L) e := fun h =>
            hr ((admEntry_iff_admRec γk st₀ L e _ het hdata hdec' hidxe hna0).1 h)
          ihave #HhL := monoListLbOwn_get γk.hist _ (admStates γk st₀ L) $$ Hh
          imod Hclose $$ [HL Hσ Hh] with -
          · inext
            iexists L ++ [e]
            rw [hent, admStates_snoc_other γk st₀ L e hae]
            iframe HL Hσ Hh Hw'
            ipureintro
            exact hfacts
          imodintro
          iintro !>
          iunfold adminPropRes
          iunfold adminRecRes
          isplitr
          · ipureintro; exact ⟨hsrt, hdet⟩
          iunfold authHistLb
          iframe HhL
          iright
          ipureintro; exact hr

/-- **A result predicate of the mode-`on` model of the log is one the server's two logs agree on**
(2026-10-27; `kv_qinv`'s): the mode-`on` KV invariant keeps the start's consistent index at most
the start index (`kvRaftOfOn_eqv`), and so the auth history (`admStates_eqv`). -/
theorem kvOn_qinv (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Q : auth.AuthState × mvcc.Log → List auth.AuthState → IProp GF) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗
      srvQInv γ (fun L => Q (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L) (admStates γk st₀ L)) := by
  iintro #Hinv
  iunfold srvQInv
  iintro !> %A %B %Hab #HA
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
  imod Hclose $$ [HL Hσ Hh] with -
  · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
  imodintro
  inext
  rw [← kvRaftOfOn_eqv γ _ _ _ A B Hab Hok.2.2.2.1, ← admStates_eqv γ γk st₀ A B Hab Hok.2.2.2.1]
  iexact HA

/-- The result predicates `reqPropOkOn` admits are of the mode-`on` model of the log, so the two
logs agree on them (2026-10-27). -/
theorem reqPropOkOn_qinv (γ γl : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel) (hm : apply.HeaderModel)
    (Qr : List EntryModel → IProp GF) :
    reqPropOkOn (GF := GF) γl γk st₀ Gb rq₀ hm Qr ⊢
      reqPropOkOn γl γk st₀ Gb rq₀ hm Qr ∗ (kvInvOn γ γk st₀ -∗ srvQInv γ Qr) := by
  iintro Hok
  ihave %Hsh : ⌜∃ Q : auth.AuthState × mvcc.Log → List auth.AuthState → IProp GF,
      Qr = fun L => Q (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L) (admStates γk st₀ L)⌝ $$ [Hok]
  · iunfold reqPropOkOn at Hok
    icases Hok with (%Hno | ⟨%op, %Q, %γc, %L₀, %Hop, -⟩ | (%Had | ⟨%Qh, %Had, -⟩))
    · ipureintro; exact ⟨fun _ _ => iprop(True), Hno.2.2.2.2.2⟩
    · ipureintro
      refine ⟨fun x _ => iprop((⌜kvGranted x.1 (apply.withHeader rq₀ hm)⌝ ∗
        kvRes γc Q (kvStateOf x.2)) ∨ ⌜¬ kvGranted x.1 (apply.withHeader rq₀ hm)⌝), ?_⟩
      rw [Hop.2.2.2.2.2]; rfl
    · ipureintro
      refine ⟨fun x _ => iprop(⌜rolesSorted x.1 ∧ authDet (apply.withHeader rq₀ hm) x.1⌝), ?_⟩
      rw [Had.2.2.2]; rfl
    · ipureintro
      refine ⟨fun x hs => iprop(⌜rolesSorted x.1 ∧ authDet (apply.withHeader rq₀ hm) x.1⌝ ∗
        authHistLb γk hs ∗ ((⌜auth.adminOk x.1 (some (auth.authInfoM (apply.principalOf (apply.withHeader rq₀ hm)))) ∧
            adminNext (apply.withHeader rq₀ hm) x.1 ≠ x.1⌝ ∗ □ Qh hs) ∨
          ⌜¬ (auth.adminOk x.1 (some (auth.authInfoM (apply.principalOf (apply.withHeader rq₀ hm)))) ∧
            adminNext (apply.withHeader rq₀ hm) x.1 ≠ x.1)⌝)), ?_⟩
      rw [Had.2.2.2]; rfl
  obtain ⟨Q, rfl⟩ := Hsh
  iframe Hok
  iintro #Hinv
  iapply kvOn_qinv γ γk st₀ Q $$ Hinv

end lemmas

end EtcdGrove
end Perennial
