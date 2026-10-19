/-
**The top-level KV specs of etcd's server, over the state machine** (2026-10-19; `notes/decisions.md`,
"The KV specs over a state machine (D22)"). Lean-first (no Rocq counterpart).

Each spec is a triple of one of `EtcdServer`'s KV methods (`Put`, ...) stated in the state
machine's terms only (`StateMachine.lean`, written to be audited by etcd's experts):

* **etcd's state is one ghost variable** holding the whole multi-revision store
  (`etcdState γ σ`, `σ : EtcdSM.State`): the server's invariants own one half (the KV invariant,
  `kvInv`: the state of raft's committed log), the client the other, to hand over at the
  linearization point.
* **A request takes effect atomically on the whole state**: the precondition has the client's
  persistent atomic update `etcdAU γ (EtcdSM.putNext req) Q` (persistent: etcd may apply a write
  after the call returned an error, or twice, `kvAu`'s docstring); a success returns `□ Q σ` at the
  state `σ` the request took effect on, and the response the state machine gives for `σ`.
* **The server is one handle** (`ownEtcdServer s γ`, given back): the server's persistent views
  and one request's reader slots of its `RWMutex`es (`srvCallSlot`: the server's, the store's, the
  logger's, the read loop's, the auth store's). The slots are bounded (`NewServer` hands out
  `srvServeBuilt`'s), hence a handle per call rather than a persistent predicate: a pool of slots
  paid for by thread tokens needs the slots taken at the `RLock` steps themselves (a slot is not
  timeless: an invariant holding them could not give one up before the call), a change of the
  request path's internal specs (`notes/decisions.md`, D22).
* **What the server's internals use and the specs leave out**: the apply thread's environment
  (`apply.AEnv`), the request names, mvcc's log and its certificates (`idxCert`, `certOk`), the
  revision tokens, the id credit (`idCred`, now the premise `receiptBound GF ≤ 2 ^ 48`, D19b).

The proofs instantiate the server's linked specs (`EtcdServer.wp_Put`, ...) and translate, through
`StateMachineRefinement.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StateMachineRefinement

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-! ## Pure: what an applied put checked -/

/-- A put applied with no error through any chain passed the backend's key check (the key
exists if the put keeps its value or lease). -/
theorem chainStep_put_check (op : OpFull) (rq : apply.IRRModel)
    (hk : apply.dispatchKind rq = .put) (hop : rq.put = some op) (log l : mvcc.Log) :
    ∀ c : apply.Chain, apply.chainStep apply.backendStep c rq log (.applied l false) →
      (txn.needsPrev op = true → (mvcc.findKey op.key (mvcc.stateAfter log)).isSome)
  | .backend, h => by
    simp only [apply.chainStep, apply.backendStep, hk] at h
    obtain ⟨op', hop', h⟩ := h
    rw [hop] at hop'; cases hop'
    rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hc, -⟩
    · cases h
    · cases h
    · exact hc
  | .corrupt c, h => by
    simp only [apply.chainStep, hk, apply.corruptRejects, ↓reduceIte] at h
    cases h
  | .capped c, h => by
    simp only [apply.chainStep, hk, apply.cappedRejects, ↓reduceIte] at h
    cases h
  | .auth _ c, h => by
    unfold apply.chainStep at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · cases h
      · exact chainStep_put_check op rq hk hop log l c h
    · exact chainStep_put_check op rq hk hop log l c h
  | .quota c, h => by
    unfold apply.chainStep at h
    exact chainStep_put_check op rq hk hop log l c h

/-- **An applied put passed its key check** at the log it met. -/
theorem put_applied_check (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (l : mvcc.Log) (skip : Bool)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    txn.needsPrev o = true → (mvcc.findKey o.key (mvcc.stateAfter x.log)).isSome := by
  obtain ⟨-, hd, -, -⟩ := h
  have hk : apply.dispatchKind (apply.withHeader (irrPut o) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  have hop : (apply.withHeader (irrPut o) hm).put = some o := by
    simp [apply.withHeader, irrPut, apply.irrEmpty]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, false_or, ↓reduceIte] at hd
  exact chainStep_put_check o _ hk hop x.log l x.chain hd

/-! ## The vocabulary of the specs -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **One request's reader slots** of the server's `RWMutex`es: `leadTimeMu`'s, the store's,
`lgMu`'s, the read loop's, the auth store's (with the backend's read resource, `E.RD`). -/
def srvCallSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ srvReadReader s γr ∗
    E.RD)

/-- **A handle on the etcd server `s`**, whose KV state's ghost names are `γ` (not persistent:
one request's reader slots; see the file header): the server as its proposers and readers see
it (`isServerReq`, `isServerRead`) at some apply environment and request names. -/
def ownEtcdServer (s : Loc) (γ : KVNames) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (ρ : ReqNames), ⌜ρ.kv = γ⌝ ∗ isServerReq s E ρ ∗
    isServerRead s E ρ.rd ∗ srvCallSlot s E ρ.rd)

/-- **etcd's KV state is `σ`** (the client's half of the state's ghost variable). -/
abbrev etcdState (γ : KVNames) (σ : EtcdSM.State) : IProp GF := etcdKV γ σ

/-- **A client's atomic update of etcd's state by `f`** (persistent): fired at the state `σ` the
request takes effect on, the state stepped to `f σ`, with the client's `□ Q σ`. -/
abbrev etcdAU (γ : KVNames) (f : EtcdSM.State → EtcdSM.State) (Q : EtcdSM.State → IProp GF) :
    IProp GF :=
  kvAu γ f Q

/-- **The `*pb.PutRequest` `r` is the request `req`** (read-only). -/
def kvPutRequestIs (r : Loc) (req : EtcdSM.PutRequest) : IProp GF :=
  txn.putRequestIs r
    (txn.putOpOf req.key req.value req.lease req.prevKv req.ignoreValue req.ignoreLease)

/-- **The `*pb.PutResponse` `resp` is the response `res`**: its header's revision and previous
key-value (read-only), the header's other fields owned (for the gRPC layer to fill), a revision
of a store that has one and room for one more. -/
def kvPutResponseIs (resp : Loc) (res : EtcdSM.PutResponse) : IProp GF :=
  iprop(txn.putResponseIs resp (W64 (res.revision : Int)) res.prevKv ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
    ⌜2 ≤ res.revision ∧ res.revision + 4 ≤ 2 ^ 63⌝)

/-- **The `*pb.DeleteRangeRequest` `r` is the request `req`** (read-only). -/
def kvDeleteRangeRequestIs (r : Loc) (req : EtcdSM.DeleteRangeRequest) : IProp GF :=
  txn.deleteRangeRequestIs r (txn.deleteOpOf req.key req.rangeEnd req.prevKv)

/-- **The `*pb.DeleteRangeResponse` `resp` is the response `res`** (as `kvPutResponseIs`). -/
def kvDeleteRangeResponseIs (resp : Loc) (res : EtcdSM.DeleteRangeResponse) : IProp GF :=
  iprop(txn.deleteRangeResponseIs resp (W64 (res.revision : Int)) res.deleted res.prevKvs ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
    ⌜1 ≤ res.revision ∧ res.revision + 3 ≤ 2 ^ 63⌝)

/-- **The `*pb.RangeRequest` `r` is the request `req`** (read-only). -/
def kvRangeRequestIs (r : Loc) (req : EtcdSM.RangeRequest) : IProp GF :=
  iprop(∃ o : OpFull, txn.rangeRequestIs r o ∗ ⌜rangeReqOf o = req⌝)

/-- **The `*pb.RangeResponse` `resp` is the response `res`**: its header's revision, key-values,
`more` and count (read-only), the header's other fields owned. -/
def kvRangeResponseIs (resp : Loc) (res : EtcdSM.RangeResponse) : IProp GF :=
  iprop(txn.rangeResponseIs resp (W64 (res.revision : Int)) res.kvs res.more
      (W64 (res.count : Int)) ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp) ∗
    ⌜1 ≤ res.revision ∧ res.revision + 4 ≤ 2 ^ 63⌝)

end defs

/-! ## The handles, from the server's construction -/

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`N` handles on the server** from its views (`Start`'s, `start_gives_views`), `N` of each of
the reader slots `NewServer` hands out (`srvServeBuilt`'s: `64` of each) and `N` of the read
loop's (`Start`'s). -/
theorem ownEtcdServer_of_slots (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (N : Nat) :
    ∀ K M : Nat, N ≤ K → N ≤ M →
    isServerReq s E ρ ∗ isServerRead s E ρ.rd ∗
        ([∗list] _x ∈ List.replicate K (), srvLeadTimeReader (GF := GF) s) ∗
        ([∗list] _x ∈ List.replicate K (), srvLgReader s) ∗
        ([∗list] _x ∈ List.replicate K (), E.RD) ∗
        ([∗list] _x ∈ List.replicate K (), mvcc.storeReader E.s E.γ) ∗
        ([∗list] _x ∈ List.replicate M (), srvReadReader s ρ.rd) ⊢
      [∗list] _x ∈ List.replicate N (), ownEtcdServer s ρ.kv := by
  induction N with
  | zero =>
    intro K M _ _
    iintro -
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ n ih =>
    intro K M hK hM
    iintro ⟨#Hreq, #Hrd, Hlt, Hlg, HRD, Hst, Hrr⟩
    icases replicate_take1 _ _ (by omega) $$ Hlt with ⟨Hlt1, Hlt⟩
    icases replicate_take1 _ _ (by omega) $$ Hlg with ⟨Hlg1, Hlg⟩
    icases replicate_take1 _ _ (by omega) $$ HRD with ⟨HRD1, HRD⟩
    icases replicate_take1 _ _ (by omega) $$ Hst with ⟨Hst1, Hst⟩
    icases replicate_take1 _ _ (by omega) $$ Hrr with ⟨Hrr1, Hrr⟩
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hlt1 Hlg1 HRD1 Hst1 Hrr1]
    · iunfold ownEtcdServer
      iexists E, ρ
      iframe #
      isplitr
      · ipureintro; rfl
      iunfold srvCallSlot
      iframe
    · iapply (ih (K - 1) (M - 1) (by omega) (by omega))
      iframe #
      iframe Hlt Hlg HRD Hst Hrr

end alloc

/-! ## Put -/

section put
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Put(ctx, r)`, over the state machine**: for a put request `req` with no lease and the
client's update by the put's step: success, the client's `□ Q σ` at the state `σ` the put took
effect on and the state machine's response there (`EtcdSM.put`, which succeeds: the key check
passed); or an error (`applyErrIs`: one `errors.Is` can take), and the put may still take effect
(`etcdAU` is persistent). -/
def EtcdServer.Put.kvSpec : Prop :=
  ∀ (s : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc)
    (req : EtcdSM.PutRequest) (Q : EtcdSM.State → IProp GF),
  receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ownEtcdServer s γ ∗ context.isContext ctx cd ∗ kvPutRequestIs r req ∗
      ⌜req.lease = W64 0⌝ ∗ etcdAU γ (EtcdSM.putNext req) Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ownEtcdServer s γ ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (σ : EtcdSM.State) (res : EtcdSM.PutResponse),
          ⌜EtcdSM.put req σ = .ok (EtcdSM.putNext req σ, res)⌝ ∗ □ Q σ ∗
          kvPutResponseIs resp res) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

theorem kvPutRequest_op (req : EtcdSM.PutRequest) :
    putReqOf (txn.putOpOf req.key req.value req.lease req.prevKv req.ignoreValue req.ignoreLease) =
      req := by
  cases req; rfl

/-- **`EtcdServer.Put.kvSpec`**, from the linked `EtcdServer.wp_Put`. -/
theorem EtcdServer.wp_Put_kv : EtcdServer.Put.kvSpec (GF := GF) (hG := hG) := by
  intro s γ ctx cd r req Q hR
  iintro %Φ ⟨#Hpkg, Hown, #Hctx, Hreq, %Hlease, #Hau⟩ HΦ
  iunfold ownEtcdServer at Hown
  icases Hown with ⟨%E, %ρ, %Hρ, #Hsrv, #Hrd, Hslot⟩
  iunfold srvCallSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrr, HRD⟩
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #Hcert
  have hop := kvPutRequest_op req
  iunfold kvPutRequestIs at Hreq
  iapply (EtcdServer.wp_Put s E ρ ctx cd r
    (txn.putOpOf req.key req.value req.lease req.prevKv req.ignoreValue req.ignoreLease) Q [])
    $$ [Hlt HRD Hreq]
  · iframe #
    iframe Hlt HRD Hreq
    isplitr
    · iunfold idCred; ipureintro; exact hR
    iunfold putPermit
    isplitr
    · ipureintro; exact Hlease
    iunfold kvOpAu
    rw [← putNext_eq, hop, Hρ]
    iexact Hau
  inext
  iintro %resp %err ⟨Hlt, HRD, Hout⟩
  iapply HΦ
  isplitl [Hlt HRD Hsr Hlg Hrr]
  · iunfold ownEtcdServer
    iexists E, ρ
    iframe #
    isplitr
    · ipureintro; exact Hρ
    iunfold srvCallSlot
    iframe
  icases Hout with (⟨%Herr, %hm, %x, %x', %o, %skip, %Hstep, Hans, Hhdr, -, -, -, -, #HQ⟩ |
    ⟨⟨%Hnull, %Herr⟩, #Herr', -⟩)
  · ileft
    obtain ⟨hstep, ⟨l', ho⟩, -⟩ := Hstep
    subst ho
    simp only [apply.putOutcomeIs]
    icases Hans with ⟨#Hpr, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hho, %Hb⟩
    have hne : x.log ≠ [] := by intro h; rw [h] at Hb; simp at Hb
    have hchk := put_applied_check _ hm x x' l' skip hstep
    have hok := put_ok (txn.putOpOf req.key req.value req.lease req.prevKv req.ignoreValue
      req.ignoreLease) (kvStateOf x.log) (by rw [kvStateOf_kvs]; exact hchk)
    rw [hop] at hok
    isplitr
    · ipureintro; exact Herr
    iexists kvStateOf x.log
    iexists (⟨(kvStateOf x.log).rev + 1,
      if (txn.putOpOf req.key req.value req.lease req.prevKv req.ignoreValue req.ignoreLease).base.prevKV
      then mvcc.findKey (txn.putOpOf req.key req.value req.lease req.prevKv req.ignoreValue
        req.ignoreLease).key (kvStateOf x.log).kvs else none⟩ : EtcdSM.PutResponse)
    isplitr
    · ipureintro
      rw [hok, ← hop, putNext_eq]
      rfl
    iframe HQ
    iunfold kvPutResponseIs
    rw [kvStateOf_rev_succ x.log hne, kvStateOf_kvs]
    iframe Hho
    isplitl
    · iexact Hpr
    · ipureintro; omega
  · iright
    iframe Herr'
    ipureintro; exact Herr

end put

/-! ## DeleteRange -/

section delete
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.DeleteRange(ctx, r)`, over the state machine** (as `EtcdServer.Put.kvSpec`): for a
delete request whose range end is not `"\x00"` (the server's encoding of the request in raft's log
loses that range end, `deletePermit`), success, the client's `□ Q σ` at the state `σ` the delete
took effect on and the state machine's response there; or an error. -/
def EtcdServer.DeleteRange.kvSpec : Prop :=
  ∀ (s : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc)
    (req : EtcdSM.DeleteRangeRequest) (Q : EtcdSM.State → IProp GF),
  receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ownEtcdServer s γ ∗ context.isContext ctx cd ∗ kvDeleteRangeRequestIs r req ∗
      ⌜req.rangeEnd ≠ [W8 0]⌝ ∗ etcdAU γ (EtcdSM.deleteRangeNext req) Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ownEtcdServer s γ ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (σ : EtcdSM.State) (res : EtcdSM.DeleteRangeResponse),
          ⌜EtcdSM.deleteRange req σ = (EtcdSM.deleteRangeNext req σ, res)⌝ ∗ □ Q σ ∗
          kvDeleteRangeResponseIs resp res) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

theorem kvDeleteRangeRequest_op (req : EtcdSM.DeleteRangeRequest) :
    deleteRangeReqOf (txn.deleteOpOf req.key req.rangeEnd req.prevKv) = req := by
  cases req; rfl

/-- **`EtcdServer.DeleteRange.kvSpec`**, from the linked `EtcdServer.wp_DeleteRange`. -/
theorem EtcdServer.wp_DeleteRange_kv : EtcdServer.DeleteRange.kvSpec (GF := GF) (hG := hG) := by
  intro s γ ctx cd r req Q hR
  iintro %Φ ⟨#Hpkg, Hown, #Hctx, Hreq, %Hend, #Hau⟩ HΦ
  iunfold ownEtcdServer at Hown
  icases Hown with ⟨%E, %ρ, %Hρ, #Hsrv, #Hrd, Hslot⟩
  iunfold srvCallSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrr, HRD⟩
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #Hcert
  have hop := kvDeleteRangeRequest_op req
  iunfold kvDeleteRangeRequestIs at Hreq
  iapply (EtcdServer.wp_DeleteRange s E ρ ctx cd r
    (txn.deleteOpOf req.key req.rangeEnd req.prevKv) Q []) $$ [Hlt HRD Hreq]
  · iframe #
    iframe Hlt HRD Hreq
    isplitr
    · iunfold idCred; ipureintro; exact hR
    iunfold deletePermit
    isplitr
    · ipureintro; simpa [txn.deleteOpOf] using Hend
    iunfold kvOpAu
    rw [← deleteRangeNext_eq, hop, Hρ]
    iexact Hau
  inext
  iintro %resp %err ⟨Hlt, HRD, Hout⟩
  iapply HΦ
  isplitl [Hlt HRD Hsr Hlg Hrr]
  · iunfold ownEtcdServer
    iexists E, ρ
    iframe #
    isplitr
    · ipureintro; exact Hρ
    iunfold srvCallSlot
    iframe
  icases Hout with (⟨%Herr, %hm, %rq', %op', %x, %x', %o, %skip, %Hstep, Hans, Hhdr, -, -, -, -,
    #HQ⟩ | ⟨⟨%Hnull, %Herr⟩, #Herr', -⟩)
  · ileft
    obtain ⟨-, -, hz, -, ⟨l', ho⟩, -⟩ := Hstep
    subst ho
    have hnz : irrNoZeroEnd (irrDeleteRange (txn.deleteOpOf req.key req.rangeEnd req.prevKv)) := by
      refine ⟨fun o' h => by simp [irrDeleteRange, apply.irrEmpty] at h, fun o' h => ?_,
        fun t h => by simp [irrDeleteRange, apply.irrEmpty] at h⟩
      simp only [irrDeleteRange, Option.some.injEq] at h
      subst h
      simpa [txn.deleteOpOf] using Hend
    have hop' := hz hnz
    subst hop'
    simp only [apply.deleteOutcomeIs]
    icases Hans with ⟨#Hdr, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hho, %Hb⟩
    have hne : x.log ≠ [] := by intro h; rw [h] at Hb; simp at Hb
    have hres := deleteRange_resp (txn.deleteOpOf req.key req.rangeEnd req.prevKv)
      (kvStateOf x.log) (kvStateOf_revs_ne_nil _ hne)
    rw [hop] at hres
    isplitr
    · ipureintro; exact Herr
    iexists kvStateOf x.log
    iexists _
    isplitr
    · ipureintro
      rw [hres, ← hop, deleteRangeNext_eq, hop]
    iframe HQ
    iunfold kvDeleteRangeResponseIs
    simp only [kvStateOf_kvs]
    have hrev : W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log)
        (txn.deleteOpOf req.key req.rangeEnd req.prevKv)) : Nat) : Int) =
        W64 (((if txn.delChanges (mvcc.stateAfter x.log)
          (txn.deleteOpOf req.key req.rangeEnd req.prevKv) = [] then (kvStateOf x.log).rev
          else (kvStateOf x.log).rev + 1 : Nat)) : Int) := by
      unfold mvcc.writeRev
      rw [kvStateOf_rev]
      split <;> (congr 2 <;> omega)
    rw [← hrev]
    iframe Hho
    isplitl
    · iexact Hdr
    · ipureintro
      rw [kvStateOf_rev]
      split <;> omega
  · iright
    iframe Herr'
    ipureintro; exact Herr

end delete

/-! ## Range -/

section range
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`s.Range(ctx, r)`, over the state machine**: for a linearizable range (not serializable:
a serializable range reads the member's own store, at no point of the client's update, a
follow-up) whose sort target is one of the protobuf's (the server panics on another; the gRPC
layer rejects it), from a context carrying no trace: success, the client's `□ Q σ` at the state
`σ` the range read and a response the state machine allows there (`EtcdSM.RangeOk`); or an
error. -/
def EtcdServer.Range.kvSpec : Prop :=
  ∀ (s : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc)
    (req : EtcdSM.RangeRequest) (Q : EtcdSM.State → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ownEtcdServer s γ ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx none ∗
      kvRangeRequestIs r req ∗
      ⌜req.serializable = false ∧ 0 ≤ sint.Z req.sortTarget ∧ sint.Z req.sortTarget ≤ 4⌝ ∗
      etcdAU γ (fun σ => σ) Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ownEtcdServer s γ ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (σ : EtcdSM.State) (res : EtcdSM.RangeResponse),
          ⌜EtcdSM.RangeOk req σ (.ok res)⌝ ∗ □ Q σ ∗ kvRangeResponseIs resp res) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

/-- `sint.nat` of a log's last revision. -/
theorem sint_nat_last (l : mvcc.Log) (h1 : 1 ≤ l.length) (h2 : l.length < 2 ^ 63) :
    sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
  unfold sint.nat; word

/-- **The state machine's range at the state of a log is the server's** (`txn.rangeResult`'s
answer). -/
theorem rangeOk_of_result (o : OpFull) (hset : SortSetOk o) (l : mvcc.Log) (kvs : List EtcdKv)
    (more : Bool) (h2 : 2 ≤ l.length) (h3 : l.length + 3 ≤ 2 ^ 63)
    (hrev : sint.Z o.base.rev ≤ sint.Z (W64 ((l.length : Int) - 1)))
    (hsel : txn.srvRangeOk o (mvcc.stateAt l (sint.nat (mvcc.rangeRev (W64 ((l.length : Int) - 1))
      o.base.rev))) kvs more) :
    EtcdSM.RangeOk (rangeReqOf o) (kvStateOf l)
      (.ok ⟨(kvStateOf l).rev, kvs, more,
        ((mvcc.stateAt l (sint.nat (mvcc.rangeRev (W64 ((l.length : Int) - 1))
          o.base.rev))).filter (fun v => EtcdSM.inRange o.key o.base.rangeEnd v.key)).length⟩) := by
  have hl1 : sint.Z (W64 ((l.length : Int) - 1)) = (l.length : Int) - 1 := by word
  rw [hl1] at hrev
  unfold EtcdSM.RangeOk EtcdSM.readRevision
  simp only [kvStateOf_rev, rangeReqOf]
  have hnf : ¬ (((l.length - 1 : Nat) : Int) < sint.Z o.base.rev) := by omega
  simp only [hnf, ↓reduceIte]
  -- the revision read
  obtain ⟨r, hr, hrl⟩ : ∃ r : Nat, sint.nat (mvcc.rangeRev (W64 ((l.length : Int) - 1)) o.base.rev) = r ∧
      r < l.length ∧ (if sint.Z o.base.rev ≤ 0 then (Except.ok (l.length - 1) : Except EtcdSM.Error Nat)
        else .ok (sint.Z o.base.rev).toNat) = .ok r := by
    unfold mvcc.rangeRev
    by_cases h0 : sint.Z o.base.rev ≤ 0
    · refine ⟨l.length - 1, ?_, by omega, by simp [h0]⟩
      simp only [h0, ↓reduceIte]
      exact sint_nat_last l (by omega) (by omega)
    · refine ⟨(sint.Z o.base.rev).toNat, ?_, by omega, by simp [h0]⟩
      simp only [h0, ↓reduceIte]
  obtain ⟨hrl, hok⟩ := hrl
  rw [hok]
  simp only
  rw [hr] at hsel ⊢
  refine ⟨_, rfl, by simp, ?_, ?_⟩
  · rw [kvStateOf_at l hrl]
    exact (rangeKvsOk_iff o hset _ kvs more).2 hsel
  · rw [kvStateOf_at l hrl]
    rfl

/-- The sort facts a `*pb.RangeRequest` gives of the range it denotes. -/
theorem rangeRequestIs_sortSet (r : Loc) (o : OpFull) :
    txn.rangeRequestIs (GF := GF) r o ⊢ ⌜SortSetOk o⌝ := by
  iintro #H
  iunfold txn.rangeRequestIs at H
  icases H with ⟨-, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM,
    %minC, %maxC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %Ho, -⟩
  ipureintro
  rw [Ho]
  exact rangeOpOf_sortSetOk _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **`EtcdServer.Range.kvSpec`**, from the linked `EtcdServer.wp_Range`. -/
theorem EtcdServer.wp_Range_kv : EtcdServer.Range.kvSpec (GF := GF) (hG := hG) := by
  intro s γ ctx cd r req Q
  iintro %Φ ⟨#Hpkg, Hown, #Hctx, #Htr, Hreq, %Hp, #Hau⟩ HΦ
  obtain ⟨hser, ht0, ht4⟩ := Hp
  iunfold ownEtcdServer at Hown
  icases Hown with ⟨%E, %ρ, %Hρ, #Hsrv, #Hrd, Hslot⟩
  iunfold srvCallSlot at Hslot
  icases Hslot with ⟨Hlt, Hsr, Hlg, Hrr, HRD⟩
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #Hcert
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #Hc0
  iunfold kvRangeRequestIs at Hreq
  icases Hreq with ⟨%o, #Hreq, %Ho⟩
  ihave %Hset := rangeRequestIs_sortSet r o $$ Hreq
  subst Ho
  iapply (EtcdServer.wp_Range s E ρ ρ.rd (W64 0) ctx cd r o none true
    (fun L => iprop(□ Q (kvStateOf (kvModel ρ.rd.kv L)))) []) $$ [Hsr Hlg Hrr HRD]
  · iframe #
    isplitl
    · iunfold srvRdCall
      iframe Hsr Hlg Hrr HRD
      iunfold committedAtLeast
      rw [show uint.nat (W64 0) = 0 from rfl]
      iexact Hc0
    isplitr
    · iunfold traceutil.ownTraceOpt; itrivial
    isplitr
    · ipureintro; exact ⟨ht0, ht4⟩
    iunfold kvDep
    ileft
    iexists Q
    isplitr
    · ipureintro; rfl
    iunfold kvReadAu
    rw [show ρ.rd.kv = γ from Hρ]
    iexact Hau
  inext
  iintro %resp %err ⟨Hcall, Hout⟩
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hsr, Hlg, -, Hrr, HRD⟩
  iapply HΦ
  isplitl [Hlt HRD Hsr Hlg Hrr]
  · iunfold ownEtcdServer
    iexists E, ρ
    iframe #
    isplitr
    · ipureintro; exact Hρ
    iunfold srvCallSlot
    iframe
  icases Hout with (⟨⟨%Herr, %Hnn⟩, Hok⟩ | ⟨⟨%Hnull, %Herr⟩, #Herr'⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    iunfold rangeReadOk at Hok
    have hs : (o.base.serializable = true) = False := by
      simp only [rangeReqOf] at hser; simp [hser]
    simp only [rangeReqOf] at hser
    simp only [hser, Bool.false_eq_true, ↓reduceIte]
    icases Hok with ⟨%l, -, -, %Hl, -, ⟨%L, -, %HL, #HQ⟩, #Hres, Hho⟩
    obtain ⟨h2, h3, -⟩ := Hl
    iunfold txn.rangeResult at Hres
    icases Hres with (⟨⟨-, %Hn⟩, -⟩ | ⟨⟨-, -, -, %Hn⟩, -⟩ | ⟨⟨%Hrev, -⟩, %kvs, %more, #Hrr, %Hsel⟩)
    · exact absurd Hn Hnn
    · exact absurd Hn Hnn
    iexists kvStateOf l
    iexists (⟨(kvStateOf l).rev, kvs, more,
      ((mvcc.stateAt l (sint.nat (mvcc.rangeRev (W64 ((l.length : Int) - 1))
        o.base.rev))).filter (fun v => EtcdSM.inRange o.key o.base.rangeEnd v.key)).length⟩ :
      EtcdSM.RangeResponse)
    isplitr
    · ipureintro
      exact rangeOk_of_result o Hset l kvs more h2 h3 Hrev Hsel
    isplitr
    · rw [← HL]; iexact HQ
    iunfold kvRangeResponseIs
    have hrv : W64 (((kvStateOf l).rev : Nat) : Int) = W64 ((l.length : Int) - 1) := by
      rw [kvStateOf_rev]; congr 1; omega
    have hc := range_count_eq o (mvcc.stateAt l (sint.nat (mvcc.rangeRev
      (W64 ((l.length : Int) - 1)) o.base.rev)))
    simp only [EtcdSM.KVMap.range, rangeReqOf] at hc
    dsimp only
    rw [hrv, ← hc]
    iframe Hho
    isplitl
    · iexact Hrr
    · ipureintro; rw [kvStateOf_rev]; omega
  · iright
    iframe Herr'
    ipureintro; exact Herr

end range

end EtcdGrove
end Perennial
