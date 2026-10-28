/-
**An admin entry's application by the apply thread, with auth on** (the auth plan's E3n,
2026-10-27). Lean-first (no Rocq counterpart).

`apply.Apply(lg, e, uberApply, w, v3)` on an admitted admin request (`adminKindOk`), from the
apply thread's resources in the mode `on γa`: its auth row at the server's hook (`authApplyResB`:
the authority with its fuel and tie at a history `hs` whose latest state is the model's `st`, the
write token, the provider's admin share, the write contract at every schema auth backend on `bel`,
the store's admin steps at `adminW`), the rest resource lending the store's half of `be`
(`roLendsAuthBe`, E3n), the uber-applier's latest-state admin triples (`uberAuthStepsL`,
`srv_uberAuthStepsL_on`) and one time receipt (the admin step's cost, E2l). The half of `be` is
borrowed from the rest for the call (blocker 1's row: `adminW_of_beOn`, `beOn_of_adminW`), the
latest-state resource lent by the authority (`ownFuT_lend`), and `apply.Apply.adminSpecL`'s outcome
read as the model's admin step (`adminOut_model`): the row comes back at the history after it,
whose latest state `st'` is a successor of the model's (`adminStateR rq st st'`), the rest at the
same value, the KV log and chain kept (`applyStep_admin_keep`).

E3o: any `v3` (a replayed entry, `v3` false, changes nothing: the authority comes back at the same
history), and with `v3` the result `nil` or its error not `ErrNoSpace`'s
(`applyResultIs_notNoSpaceAdmin`, read off the admin outcome before it is consumed), for
`applyEntryNormal`'s NOSPACE branch.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadAdminOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **An `Authenticate` entry's response** (C1's A2, 2026-10-28): unless the entry is not an
`Authenticate` or was not dispatched, the result at `ar` holds the response (`Resp`, a pointer to
an `AuthenticateResponse`) and its error, and the response is what the store returned
(`apply.authnOut`: an error and no response, or a token issued to the request's user). -/
def adminAuthnAr (γa : auth.AuthNames) (ar : Loc) (rq : apply.IRRModel) (out : apply.ApplyOut) :
    IProp GF :=
  iprop(⌜apply.dispatchKind rq ≠ .authenticate ∨ ∀ o b, out ≠ .dispatched o b⌝ ∨
    ∃ (am : apply.AuthenticateModel) (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result)
      (resp : Loc),
      ⌜rq.authenticate = some am ∧
        v.Resp' = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty)
          #resp⌝ ∗
      ar ↦□ v ∗ apply.authnOut γa am.name resp v.Err')

/-- **An admin entry's application with auth on** (see the file header): the triple. (C1's A2) An
`Authenticate` entry too (`adminKindOk`; it needs no admin permission): with `v3`, the right to
its token at the index `ConsistentIndex()` reads under what it borrows from `Pre`
(`apply.adminExtra`), giving back the response (`adminAuthnAr`). -/
abbrev adminEntryOn.spec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (γa : auth.AuthNames)
    (stl bel : Loc) (T : IProp GF) (st : auth.AuthState) (rs : apply.RestM),
    E.authMode = .on γa → apply.noSideEffect rq = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        Perennial.EtcdGrove.apply.uberAuthStepsL ua E (adminW stl bel (.on γa) E.P E.f T)
          (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
          (auth.latestRes stl (.on γa)) ∗
        waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
        (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
            (Q ={⊤}=∗ E.P ∗ Post))
         else iprop(True)) ∗ Pre ∗
        apply.applyKV E ua x ∗
        ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
          apply.dispatchOk E.authOn rq ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
        ⌜x.chain = apply.baseChain E.authOn⌝ ∗
        (∃ (hs : List auth.AuthState), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
          ⌜hs.getLast? = some st⌝) ∗
        T ∗ auth.tpAdmin stl (.on γa) ∗ authWBackendAt bel (.on γa) E.P E.f T ∗
        roLendsAuthBe E.RO stl bel ∗ E.RO rs ∗ ⧗ 1 ∗ (if v3 then apply.adminExtra E γa rq Pre else iprop(True)) }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
        (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
    {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗
        (if v3 then iprop(Post ∨ Pre) else Pre) ∗
        apply.resultErrOk ar ∗ apply.resTrace ar ∗ ⌜id' = id⌝ ∗
        ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
          ⌜apply.applyStep rq v3 x x' out ∧ x'.log = x.log ∧ x'.chain = x.chain⌝ ∗
          apply.applyResultIs rq v3 x.log ar out ∗ (⌜out.waived = false⌝ ∨ G ot id) ∗
          apply.adminRejErr ar out ∗
          (if v3 then iprop(⌜ar = null⌝ ∨ ∃ err : GoInterface,
              structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
              notNoSpaceErr err)
           else iprop(True)) ∗
          E.RO rs ∗ T ∗ auth.tpAdmin stl (.on γa) ∗
          ∃ (hs' : List auth.AuthState) (st' : auth.AuthState),
            auth.authOwnFu γa hs' ∗ auth.tieRes stl (.on γa) hs' ∗
            ⌜hs'.getLast? = some st' ∧ (if v3 then adminStateR rq st st' else st' = st)⌝ ∗
            (if v3 then adminTieAr ar rq st st' out else iprop(True)) ∗
          (if v3 then adminAuthnAr γa ar rq out else iprop(True)) }}

/-- **An admin entry's application with auth on** (see the file header). -/
theorem apply_admin_entry_on
    (hAL : Perennial.EtcdGrove.apply.Apply.adminSpecL (GF := GF) (hG := hG)) :
    adminEntryOn.spec (GF := GF) (hG := hG) := by
  -- (C1's A2) phase 1 of the spec-first stage: the proof (at 2040bccc8a) is redone in phase 2
  sorry

end proof

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.apply_admin_entry_on
