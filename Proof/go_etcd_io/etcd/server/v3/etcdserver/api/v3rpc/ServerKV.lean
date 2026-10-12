/-
**The server's contract instantiated** (unit 3a of the request path, 2026-10-12): the
parameters `A : KVAns GF` of unit 1's `raftKV s A` (`InvKV.lean`) for the server `s`, and
`raftKV`'s `Put` and `DeleteRange` conjuncts proved from unit 2's `EtcdServer.Put` and
`EtcdServer.DeleteRange` (`kvPutOk_of_server`, `kvDeleteOk_of_server`, `raftKV_of_server`).
Lean-first (no Rocq counterpart); plan: `notes/decisions.md`, "The request path".

**`srvKVAns s E ρ A0`**: what a call needs (`srvCall`: the request's context, one id credit, a
reader slot of `s.leadTimeMu`; and `A0.call`, the read side's, 3b's), what a successful `Put` is
(`putAppliedOk`: applied by the apply thread at the log `x.log` the entry met, the outcome
`putOutcomeIs`, the header's revision the put's, mvcc's certificate of the log after, the reader
slot back), what a successful `DeleteRange` is (`deleteAppliedOk`), what their errors are
(`putErrOk`/`deleteErrOk`: the apply's or the proposal's, the reader slot back); for `Range` and
`Txn`, and for `KV().Rev()` (`revR`), `A0`'s (unit 3b instantiates them).

**What the server's answers give the handler** (`kvAnswer`): the response header's four id
fields owned (`apply.appliedHdr` → `hdrW`), its revision read-only and not `0` (the log has
`NewStore`'s two revisions and room for the write: `hdrRevIn`'s first case, so `header.fill`
never calls `rev()` on these answers), an error `togRPCError` can take (`srvErrIs`, from
`applyErrIs`: `srvErrIs_of_applyErrIs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__DeleteRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An error `togRPCError` can take, from the apply package's facts**: a non-nil error with
`applyErrIs` (its tree, a safe map key, an `Error()` that returns). -/
theorem srvErrIs_of_applyErrIs (err : GoInterface) (hne : err ≠ GoInterface.nil) :
    applyErrIs (GF := GF) err ⊢ srvErrIs err := by
  iintro #H
  iunfold srvErrIs
  isplitr
  · ipureintro; exact hne
  isplitr
  · iexact H
  ihave #Hkm : iprop(errKeyMsg err) $$ []
  · iunfold applyErrIs at H; icases H with ⟨-, #Hkm⟩; iexact Hkm
  iunfold errKeyMsg at Hkm
  icases Hkm with (%Hn | ⟨%Hsafe, %ei, %Hei, #Hm⟩)
  · exact absurd Hn hne
  isplitr
  · ipureintro; exact Hsafe
  iexists ei
  isplitr
  · ipureintro; exact Hei
  iunfold errMsgOk at Hm
  iexact Hm

/-- **What one call of the server's write path needs** (`EtcdServer.Put`/`DeleteRange`): the
request's context (a `context.Context` value with Perennial's `isContext`), one id credit (for
`reqIDGen.Next()`), a reader slot of `s.leadTimeMu` (`parseProposeCtxErr` read-locks it; given
back with the answer). -/
def srvCall (s : Loc) (ρ : ReqNames) (ctx : GoInterface) : IProp GF :=
  iprop(∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)), ⌜ctx = GoInterface.ok ci⌝ ∗
    context.isContext ci cd ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s)

/-- **A successful `Put` of `o`** (`EtcdServer.Put`'s success, at the handler's level): the
request with the server's header (`hm`) was dispatched by the apply thread at the KV state `x`
to `x'` and applied (`applied l false`: `putModel`'s, no `ErrNoSpace`), the response is the
put's (`putOutcomeIs` at `x.log`: header revision `x.log.length`, the previous key-value if
asked), the header's revision `r` is that revision, mvcc's certificate of the log after; the
caller's reader slot back. -/
def putAppliedOk (s : Loc) (E : apply.AEnv GF) (o : OpFull) (resp : Loc) (r : w64) :
    IProp GF :=
  iprop(srvLeadTimeReader s ∗ ∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : mvcc.Log)
      (skip : Bool),
    ⌜apply.applyStep (apply.withHeader (irrPut o) hm) true x x' (.dispatched (.applied l false) skip) ∧
      r = W64 (x.log.length : Int)⌝ ∗
    apply.putOutcomeIs x.log o resp GoInterface.nil (.applied l false) ∗
    mvcc.idxCert E.γ.idx x'.log)

/-- **A successful `DeleteRange` of `o`**: as `putAppliedOk`, for the request the proposed data
decode to (`rq'`, whose delete `op'` is `o` unless its range end is `[0]`, `irrWireOf`); the
header's revision the delete's (`writeRev`). -/
def deleteAppliedOk (s : Loc) (E : apply.AEnv GF) (o : OpFull) (resp : Loc) (r : w64) :
    IProp GF :=
  iprop(srvLeadTimeReader s ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
      (x x' : apply.ApplyKV) (l : mvcc.Log) (skip : Bool),
    ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq' ∧ rq'.deleteRange = some op' ∧
      (irrNoZeroEnd (irrDeleteRange o) → op' = o) ∧
      apply.applyStep rq' true x x' (.dispatched (.applied l false) skip) ∧
      r = W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int)⌝ ∗
    apply.deleteOutcomeIs x.log op' resp GoInterface.nil (.applied l false) ∗
    mvcc.idxCert E.γ.idx x'.log)

/-- **A failed `Put` of `o`**: the apply thread's error (`appliedErr`), or the proposal's (made
or not; if made, deposited: it may still be applied, `srvMaybeDeposited`); the reader slot
back. -/
def putErrOk (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (o : OpFull) (err : GoInterface) :
    IProp GF :=
  iprop(srvLeadTimeReader s ∗
    ((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut o) hm) err) ∨
      srvMaybeDeposited ρ (irrPut o)))

/-- **A failed `DeleteRange` of `o`** (as `putErrOk`). -/
def deleteErrOk (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (o : OpFull) (err : GoInterface) :
    IProp GF :=
  iprop(srvLeadTimeReader s ∗
    ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
        ⌜irrWireOf (apply.withHeader (irrDeleteRange o) hm) rq'⌝ ∗ appliedErr E rq' err) ∨
      srvMaybeDeposited ρ (irrDeleteRange o)))

/-- **The server's parameters of `raftKV`** (see the file header): the write path's
(`Put`, `DeleteRange`) from unit 2's specs, the read side's (`Range`, `Txn`, `KV().Rev()`) from
`A0` (unit 3b's). -/
def srvKVAns (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (A0 : KVAns GF) : KVAns GF where
  call ctx := iprop(srvCall s ρ ctx ∗ A0.call ctx)
  ok q resp h r := match q with
    | .put o => putAppliedOk s E o resp r
    | .deleteRange o => deleteAppliedOk s E o resp r
    | q => A0.ok q resp h r
  err q e := match q with
    | .put o => putErrOk s E ρ o e
    | .deleteRange o => deleteErrOk s E ρ o e
    | q => A0.err q e
  revR := A0.revR

/-- **The `*kvServer` `p`, but for the server's contract** (`kvServerIs` without `raftKV`): its
header, `kv` the server `s`, the transaction budget `n`. What `NewKVServer(s)` builds, apart
from the server's own triples (`kvServerIs_of_at`). -/
def kvServerAt (p : Loc) (s : Loc) (A : KVAns GF) (cid mid n : w64) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    hdrIs (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"hdr" p)
      s A cid mid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"kv" p ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"maxTxnOps" p ↦□ n)

instance kvServerAt_persistent (p s : Loc) (A : KVAns GF) (cid mid n : w64) :
    Persistent (kvServerAt p s A cid mid n) := by
  unfold kvServerAt; infer_instance

theorem kvServerIs_of_at (p s : Loc) (A : KVAns GF) (cid mid n : w64) :
    kvServerAt (GF := GF) p s A cid mid n ∗ raftKV s A ⊢ kvServerIs p s A cid mid n := by
  iintro ⟨#Hat, #HKV⟩
  iunfold kvServerAt at Hat
  icases Hat with ⟨%Hpn, #Hh, #Hk, #Hn⟩
  iunfold kvServerIs
  iframe #
  ipureintro; exact Hpn

end defs

/-- A revision at a log of `NewStore`'s two revisions at least, and room: not `0`. -/
theorem w64_rev_ne_zero (n : Nat) (h1 : 1 ≤ n) (h2 : n + 4 ≤ 2 ^ 63) : W64 (n : Int) ≠ W64 0 := by
  intro h
  have := congrArg (fun w : w64 => uint.Z w) h
  word

/-- The delete's revision (`writeRev`) at such a log: at least `1`. -/
theorem writeRev_ne_zero (log : mvcc.Log) (pend : List mvcc.Change) (h1 : 2 ≤ log.length)
    (h2 : log.length + 4 ≤ 2 ^ 63) : W64 ((mvcc.writeRev log pend : Nat) : Int) ≠ W64 0 := by
  apply w64_rev_ne_zero
  · unfold mvcc.writeRev; split <;> omega
  · unfold mvcc.writeRev; split <;> omega

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`raftKV`'s `Put` conjunct, from `EtcdServer.Put`**. -/
theorem kvPutOk_of_server (hPut : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (A0 : KVAns GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerReq s E ρ ⊢
      kvPutOk s (srvKVAns s E ρ A0) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvPutOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  simp only [srvKVAns]
  icases Hcall with ⟨Hcall, -⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, Hcred, Hrd⟩
  subst Hci
  wp_apply hPut s E ρ ci cd r o $$ [Hrd Hcred] as %resp %err ⟨Hrd, Hres⟩
  · iframe #; iframe Hrd Hcred
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert⟩ |
    ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hstep, l, rfl⟩ := Hst
    subst Herr
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    icases Hpo with ⟨#Hresp, -⟩
    ihave #Hresp' := Hresp
    iunfold txn.putResponseIs at Hresp'
    icases Hresp' with ⟨%Hrn, %h, %pk, #Hhf, %Hhn, #Hrev, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hown, %Hlen⟩
    iunfold txn.respHdrOwn at Hown
    icases Hown with ⟨%h', #Hhf', %Hhn', %c, %m, %t, %ld, Hc, Hm, Ht, Hl⟩
    icombine Hhf Hhf' gives %Heq
    subst Heq
    ileft
    isplitr
    · ipureintro; exact ⟨trivial, Hrn⟩
    iexists h, W64 (x.log.length : Int)
    iframe Hhf
    isplitl [Hc Hm Ht Hl]
    · iunfold hdrW
      isplitr
      · ipureintro; exact Hhn
      iexists c, m, t, ld
      iframe
    isplitr
    · iunfold hdrRevIn
      ileft
      isplitr
      · ipureintro; exact w64_rev_ne_zero _ (by omega) Hlen.2
      iexact Hrev
    iunfold putAppliedOk
    iframe Hrd
    iexists hm, x, x', l, skip
    iframe Hcert
    isplitr
    · ipureintro; exact ⟨Hstep, rfl⟩
    simp only [apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iunfold putErrOk
    iframe Hrd Hfail

/-- **`raftKV`'s `DeleteRange` conjunct, from `EtcdServer.DeleteRange`**. -/
theorem kvDeleteOk_of_server (hDel : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (A0 : KVAns GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerReq s E ρ ⊢
      kvDeleteOk s (srvKVAns s E ρ A0) := by
  iintro ⟨#Hpkg, #Hsrv⟩
  iunfold kvDeleteOk
  iintro %ctx %r %o !> %Φ ⟨Hcall, #Hr, %Hok⟩ HΦ
  simp only [srvKVAns]
  icases Hcall with ⟨Hcall, -⟩
  iunfold srvCall at Hcall
  icases Hcall with ⟨%ci, %cd, %Hci, #Hctx, Hcred, Hrd⟩
  subst Hci
  wp_apply hDel s E ρ ci cd r o $$ [Hrd Hcred] as %resp %err ⟨Hrd, Hres⟩
  · iframe #; iframe Hrd Hcred
  iapply HΦ
  iunfold kvAnswer
  icases Hres with (⟨%Herr, %hm, %rq', %op', %x, %x', %oc, %skip, %Hst, Hpo, Hhdr, #Hcert⟩ |
    ⟨%Hre, #HaE, Hfail⟩)
  · obtain ⟨Hwire, Hop', Hnz, Hstep, l, rfl⟩ := Hst
    subst Herr
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    icases Hpo with ⟨#Hresp, -⟩
    ihave #Hresp' := Hresp
    iunfold txn.deleteRangeResponseIs at Hresp'
    icases Hresp' with ⟨%Hrn, %h, %sl, %ps, #Hhf, %Hhn, #Hrev, -⟩
    iunfold apply.appliedHdr at Hhdr
    icases Hhdr with ⟨Hown, %Hlen⟩
    iunfold txn.respHdrOwn at Hown
    icases Hown with ⟨%h', #Hhf', %Hhn', %c, %m, %t, %ld, Hc, Hm, Ht, Hl⟩
    icombine Hhf Hhf' gives %Heq
    subst Heq
    ileft
    isplitr
    · ipureintro; exact ⟨trivial, Hrn⟩
    iexists h, W64 ((mvcc.writeRev x.log (txn.delChanges (mvcc.stateAfter x.log) op') : Nat) : Int)
    iframe Hhf
    isplitl [Hc Hm Ht Hl]
    · iunfold hdrW
      isplitr
      · ipureintro; exact Hhn
      iexists c, m, t, ld
      iframe
    isplitr
    · iunfold hdrRevIn
      ileft
      isplitr
      · ipureintro; exact writeRev_ne_zero _ _ Hlen.1 Hlen.2
      iexact Hrev
    iunfold deleteAppliedOk
    iframe Hrd
    iexists hm, rq', op', x, x', l, skip
    iframe Hcert
    isplitr
    · ipureintro; exact ⟨Hwire, Hop', Hnz, Hstep, rfl⟩
    simp only [apply.deleteOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
  · obtain ⟨rfl, Hne⟩ := Hre
    iright
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply srvErrIs_of_applyErrIs _ Hne $$ HaE
    simp only
    iunfold deleteErrOk
    iframe Hrd Hfail

/-- **The server's contract `raftKV`, its write path discharged**: from `EtcdServer.Put` and
`EtcdServer.DeleteRange` (`kvPutOk_of_server`, `kvDeleteOk_of_server`), with the read side's
conjuncts (`Range`, `Txn`, the header's getters: unit 3b's) as premises, at the parameters
`srvKVAns s E ρ A0`. -/
theorem raftKV_of_server (hPut : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (hDel : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (A0 : KVAns GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerReq s E ρ ∗
        kvRangeOk s (srvKVAns s E ρ A0) ∗ kvTxnOk s (srvKVAns s E ρ A0) ∗
        kvGetOk s (srvKVAns s E ρ A0) ⊢
      raftKV s (srvKVAns s E ρ A0) := by
  iintro ⟨#Hpkg, #Hsrv, #HR, #HT, #HG⟩
  iunfold raftKV
  iframe HR HT HG
  isplitr
  · iapply kvPutOk_of_server hPut s E ρ A0; iframe #
  iapply kvDeleteOk_of_server hDel s E ρ A0; iframe #

end proofs

end v3rpc
end EtcdGrove
end Perennial
