/-
**The auth store's view of a backend** (the auth-on snapshot plan's P6.2, 2026-11-03; moved out of
`AuthSnapKit.lean` so that the apply thread's auth row, `StoreLatest.lean`, can name it): the
realization's open share `authOpenQ`, the schema auth backend `ablOn`, and the write contract at a
frozen hook `authWAtHook`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The auth realization's share of a backend's open token** (a quarter). -/
def authOpenQ : Qp := (1 : Qp).half.half

/-- The auth buckets: lean's `auth.authBkts` (the backend-auth-split stage). -/
abbrev authBkts : GoString → Prop := auth.authBkts

-- `backend.rbOwnIn` (decision 1's per-bucket idleness) is the backend's own (`InvBackend.lean`,
-- landed with the backend stage, `a43af91055`); the Draft's opaque stand-in and its split law are gone
-- (the real split is `rbOwn_split`'s into two `rbPart`s, of which only a written-back one is idle).

/-- The schema auth backend `abl` over the backend `be`, with the logger `lg` (read-only). -/
def ablOn (abl : Loc) (be lg : Loc) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #be : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg)

instance ablOn_persistent (abl be lg : Loc) : Persistent (ablOn (GF := GF) abl be lg) := by
  unfold ablOn; infer_instance

/-- **The write contract at every schema auth backend on `d`'s backend, at its frozen hook**
(`authSchemaSrv`'s E3l/E3n clause), at the backend `γc`'s write token. -/
def authWAtHook (γa : auth.AuthNames) (d : mvcc.KBReal) (γc : auth.AuthBkNames) : IProp GF :=
  iprop(□ ∀ (abl' lg' : Loc) (W' Pk' : IProp GF) (f' : GoFunc),
    ablOn abl' d.be lg' -∗ backend.isBackend d.γB d.P W' Pk' d.be -∗ backend.plHookRO d.γB f' -∗
    ⌜f' ≠ func.nil⌝ -∗ auth.authWBackendOkR (authBkIface abl') (.on γa) Pk' #f' (auth.authWTok γc))

instance authWAtHook_persistent (γa : auth.AuthNames) (d : mvcc.KBReal) (γc : auth.AuthBkNames) :
    Persistent (authWAtHook (GF := GF) γa d γc) := by
  unfold authWAtHook; infer_instance

/-- **The realization lends the auth buckets to the writer** (trusted, `authSchemaSrv`'s and
`authSchemaSnap`'s; persistent; #7-on, the user's approval of 2026-11-03): the holder of the backend
`γc`'s write token and of the admin side's half of the history `hs` borrows a part of `d`'s tracked
auth buckets, which hold `hs`'s latest state (`authBucketsAt`), and gives it back. True of the code:
every auth write is the apply thread's, inside a batch transaction it holds the write token for, so
while it holds the token (with the history's half) no auth write is pending and the buckets are the
latest state's encoding. What the merged snapshot's window observes the auth buckets with
(`srvImageOn`'s `authBucketsAt`). -/
def authBkLend (γa : auth.AuthNames) (γc : auth.AuthBkNames) (d : mvcc.KBReal) : IProp GF :=
  iprop(□ ∀ (hs : List auth.AuthState) (st : auth.AuthState), ⌜hs.getLast? = some st⌝ -∗
    auth.authWTok γc -∗ auth.authHistHalf γa hs ={⊤}=∗
      ∃ r : GMap GoString backend.BktData, backend.rbPart d.γB authBkts r ∗ ⌜authBucketsAt st r⌝ ∗
        (backend.rbPart d.γB authBkts r ={⊤}=∗ auth.authWTok γc ∗ auth.authHistHalf γa hs))

instance authBkLend_persistent (γa : auth.AuthNames) (γc : auth.AuthBkNames) (d : mvcc.KBReal) :
    Persistent (authBkLend (GF := GF) γa γc d) := by
  unfold authBkLend; infer_instance

/-- **A lend of tracked buckets of the environment's backend** (#7-on, 2026-11-03): at the
backend `d` of `E`'s store, a part of the buckets `SA` at contents `r` with `QA r`, given back for
`RA`. What the merged snapshot's window observes the auth buckets with in the mode `on`
(`srvAuthApplyResB_lend`, from `authBkLend`); nothing in the mode `off` (`bkLendW_none`). -/
def bkLendW (E : apply.AEnv GF) (SA : GoString → Prop) (QA : GMap GoString backend.BktData → Prop)
    (RA : IProp GF) : IProp GF :=
  iprop(∀ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ={⊤}=∗ ∃ r : GMap GoString backend.BktData,
    ⌜QA r⌝ ∗ backend.rbPart d.γB SA r ∗ (backend.rbPart d.γB SA r ={⊤}=∗ RA))

end defs

end EtcdGrove
end Perennial
