# `EtcdServer.Put` (2026-10-27)

The server's `s.Put(ctx, r)` (`v3_server.go`): a put proposed through raft, applied by the apply
thread. Reviewed by the user over six candidates; the last is the one the user approved.

## The first version (the repository's spec at the time)

```lean
abbrev EtcdServer.Put.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull)
    (Q : KVState → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.putRequestIs r op ∗ putPermit ρ.kv op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
          (o : apply.Outcome) (skip : Bool),
          ⌜apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip) ∧
            (∃ log', o = .applied log' false) ∧ F <+: x.log⌝ ∗
          apply.putOutcomeIs x.log op resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut op) hm) F err) ∨
          srvMaybeDeposited ρ (irrPut op)))) }}
```

(and a word-for-word copy `specOn` for auth enabled, with `isServerReqM true`, `putPermitOn` and one
more conjunct.)

## The critiques, in order

1. **Candidate 1** stated the post over two logs (`lb`, `la = putLogAfter op lb`) with the floor `F`
   and the certificates kept, and merged `spec`/`specOn` into `specM on`. Its failure branch dropped
   `appliedErr ∨ srvMaybeDeposited`, which is vacuous (`srvMaybeDeposited` holds with `proposed :=
   false`).
2. **Candidate 2** bundled the certificates into one predicate `srvLogLb E ρ l`. The user: "This spec
   should be the same spec that an alternate implementation would have. For instance, I could
   implement an in-memory, single-server version of etcd that has no raft library and no
   srvLogLb." And: "When I ask for a spec to be improved, I'm generally wanting to change predicates
   that are used in that spec too."
3. **Candidate 3** rebuilt the vocabulary over the abstract state: `kvState γ σ`, one handle
   `isKVServer s γ`, one namespace `kvN`; linearizability as the caller's atomic update, which
   replaced the floor and every certificate. It kept a per-caller token `kvCaller s` for the reader
   slots. The user: "Why is kvCaller needed? Would the spec be unprovable without it?" It was not:
   the caller's `threadTok` bounds the readers.
4. **Candidate 4** took the update as a helper `kvOpAu1 γ (.put op) Q`. The user: "get rid of
   kvOpAu1 as a helper definition, and just write the AU directly in the hoare triple. It should
   look like the client Put spec."
5. **Candidate 5** copied the client's `σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ ∧ kvLogOk (…)` into the post.
   The user: "Why did you add the pure facts with random hard-coded numbers?" They were proof slack
   and facts of every reachable state, now one law of the vocabulary.
6. **Candidate 6**, approved: "This looks good for my review."

## The approved spec (candidate 6)

The vocabulary (an implementation defines it, sealed in its API module):

```lean
opaque KVName : Type
/-- The KV's current state is `σ`: the client's view, what its atomic updates are over. -/
opaque kvState (γ : KVName) (σ : KVState) : IProp GF
/-- The namespace an implementation reserves for its invariants. -/
def kvN : Namespace := nroot .@ "etcd_kv"
/-- `s` serves the KV `γ` (persistent). Law: `isKVServer s γ ⊢ ⌜threadBound GF ≤ 2 ^ 30⌝`. -/
opaque isKVServer (s : Loc) (γ : KVName) : IProp GF

inductive KVReachable : KVState → Prop
  | start : KVReachable kvStart
  | step (op : KVOp) (σ : KVState) : KVReachable σ → KVReachable (kvOpStep op σ)
/-- Law: every state of a served KV is reachable. -/
theorem kvState_reachable (s : Loc) (γ : KVName) (σ : KVState) :
  isKVServer (GF := GF) s γ ∗ kvState γ σ ⊢ ⌜KVReachable σ⌝
```

The triple:

```lean
abbrev EtcdServer.Put.spec : Prop :=
  ∀ (s : Loc) (γ : KVName) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (r : Loc) (op : OpFull) (Q : KVState → IProp GF),
  {{ isKVServer s γ ∗ threadTok ∗ context.isContext ctx cd ∗ txn.putRequestIs r op ∗
      ⌜op.leaseID = W64 0⌝ ∗
      AU <{ ∃∃ (σ : KVState), kvState γ σ }> @ ⊤ \ ↑kvN, ∅
        <{ kvState γ (kvOpStep (.put op) σ), COMM Q σ }> }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState,
          txn.putResponseIs resp (W64 ((σ.rev + 1 : Nat) : Int))
            (if op.base.prevKV then (σ.store.lookup op.key).map (KVRec.toKv op.key) else none) ∗
          txn.respHdrOwn (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
          Q σ) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}
```

Open when approved: auth (with auth enabled the update must read the auth state), the revision's
overflow (the time receipts bound the writes), a stronger failure branch (the update back for errors
raised before the request can take effect), and `op.leaseID = 0` (a scope restriction of the proof).

Found after the approval, not yet reviewed: an `IgnoreValue`/`IgnoreLease` put of a missing key
leaves the state unchanged and fails with `ErrKeyNotFound`, so success must also say the put
committed.
