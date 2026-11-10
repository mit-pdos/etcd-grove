/-
`lease.NewLessor(lg, b, cluster, cfg)` (`lessor.go:208`) on a backend whose `Lease` bucket holds
records: a restart (a member's backend reopened on its file). DRAFT (mvccfull F1, 2026-11-09), a
candidate restatement of `lease.NewLessor.spec` (`NewLessor.lean`), which it generalizes from the
empty bucket (`NewLessor.spec_of_specR`, proved); for etcd's server restart
(`notes/restart-plan.md`, R2d'b) and the tester `examples/mvccfull` (`runner.open` after `shut`).
Not yet an axiom: at the Freeze switch it replaces the axiom `lease.NewLessor.wp_proof` (one axiom,
`specR`; the original a theorem from it), which also settles the bounds gate (review round 1's F2:
the copied `replicate … actualMaxReaders`).

**The receipt `⧖ |recs|`** (review round 1's F1; settled by the axiom review,
`notes/axiom-review/mvccfull-newlessor-specR.md`: kept). The post's `lessorInv` holds `lessorMu`'s
`⧖ (size M)` (`InvLessor.lean`), so at the recovered map (`M = recMap (recs.zip ls)`) this axiom
gives out the receipt `⧖ recs.length`, which the original (at `M = ∅`, `⧖ 0`) never did. Its source
is the translated code: `NewLessor` → `newLessor` → `initAndRecover`, and the proved
`lessor.initAndRecover.spec` (`Spec/.../lease/lessor__initAndRecover.lean`) has `⧖ recs.length` in
its post with no receipt in its pre (its proof starts from `preceipt_zero` and raises the receipt
once per iteration of the recovery loop, `lessor.go:815-830`: `wp_raise_receipt`). So the receipt
is what the translation of the same Go code proves; the axiom adds only `newLessor`'s names-only
wrapper (its fields, the reader slots, the `runLoop` goroutine), not the step count. The per-lease
allocations (`make(chan struct{})` for `revokec`, the zero `RWMutex` of `&Lease{}`, inside
`leaseOwn`'s closers) are `initAndRecover`'s too. (The alternative, the receipt in the pre, would be
strictly weaker for clients and cost the server a law, `recs.length ≤ logCh L` of the image, for no
soundness.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewLessor(lg, b, cl, cfg)` over a `Lease` bucket holding the records `recs`**: everything
`lease.NewLessor.spec` says (its docstring is this one's, clause by clause), except that the
bucket, a part of any bucket set `S` containing it (`rbPart d.γB S r`), holds in key order the
records `recs`, each what `Grant` writes (`backend.bktEnts … = recs.map leaseRecEnc`, `Recover`'s
premise; empty or absent: `recs = []`, the original; a scope restriction, as `Recover`'s: only
buckets whose every value is exactly `leaseRecEnc` of a record, `proto.Marshal` of the three fields;
a bucket written by another tool, or a record with unknown fields, which Go would decode, is
outside it), and what the lessor makes of them is what
`Recover` makes (`lessor.Recover.spec`), at a lessor that had nothing before (`L = []`, `U = []`).
The new clauses, and why each is true of the Go code (`newLessor` `lessor.go:212-249`,
`initAndRecover` `:808-835`):
* **The records are read and decoded** (pre: the entries' equation, replacing `getD ∅ = ∅`):
  `initAndRecover` takes the batch lock (`:811`), creates the bucket (absent: none; present: a
  no-op, `UnsafeCreateLeaseBucket`), and `MustUnsafeGetAllLeases` (`:813`) decodes every record
  (a panic on an undecodable one; each record here is an encoding, `leaseRecEnc`, so none). One
  write-back (`wbTok`), with records as without: `UnsafeCreateBucket` always counts a pending
  operation (`pending++`, `batch_tx.go:144`), so the first `Unlock` (`:814`) writes back
  (`batch_tx.go:328-333`) and may commit (`pending >= batchLimit`, `:355`); `ForceCommit`
  (`backend.go:377`) is `lock`, `commit`, `Unlock` (`batch_tx.go:362-366`), and `commit` resets
  `pending = 0` (`:300`), so its `Unlock` writes nothing back (a hook the commit runs may write;
  `commit` still resets `pending`). The records change neither `pending` nor the commits (the loop
  writes no bucket). One token is stronger than what the proved `lessor.initAndRecover.spec` gives
  (`ownToks γB.wb 2`): the original's known margin, unchanged by records. So the part comes back idle with the bucket as it was
  (`rbOwnIn d.γB S (r.insert "lease" ((r.lookup "lease").getD ∅))`, `Recover`'s post; the
  original's `r.insert "lease" ∅` when it was empty or absent).
* **One fresh lease per record** (`:815-830`): `ID` the record's, `ttl` the record's raised to
  `le.minLeaseTTL`, which `newLessor` set to `cfg.MinLeaseTTL` (`:231`, never written again: the
  post's `lF "minLeaseTTL" lp ↦□ cfg.MinLeaseTTL'`, review round 1's S2, which ties `lessorCfg`'s
  minimum, the one a later `Grant` raises to, to the recovered TTLs'), no item, `expiry` forever,
  a fresh `revokec`, `remainingTTL` the record's, put into the fresh `leaseMap` (no registration
  with the expiry notifier, `Init` of an empty one; the heap empty). So the live set is the
  records' ids in the caller's order `Lr` with no item (`leaseOwn γl Lr ∅`, the original's
  `leaseOwn γl [] ∅` at `recs = []`), each with its close right (`leaseRevokers γl Lr`): what
  `Recover`'s post gives for the same loop. The ids are distinct (the bucket's keys are, and a
  record's key is its id's 8 bytes).
* **The history's first snapshot is the recovered one** (ghost state only): the readers' model is
  allocated (as in the original) at the single snapshot `(recMap (recs.zip ls), ∅, recTTLs
  cfg.MinLeaseTTL' recs)` (the leases `ls` above; their TTLs the raised ones, each lease's `ttl`
  field, written before the map insertion and never after: `ttlTie`), the item sets' map at the
  new leases' empty sets; its facts hold of one snapshot (`histOk`: one id per lease, no item;
  `histMono`, `histOnce` trivially; `histIn`/`histCover` of the records' ids). The caller gets its
  index, `0` (`lessorAt γl 0 _`; at `recs = []` the original's `lessorAt_empty` derives it).
* **The ids the lessor ever had** (`leaseEver γl (recs.map (·.1))`): allocated at the records'
  ids, which the first snapshot has (`histIn`, `histCover`); at `recs = []`, the original's `[]`.
  Ghost state, allocated fresh with the readers' names: the caller gives nothing for it (a fresh
  lessor never had an id; `Recover`'s premises on `U` hold at `U = []`).
* **The leases' requested TTLs** (`□ leaseReqIs γl x.1 (reqOf x.1)`, the caller naming each
  record's request `reqOf`, at most its TTL): the requests' map allocated at those requests, not
  empty; `reqOk` holds since each first-snapshot TTL is the record's raised (`grantTTL`), at least
  the record's, at least the request. Persistent discarded elements: no counted resource.
* **The grant guard** (pre: `□ GA id` for every record's id): every lease of the map has the
  guard of its id (`lessorAuth`'s `leaseGranted`, `Lookup`'s and `expiredC`'s `□ GA id`); the
  original's map starts empty, so it needed none; here the caller gives it (`Recover` takes it,
  as `leaseGranted`, for the same reason). Persistent.
* **The mode** `mono`: as the original; a single snapshot is monotone (`histMono`), so either mode
  holds with records too (`Recover`'s mode premise, live ids among the records', is vacuous at
  `L = []`).
Everything else, the `runLoop` goroutine (`:245`) and what the post says of it (`lessorExpiredC`,
`lessorGuard`, the `Lookup` clause, `lessorCkptOk`), the configuration, the reader slots, `rd`
unset, `lessorBeOn`/`lessorApplyOk`, the stop right, is the original's, word for word: the loop
does not read the bucket, and every lease it sends or `Lookup` returns is the map's, with `GA` of
its id by the guard clause above. -/
abbrev lease.NewLessor.specR : Prop :=
  ∀ (lg : Loc) (cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (GA : w64 → IProp GF)
    (S : GoString → Prop) (r : GMap GoString backend.BktData) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (reqOf : w64 → w64) (Lr : List w64),
  S go!"lease" → mvcc.leaseParams d.P →
  backend.bktEnts ((r.lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc →
  (∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) → Lr.Perm (recs.map (·.1)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ ⌜lg ≠ null⌝ ∗
      ⌜ckptEffectsOk⌝ ∗ ⌜0 ≤ sint.Z cfg.leaseRevokeRate'⌝ ∗ lease.clusterOk cl ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      backend.rbPart d.γB S r ∗ □ ([∗list] id ∈ recs.map (·.1), GA id) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLessor)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #cl)) (Val #cfg))
  {{ (l : GoInterface), RET #l; backend.bOpen d.γB qo ∗
      backend.rbOwnIn d.γB S (r.insert go!"lease" ((r.lookup go!"lease").getD ∅)) ∗
      ∃ (lp : Loc) (γl : GName),
      ⌜l = lease.lessorIface lp⌝ ∗ lease.lessorInv lp γl ∗ lease.lessorModeIs γl mono ∗
      lease.lessorCfg lp ∗ lease.lF go!"minLeaseTTL" lp ↦□ cfg.MinLeaseTTL' ∗
      lease.lessorExpiredC lp GA ∗ lease.lessorGuard γl GA ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), lease.lessorRdOf γl) ∗
      lease.leaseOwn γl Lr ∅ ∗ lease.leaseEver γl (recs.map (·.1)) ∗ lease.leaseRevokers γl Lr ∗
      lease.rdOwn γl func.nil ∗ lessorCkptOk l ∗
      lease.lessorBeOn lp d.be ∗ lessorApplyOk lp ∗
      lease.lessorStopTok lp ∗
      □ ([∗list] x ∈ recs, lease.leaseReqIs γl x.1 (reqOf x.1)) ∗
      (∃ ls : List Loc, ⌜ls.length = recs.length⌝ ∗
        lease.lessorAt γl 0 (lease.recMap (recs.zip ls), ∅, lease.recTTLs cfg.MinLeaseTTL' recs)) ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.lease.lessor.ty @!! go!"Lookup")) (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ (apply.leaseIs l id ∗ □ GA id) }}) }}

end spec

section derive
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The original is the instance at no record** (`recs = []`, `Lr = []`): its `getD ∅ = ∅` gives
the entries' equation, and the extra post (the empty requests, the first snapshot) is dropped. -/
theorem lease.NewLessor.spec_of_specR (h : lease.NewLessor.specR (GF := GF) (hG := hG)) :
    lease.NewLessor.spec (GF := GF) (hG := hG) := by
  intro lg cl cfg d W Pk qo GA S r mono hS hP
  iintro %Φ ⟨#Hpkg, %Hlg, %Hck, %Hrr, #Hcl, #Hb, Ho, Hwb, Hrb, %Hempty⟩ HΦ
  have hrecs : backend.bktEnts ((r.lookup go!"lease").getD ∅) =
      ([] : List (w64 × w64 × w64)).map lease.leaseRecEnc := by
    rw [Hempty]; simp [backend.bktEnts]
  iapply (h lg cl cfg d W Pk qo GA S r mono [] (fun _ => W64 0) [] hS hP hrecs
    (by simp) (List.Perm.refl _)) $$ [Ho Hwb Hrb]
  · iframe; iframe #
    isplitr; · ipureintro; exact Hlg
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Hrr
    imodintro; rw [List.map_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
  rw [Hempty]
  iintro !> %l ⟨Ho, Hrb, %lp, %γl, %Hl, Hinv, Hmode, Hcfg, -, Hexp, Hguard, Hrds, Hown, Hever,
    Hrev, Hrd, Hck', Hbe, Hap, Hstop, -, -, Hlook⟩
  iapply HΦ
  iframe Ho Hrb
  iexists lp, γl
  iframe
  ipureintro; exact Hl

end derive

end EtcdGrove
end Perennial
