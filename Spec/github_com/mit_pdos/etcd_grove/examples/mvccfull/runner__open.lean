/- Lean-first (no Rocq counterpart).

`x.open(m)` (`examples/mvccfull/mvccfull.go`, goose's `runner.«open»`): member `m` opens its
backend, lessor and store on its file, as the server does, and checks the store against the model.
The file holds the data `D`, the image (`mvccImage`) of the model's history after `v.ops` operations,
its compaction revision and an unfinished compaction iff `u` (a fresh file's, `mvccImage_fresh.law`,
or a closed store's, `runner.shut`), its lease bucket the live leases' records (`leaseRecsOk`).
`m.rev`, `m.cmp`, `m.leases` are the model's. With what is carried across incarnations
(`memberCarry`, which holds the invariant's halves of `m.σ` and `m.bnd`, and the writer's halves of
both) and the member's hook, the chain's step 3
(`Writer.lean`'s header): `openBackend`, `NewLessor` on the records (`lease.NewLessor.spec`),
`mvcc.New` on the image (`mvcc.api.New.spec`), the hook set; the checks (`Rev`, a read
transaction's `Rev` and `FirstRev`, `checkLeases`) pass. Afterwards the member is `memCore` at a new
incarnation, the writer holding every share (`1`, `1`, `mvccReaderN`) and at least `cfg.Ops`
write-back tokens of the new backend. Fields `be`, `le`, `kv` are overwritten (their old values any).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.open.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)] (x : Loc) (ks : List GoString)
    (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames) (ops : List OpM) (i : Nat) (mp : Loc)
    (m : MemberNames) (f : GoFunc) (n : Nat) (path : GoString) (D : backend.Data) (u : Bool)
    (b : Bnd) (Hl : List HRev) (obe ole okv : GoInterface),
  logOk ks ops → n ≤ ops.length → ops.length < 2 ^ 38 → backend.dbOpenOk → ckptEffectsOk →
  sint.Z (limOf cfg) ≤ 2 ^ 57 → batchLimitOk (cblOf cfg) →
  let σ := σOf ks ops n
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗
      □ (∀ (γB : backend.BNames) (P : backend.BParams) (b' : Loc), keySized γB P b') ∗
      envVerifyOff ∗ threadTok ∗ histRd h γh ∗ monoListLbOwn γh.l (histAt ks ops n) ∗
      mF go!"id" mp ↦□ (W64 (i : Int)) ∗ mF go!"hook" mp ↦□ f ∗ hookOk mp f ∗
      mF go!"path" mp ↦ path ∗ mF go!"be" mp ↦ obe ∗ mF go!"le" mp ↦ ole ∗ mF go!"kv" mp ↦ okv ∗
      mF go!"rev" mp ↦ (W64 (revAfter ks ops n : Int)) ∗ mF go!"cmp" mp ↦ (W64 (cmpAfter ks ops n)) ∗
      (∃ sl : GoSlice, mF go!"leases" mp ↦ sl ∗ sl ↦* leasesAfter ks ops n ∗
        ownSliceCap w64 sl (DFrac.own 1)) ∗
      backend.fileHolds path D ∗ mvccImage D σ.log σ.crev u ∗
      ⌜leaseRecsOk (backend.rbData (mvccrand.rcP (limOf cfg)) D) (leasesAfter ks ops n)⌝ ∗
      memberCarry ks γh mp m σ b Hl ∗ ghostVar m.σ (1 : Qp).half σ ∗ ghostVar m.bnd (1 : Qp).half b }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"open") (Val #mp))
  {{ RET #(); threadTok ∗ histRd h γh ∗
      ∃ (v : MemS) (k : Nat), ⌜v.ops = n ∧ v.path = path ∧ v.b = b ∧ (sint.Z cfg.Ops').toNat ≤ k⌝ ∗
        memCore ks γh ops i mp m f v 1 mvccReaderN k }}

end spec

end mvccfull
end EtcdGrove
end Perennial
