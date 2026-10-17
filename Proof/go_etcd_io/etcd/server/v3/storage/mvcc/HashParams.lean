/-
The hash's parameters (`kvstore.go`'s `store.prepareHashParams`, etcd-io/etcd#21202,
pr-verify/etcd-21202): what the specs of `prepareHashParams`, `hashByRevWithCompactRev`,
`hashByRev` and `hashByRevDetailed` are stated in. Lean-first.

* **The compaction revision the hash uses** (`hashCrev`): the caller's `compactRev` if positive
  (#21202's `--compact-rev`), else the store's (`compactMainRev`, `cm`), as before the PR.
* **The caller's custom compaction revision is at or above the store's** (`hashCrevOk`): the
  premise under which the PR's `rev < compactRev` check also refuses every revision the store
  has compacted (`ErrCompacted`). Without it the code hashes a revision below the store's
  compaction revision (it calls `kvindex.Keep(rev)` with `rev` below it, which
  `treeIndex.Keep`'s spec does not allow), and the hash of `(compactRev, rev]` misses the
  revisions the store's compaction deleted, with no error (`notes/pr-verify/etcd-21202.md`,
  finding 1). The premise is stated with the compaction right (`compactRight`, the one who
  compacts: it fixes the store's compaction revision), as no reader knows a bound above it.
* **The hash histogram** (`hashRevSecOk`): `metrics.go`'s `hashRevSec`, whose `Observe` returns
  (`histSpec`); a premise of the hash's specs, not in the package's facts (`mvccInit`): adding
  it there rebuilds every mvcc proof, out of this branch's scope.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- The compaction revision `prepareHashParams` returns: the caller's `compactRev` if positive,
else the store's `cm`. -/
def hashCrev (compactRev : w64) (cm : Int) : w64 :=
  if sint.Z compactRev ≤ 0 then W64 cm else compactRev

/-- The revision `prepareHashParams` returns: the caller's `rev`, or the store's last revision
`cur` for `0`. -/
def hashRev (rev cur : w64) : w64 := if rev = W64 0 then cur else rev

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The caller's compaction revision is the store's (not positive) or at or above the store's,
which the caller knows by holding the compaction right at `c` (given back). -/
def hashCrevOk (γ : StoreNames) (compactRev : w64) : IProp GF :=
  iprop(⌜sint.Z compactRev ≤ 0⌝ ∨
    ∃ c : Int, compactRight γ c ∗ ⌜-1 ≤ c ∧ c ≤ sint.Z compactRev⌝)

/-- `hashRevSec` (`metrics.go`), a histogram whose `Observe` returns. -/
def hashRevSecOk : IProp GF :=
  iprop(∃ h : GoInterfaceOk, globalAddr hashRevSec ↦□ GoInterface.ok h ∗ histSpec h)

instance hashRevSecOk_persistent : Persistent (hashRevSecOk (GF := GF)) := by
  unfold hashRevSecOk; infer_instance

/-- The cleanup function `prepareHashParams` returns: it returns (it unlocks the read
transaction, whose lock the model does not track: `metaReadTx`). -/
def hashCleanup (f : GoFunc) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #f) (Val #())) {{ RET #(); True }}))

instance hashCleanup_persistent (f : GoFunc) : Persistent (hashCleanup (GF := GF) f) := by
  unfold hashCleanup; infer_instance


/-- With a part of the compaction revision's authority at `cm`, a positive custom compaction
revision is at or above `cm`. -/
theorem hashCrevOk_bound (γ : StoreNames) (compactRev : w64) (q : Qp) (cm : Int) (hcm : -1 ≤ cm) :
    hashCrevOk (GF := GF) γ compactRev ∗ crevUB γ.idx q cm ⊢
      hashCrevOk γ compactRev ∗ crevUB γ.idx q cm ∗
        ⌜0 < sint.Z compactRev → cm ≤ sint.Z compactRev⌝ := by
  iintro ⟨Hok, Hub⟩
  iunfold hashCrevOk at Hok
  icases Hok with (%Hle | ⟨%c', Hr, %Hc'⟩)
  · iframe Hub
    isplitl []
    · iunfold hashCrevOk; ileft; ipureintro; exact Hle
    · ipureintro; intro h; omega
  · iunfold compactRight at Hr
    icases Hr with ⟨Hr, Hq⟩
    ihave %Hcc := crevUB_agree γ.idx _ _ cm c' hcm Hc'.1 $$ Hub Hr
    iframe Hub
    isplitl [Hr Hq]
    · iunfold hashCrevOk; iright; iexists c'; iunfold compactRight; iframe Hr Hq
      ipureintro; exact Hc'
    · ipureintro; intro _; omega

end defs

end mvcc
end EtcdGrove
end Perennial
