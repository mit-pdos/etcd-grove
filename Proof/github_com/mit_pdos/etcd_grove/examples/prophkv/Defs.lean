/-
The example `prophkv` (`examples/prophkv`): the key-value map's predicates. Lean-first (a port of
Perennial's `goose/testdata/examples/prophkv` proof, whose prophecy is added in Lean instead).

The map `kv` is `isKV kv γ` (persistent): its mutex guards the Go map and the lock's half of the
abstract state `γ` (`kvLockInv`); the client holds the other half, `kvState γ m`, which a caller
of `Put`, `Get` or `GetAny` updates at the operation's linearization point.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.prophkv.Base
public import Perennial.Ghost.GhostVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.prophkv

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- The abstract state of the map `γ`: half of it (the lock holds the other half). -/
def kvState (γ : GName) (m : GMap GoString GoString) : IProp GF := ghostVar γ (1 : Qp).half m

instance kvState_timeless (γ : GName) (m : GMap GoString GoString) :
    Timeless (kvState (GF := GF) γ m) := by
  unfold kvState; infer_instance

/-- The lock's invariant: the Go map, and the lock's half of the abstract state. -/
def kvLockInv (mref : Loc) (γ : GName) : IProp GF :=
  iprop(∃ m : GMap GoString GoString, mref ↦$ m ∗ kvState γ m)

/-- `kv` is a map with abstract state `γ` (persistent). -/
def isKV (kv : Loc) (γ : GName) : IProp GF :=
  iprop(∃ (mu mref : Loc), kv ↦□ (KV.mk mu mref) ∗
    github_com.goose_lang.primitive.isMutex mu (kvLockInv mref γ))

instance isKV_persistent (kv : Loc) (γ : GName) : Persistent (isKV (GF := GF) kv γ) := by
  unfold isKV; infer_instance

/-- The answers `Test`'s map ever gives for `"k"`. -/
def goodVal (v : GoString) : Prop := v = go!"a" ∨ v = go!"b"

end defs

end prophkv
end EtcdGrove
end Perennial
