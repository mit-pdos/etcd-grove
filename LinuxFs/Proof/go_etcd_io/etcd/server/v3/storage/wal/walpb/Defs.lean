/- Lean-first (no Rocq counterpart).
# A `*walpb.Record` holding a WAL record (W3a of `notes/wal-fsext-plan.md`)

* `ownRec l r`: the `*walpb.Record` at `l` holds the record `r` as the WAL's code reads it: its
  `Type` and `Crc` (optional `*int64`/`*uint32` fields of the protobuf-go v2 message, read by
  `GetType()`/`GetCrc()`, `nil` reading as zero) and its `Data` slice, owned.
* `ownRecAny l`: the `*walpb.Record` at `l`, holding anything.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal.walpb
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open WalEnc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An optional `*T` field read by its getter: `nil` reads as zero. -/
def optPtsTo {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (x : V) : IProp GF :=
  iprop(⌜p = Loc.null ∧ x = zero_val V⌝ ∨ p ↦□ x)

instance optPtsTo_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (x : V) :
    Persistent (optPtsTo (GF := GF) p x) := by
  unfold optPtsTo; infer_instance

/-- See the file header. -/
def ownRec (l : Loc) (r : WalRec) : IProp GF :=
  iprop(∃ v : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record,
    l ↦ v ∗ optPtsTo v.Type' r.typ ∗ optPtsTo v.Crc' r.crc ∗ v.Data' ↦* r.data)

/-- See the file header. -/
def ownRecAny (l : Loc) : IProp GF :=
  iprop(∃ v : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record, l ↦ v)

theorem ownRec_any (l : Loc) (r : WalRec) : ownRec (GF := GF) l r ⊢ ownRecAny l := by
  unfold ownRec ownRecAny
  iintro ⟨%v, Hl, -⟩
  iexists v
  iexact Hl

end defs

end WalFs
end EtcdGrove
end Perennial
