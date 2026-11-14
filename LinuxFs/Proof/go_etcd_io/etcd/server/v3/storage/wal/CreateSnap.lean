/- Lean-first (no Rocq counterpart).

# `Create`'s initial snapshot record (W4, `notes/wal-fsext-plan.md`, "W4 implementation log")

`Create` saves `&walpb.Snapshot{Index: new(uint64(0)), Term: new(uint64(0))}` (S/wal.go:181) with
`SaveSnapshot`, whose spec writes `Mr.encSnap sm` for a `walSnapAt Mr sp sm cs`; the fresh WAL's
stream (`walDurFresh`, `hdrDs`) has `Mr.snap0` there. **`WalMarshalCreateOk Mr`** ties the client's
marshaller to the object: `Mr.snap0` is protobuf-go's encoding of that object (`snapEnc snapC0`) and
`Mr.encSnap` of its model the same bytes (`Create.spec`'s premise; ledger, 2026-11-14).

`walSnapAt_lit`: the literal, frozen, is `walSnapAt Mr sp snapC0.model false` (its hidden fields in
the protobuf invariant, as `encoder.encode` freezes a record).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.wal WalEnc

section pure
variable [GooseExts]

/-- **The content of `&walpb.Snapshot{Index: new(uint64(0)), Term: new(uint64(0))}`**: index and term
set to 0, no conf state, no unknown fields. -/
def snapC0 : WalSnapC := ⟨some (W64 0), some (W64 0), none, []⟩

/-- **What `Create` needs of the client's marshaller** (see the file header): the fresh WAL's snapshot
record's data `Mr.snap0` is protobuf-go's encoding of `Create`'s object, and `Mr.encSnap` of its model
gives the same bytes. -/
def WalMarshalCreateOk (Mr : WalMarshal) : Prop :=
  Mr.snap0 = snapEnc snapC0 ∧ Mr.encSnap snapC0.model = Mr.snap0

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- **The literal frozen** (see the file header). -/
theorem walSnapAt_lit (Mr : WalMarshal) (hMr : WalMarshalCreateOk Mr) (l pi pt : Loc)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32) :
    ⊢ l ↦ (walpb.Snapshot.mk st pi pt null slice.nil sc) -∗ pi ↦ W64 0 -∗ pt ↦ W64 0 ={⊤}=∗
      walSnapAt (GF := GF) Mr l snapC0.model false := by
  iintro Hl Hi Ht
  ihave ⟨Hl, %Hln⟩ := typedPointsto_not_null_dup _ _ _ $$ Hl
  iStructNamed Hl
  ipersist Index
  ipersist Term
  ipersist ConfState
  ipersist Hi
  ipersist Ht
  imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[walpb.Snapshot, go!"state"] ↦ st ∗ l.[walpb.Snapshot, go!"sizeCache"] ↦ sc ∗
      l.[walpb.Snapshot, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8))) $$ [state sizeCache unknownFields]
    with #Hinv
  · inext
    iexists st, sc, slice.nil
    iframe
    iapply ownSlice_nil
  imodintro
  iunfold walSnapAt
  iexists snapC0
  isplitl
  · iunfold snapRoC
    iexists pi, pt, null
    simp only [snapC0, recCell, walCsOptRoC, snapHidden]
    isplitr
    · ipureintro; exact Hln
    iframe #
    ipureintro; exact ufWire_nil _
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, by rw [hMr.2, hMr.1]⟩

end iris

end EtcdGrove
end Perennial
