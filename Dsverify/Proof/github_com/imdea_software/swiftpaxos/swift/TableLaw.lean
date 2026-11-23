/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableLaw.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift table's `Unmarshal`s with varint counts: the stream laws they read under and the
internal specs of the element decoders the message decoders call.

A generated `Unmarshal` reads a count with `readVarint` and `make`s a slice of that length (a
negative count panics). On a stream of the protocol, the reader's stream law (`sp.streamLaw`)
says what comes next is a prefix of a well-formed value's encoding (then more), so each
accepted varint is the encoding's own count (`uv_count`): an even value, a non-negative count
below `2 ^ 62`.

* `streamLaw_mono`, `streamLaw_shift`, `streamLaw_use`: weakening the law, moving its base
  past bytes read, using it;
* the laws of the element decoders: `fastAckNext` (an `MFastAck`'s body, also an element of
  `MAcks`), `ackNext` (an `Ack`, an element of `MOptAcks`), `depNext` (an `SDep`, an element of
  `MNewLeaderAckN`);
* their specs: `MFastAck.Unmarshal.specS`, `Ack.Unmarshal.specS`, `SDep.Unmarshal.specS`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableFixed
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.ProposeUnmarshal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

/-! ## Pure: counts and laws -/

/-- An accepted varint where the encoding has the count `k`: the same bytes. -/
theorem uv_count {X d w : List w8} {k : Nat} (ht : sp.uvTerm d)
    (h : X ++ d <+: X ++ sp.varintLen k ++ w) : d = sp.varintLen k := by
  obtain ⟨u, hu⟩ := h
  simp only [List.append_assoc] at hu
  have hu' := List.append_cancel_left hu
  unfold sp.varintLen at hu' ⊢
  exact (sp.cw.uvTerm_peel ht hu').1

theorem cmdIds_length (ds : List sp.CmdId) : ((ds.map sp.encCmdId).flatten).length = 8 * ds.length := by
  induction ds with
  | nil => simp
  | cons x ds ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
    simp [sp.encCmdId, sp.le32, u32Le_length]; omega

/-- What an `MFastAck` decoder reads next: an `MFastAck`'s encoding (then more). -/
def fastAckNext (d : List w8) : Prop :=
  ∃ (f : sp.FastAck) (w : List w8), f.wf ∧ d <+: f.enc ++ w

/-- What an `Ack` decoder reads next. -/
def ackNext (d : List w8) : Prop :=
  ∃ (a : sp.Ack) (w : List w8), a.wf ∧ d <+: a.enc ++ w

/-- What an `SDep` decoder reads next: a dependency list's encoding. -/
def depNext (d : List w8) : Prop :=
  ∃ (ds : List sp.CmdId) (w : List w8), sp.depWf ds ∧ d <+: sp.encDep ds ++ w

/-! ## The stream law -/

section law
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

theorem streamLaw_mono (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8) (L L' : List w8 → Prop) (h : ∀ d, L d → L' d) :
    sp.streamLaw br rd I R L ⊢ sp.streamLaw br rd I R L' := by
  unfold sp.streamLaw
  iintro #H
  imodintro
  iintro %d Hown
  icases H $$ %d Hown with ⟨Hown, %Hd⟩
  iframe Hown
  ipureintro; exact h d Hd

theorem streamLaw_shift (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R X : List w8) (L : List w8 → Prop) :
    sp.streamLaw br rd I R L ⊢ sp.streamLaw br rd I (R ++ X) (fun d => L (X ++ d)) := by
  unfold sp.streamLaw
  iintro #H
  imodintro
  iintro %d Hown
  ihave Hown : bufio.ownReader br rd I (R ++ (X ++ d)) $$ [Hown]
  · iExactEq Hown; simp
  icases H $$ %(X ++ d) Hown with ⟨Hown, %Hd⟩
  isplitl [Hown]
  · iExactEq Hown; simp
  ipureintro; exact Hd

theorem streamLaw_use (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R d : List w8) (L : List w8 → Prop) :
    sp.streamLaw br rd I R L ∗ bufio.ownReader br rd I (R ++ d) ⊢
      bufio.ownReader br rd I (R ++ d) ∗ ⌜L d⌝ := by
  unfold sp.streamLaw
  iintro ⟨#H, Hown⟩
  iapply H $$ %d Hown

end law

/-! ## The element decoders' specs -/

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- The persistent facts a varint-reading `Unmarshal` uses: the packages, and
`errVarintOverflow` (non-nil). -/
def ctxV : IProp netDistGF :=
  iprop(isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
    isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
    isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.binary ∗
    ∃ ov : GoInterface, typedPointsto (globalAddr swift.errVarintOverflow) ov DFrac.discard ∗
      ⌜ov ≠ interface.nil⌝)

instance ctxV_persistent : Persistent (ctxV (hG := hG)) := by
  unfold ctxV; infer_instance

/-- `(*MFastAck).Unmarshal(br)` on a `*bufio.Reader` whose next bytes are an `MFastAck`'s
encoding: without an error, the bytes read are a well-formed `f`'s, which `t` holds (its
slices owned). -/
abbrev MFastAck.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MFastAck) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R fastAckNext ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MFastAck.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (f : sp.FastAck) (dsl csl : GoSlice),
          ⌜data = f.enc ∧ f.wf⌝ ∗
          t ↦ swift.MFastAck.mk f.rep f.bal (ofCmdId f.id) dsl csl f.seqnum ∗
          dsl ↦* f.dep.map ofCmdId ∗ csl ↦* f.cs.map swift.handler.shashOf) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MFastAck, t ↦ v')) }}

/-- `(*Ack).Unmarshal(br)` (an `MOptAcks` element). -/
abbrev Ack.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.Ack) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R ackNext ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.Ack.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (a : sp.Ack) (dsl csl : GoSlice),
          ⌜data = a.enc ∧ a.wf⌝ ∗
          t ↦ swift.Ack.mk (ofCmdId a.id) dsl csl a.seqnum ∗
          dsl ↦* a.dep.map ofCmdId ∗ csl ↦* a.cs.map swift.handler.shashOf) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.Ack, t ↦ v')) }}

/-- `(*SDep).Unmarshal(br)` (an `MNewLeaderAckN` element). -/
abbrev SDep.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.SDep) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R depNext ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.SDep.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (ds : List sp.CmdId) (dsl : GoSlice),
          ⌜data = sp.encDep ds ∧ sp.depWf ds⌝ ∗
          t ↦ swift.SDep.mk dsl ∗ dsl ↦* ds.map ofCmdId) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.SDep, t ↦ v')) }}

/-- `newFastAck()` (the statement of the coordinator's `swift.newFastAck.specP`, branch
prove-swc, Proof/swift/PoolFns.lean, until the merge): a fresh `*MFastAck`, whether the pool is
on (`v`) or not. -/
abbrev newFastAck.specP' [SwiftNetPkgState netDistGF] [swift.Assumptions] : Prop :=
  ∀ v : Bool,
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      typedPointsto (globalAddr swift.useFastAckPool) v DFrac.discard }}
    (App (Val (@! swift.newFastAck)) (Val #()))
  {{ (l : Loc), RET #l; ∃ fa : swift.MFastAck, l ↦ fa }}

end specs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
