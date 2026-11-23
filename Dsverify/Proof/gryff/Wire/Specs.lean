/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Specs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# The specs of Gryff's `Marshal` / `Unmarshal` methods (stage 1 interface)

For every message type `T` of `GryffProof/Wire/Enc.lean` (the encodings `T.enc`, the
ownership `T.own`, the conditions `T.wf`, `T.nextOk` are there), two statements of one shape:

* `T.wp_Marshal`: `(*T).Marshal(wire)`, `wire` an `io.Writer` holding the `*bufio.Writer`
  `bw` (`Harness/Proof/bufio`). From `ownWriter bw wr J Q sent pend err`, `□ Q (sent ++ pend ++
  enc m)` (the stream with the message is allowed) and `T.own t dq m` (`t ↦{dq} m` for a type
  without a slice; any fraction), it returns `T.own t dq m` and the writer having accepted the
  first `k` bytes of `enc m`: `sent' ++ pend' = sent ++ pend ++ (enc m).take k`, all of them
  when the writer's error `err'` is `nil`, none when it already had an error (`err`, which
  sticks). This is bufio's `wp_Write` (`Writer.lean`) folded over `Marshal`'s `Write` calls
  (`Marshal` ignores their results; a failed `Write` makes the error sticky, so every later
  one accepts nothing).
* `T.wp_Unmarshal`: `(*T).Unmarshal(rr)`, `rr` an `io.Reader` holding the `*bufio.Reader`
  `br` (the slice types' `Unmarshal` type-asserts `rr` to its `byteReader`, which a
  `*bufio.Reader` is; the others call `io.ReadAtLeast` / `io.ReadFull` on `rr`). From
  `ownReader br rd I R` and `t ↦ v0`, it returns `err`: when `nil`, `t` holds a message `m`
  (`T.own t 1 m`) and the reader has returned exactly `enc m` more; otherwise an error with
  some message and well formed (`bufio.errWf`: what comparing it with `io.EOF` needs; hub
  request N-7), `t` holding some value and the reader having returned some more bytes `R'`.
  The premise `□ ∀ D, I (R ++ D) ={⊤}=∗ I (R ++ D) ∗ ⌜T.nextOk D⌝` says the bytes after `R`
  are a (prefix of a) well-formed encoding; it is `True` for every type without a slice
  (trivially discharged), and rules out a negative slice length (Go's
  `make` panics on it) for the five slice types. A connection's reader gets it from its
  protocol (`recvTok_proto`).

The package-initialization facts are those of the type's package, `bufio` (and `io` for
`Unmarshal`); the packages' `Assumptions` are section variables. The `GooseExts` are the run's
(`netConnExts`, local instances as in `GryffNetSpec.lean`), as `GryffNetSpec`'s `IsPkgInit`
instances for Gryff's packages are stated at them (with `pkgStateInst`, `GryffProof/Slots.lean`).
-/
module

public import Dsverify.Proof.gryff.Wire.Enc
public import Dsverify.Proof.gryff.Wire.Proof.Epaxos
public import Dsverify.Proof.gryff.Wire.Proof.Client
public import Dsverify.Proof.gryff.Wire.Proof.Genericsmr
public import Dsverify.Proof.gryff.Wire.Proof.Gryff2
public import Dsverify.Proof.gryff.Wire.Proof.Slices
public import Dsverify.Proof.gryff.Wire.Proof.SlicesM

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions] [encoding.binary.Assumptions] [wire.BufioSpecs GF]
variable [BinaryVarintHyps GF]
variable [src.state.Assumptions] [src.gryffproto.Assumptions] [src.epaxosproto.Assumptions]
variable [src.clientproto.Assumptions] [src.genericsmrproto.Assumptions]

namespace state

/-- `(*Key).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Key.wp_Marshal (t : Loc) (dq : DFrac) (m : Key.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Key.enc m) ∗
        Key.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Key.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Key.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Key.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Key.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Key.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Key.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Key).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Key.wp_Unmarshal (t : Loc) (v0 : src.state.Key) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Key.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.state.Key.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Key.Msg, ⌜Key.wf m⌝ ∗
          Key.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Key.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.state.Key) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Key.wp_Unmarshal_proof t v0 br rd I R

end state

namespace state

/-- `(*Value).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Value.wp_Marshal (t : Loc) (dq : DFrac) (m : Value.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Value.enc m) ∗
        Value.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Value.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Value.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Value.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Value.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Value.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Value.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Value).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Value.wp_Unmarshal (t : Loc) (v0 : src.state.Value) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Value.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.state.Value.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Value.Msg, ⌜Value.wf m⌝ ∗
          Value.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Value.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.state.Value) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Value.wp_Unmarshal_proof t v0 br rd I R

end state

namespace state

/-- `(*Command).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Command.wp_Marshal (t : Loc) (dq : DFrac) (m : Command.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Command.enc m) ∗
        Command.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.state.Command.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Command.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Command.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Command.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Command.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Command.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Command).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Command.wp_Unmarshal (t : Loc) (v0 : src.state.Command) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.state ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Command.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.state.Command.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Command.Msg, ⌜Command.wf m⌝ ∗
          Command.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Command.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.state.Command) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Command.wp_Unmarshal_proof t v0 br rd I R

end state

namespace gryffproto

/-- `(*Tag).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Tag.wp_Marshal (t : Loc) (dq : DFrac) (m : Tag.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Tag.enc m) ∗
        Tag.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Tag.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Tag.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Tag.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Tag.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Tag.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Tag).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Tag.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Tag) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Tag.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Tag.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Tag.Msg, ⌜Tag.wf m⌝ ∗
          Tag.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Tag.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Tag) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Tag.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*ValTag).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem ValTag.wp_Marshal (t : Loc) (dq : DFrac) (m : ValTag.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ValTag.enc m) ∗
        ValTag.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ValTag.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ValTag.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ValTag.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ValTag.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ValTag.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact ValTag.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*ValTag).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem ValTag.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.ValTag) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ValTag.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ValTag.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ValTag.Msg, ⌜ValTag.wf m⌝ ∗
          ValTag.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ValTag.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.ValTag) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact ValTag.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Dep).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Dep.wp_Marshal (t : Loc) (dq : DFrac) (m : Dep.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Dep.enc m) ∗
        Dep.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Dep.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Dep.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Dep.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Dep.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Dep.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Dep.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Dep).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Dep.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Dep) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Dep.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Dep.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Dep.Msg, ⌜Dep.wf m⌝ ∗
          Dep.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Dep.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Dep) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Dep.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Read).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Read.wp_Marshal (t : Loc) (dq : DFrac) (m : Read.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read.enc m) ∗
        Read.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Read.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Read).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Read.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Read) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read.Msg, ⌜Read.wf m⌝ ∗
          Read.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Read.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*ReadReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem ReadReply.wp_Marshal (t : Loc) (dq : DFrac) (m : ReadReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ReadReply.enc m) ∗
        ReadReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ReadReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ReadReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ReadReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ReadReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ReadReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact ReadReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*ReadReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem ReadReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.ReadReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ReadReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ReadReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ReadReply.Msg, ⌜ReadReply.wf m⌝ ∗
          ReadReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ReadReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.ReadReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact ReadReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Write).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Write.wp_Marshal (t : Loc) (dq : DFrac) (m : Write.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write.enc m) ∗
        Write.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Write.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Write).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Write.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Write) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write.Msg, ⌜Write.wf m⌝ ∗
          Write.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Write.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*WriteReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem WriteReply.wp_Marshal (t : Loc) (dq : DFrac) (m : WriteReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ WriteReply.enc m) ∗
        WriteReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.WriteReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (WriteReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (WriteReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (WriteReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        WriteReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact WriteReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*WriteReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem WriteReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.WriteReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R WriteReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.WriteReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : WriteReply.Msg, ⌜WriteReply.wf m⌝ ∗
          WriteReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ WriteReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.WriteReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact WriteReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*RMW).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem RMW.wp_Marshal (t : Loc) (dq : DFrac) (m : RMW.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ RMW.enc m) ∗
        RMW.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMW.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (RMW.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (RMW.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (RMW.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        RMW.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact RMW.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*RMW).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem RMW.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.RMW) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R RMW.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMW.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : RMW.Msg, ⌜RMW.wf m⌝ ∗
          RMW.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ RMW.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.RMW) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact RMW.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*RMWReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem RMWReply.wp_Marshal (t : Loc) (dq : DFrac) (m : RMWReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ RMWReply.enc m) ∗
        RMWReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMWReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (RMWReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (RMWReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (RMWReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        RMWReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact RMWReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*RMWReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem RMWReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.RMWReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R RMWReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.RMWReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : RMWReply.Msg, ⌜RMWReply.wf m⌝ ∗
          RMWReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ RMWReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.RMWReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact RMWReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Read1Proxied).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Read1Proxied.wp_Marshal (t : Loc) (dq : DFrac) (m : Read1Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read1Proxied.enc m) ∗
        Read1Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read1Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read1Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read1Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read1Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Read1Proxied.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Read1Proxied).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Read1Proxied.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Read1Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read1Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read1Proxied.Msg, ⌜Read1Proxied.wf m⌝ ∗
          Read1Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read1Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read1Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Read1Proxied.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Read1Reply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Read1Reply.wp_Marshal (t : Loc) (dq : DFrac) (m : Read1Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read1Reply.enc m) ∗
        Read1Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read1Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read1Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read1Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read1Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Read1Reply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Read1Reply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Read1Reply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Read1Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read1Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read1Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read1Reply.Msg, ⌜Read1Reply.wf m⌝ ∗
          Read1Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read1Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read1Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Read1Reply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Read2Proxied).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Read2Proxied.wp_Marshal (t : Loc) (dq : DFrac) (m : Read2Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read2Proxied.enc m) ∗
        Read2Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read2Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read2Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read2Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read2Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Read2Proxied.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Read2Proxied).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Read2Proxied.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Read2Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read2Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read2Proxied.Msg, ⌜Read2Proxied.wf m⌝ ∗
          Read2Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read2Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read2Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Read2Proxied.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Read2Reply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Read2Reply.wp_Marshal (t : Loc) (dq : DFrac) (m : Read2Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Read2Reply.enc m) ∗
        Read2Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Read2Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Read2Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Read2Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Read2Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Read2Reply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Read2Reply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Read2Reply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Read2Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Read2Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Read2Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Read2Reply.Msg, ⌜Read2Reply.wf m⌝ ∗
          Read2Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Read2Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Read2Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Read2Reply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Write1Proxied).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Write1Proxied.wp_Marshal (t : Loc) (dq : DFrac) (m : Write1Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write1Proxied.enc m) ∗
        Write1Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write1Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write1Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write1Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write1Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Write1Proxied.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Write1Proxied).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Write1Proxied.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Write1Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write1Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write1Proxied.Msg, ⌜Write1Proxied.wf m⌝ ∗
          Write1Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write1Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write1Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Write1Proxied.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Write1Reply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Write1Reply.wp_Marshal (t : Loc) (dq : DFrac) (m : Write1Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write1Reply.enc m) ∗
        Write1Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write1Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write1Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write1Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write1Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Write1Reply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Write1Reply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Write1Reply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Write1Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write1Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write1Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write1Reply.Msg, ⌜Write1Reply.wf m⌝ ∗
          Write1Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write1Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write1Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Write1Reply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Write2Proxied).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Write2Proxied.wp_Marshal (t : Loc) (dq : DFrac) (m : Write2Proxied.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write2Proxied.enc m) ∗
        Write2Proxied.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Proxied.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write2Proxied.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write2Proxied.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write2Proxied.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write2Proxied.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Write2Proxied.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Write2Proxied).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Write2Proxied.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Write2Proxied) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write2Proxied.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Proxied.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write2Proxied.Msg, ⌜Write2Proxied.wf m⌝ ∗
          Write2Proxied.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write2Proxied.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write2Proxied) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Write2Proxied.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Write2Reply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Write2Reply.wp_Marshal (t : Loc) (dq : DFrac) (m : Write2Reply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Write2Reply.enc m) ∗
        Write2Reply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Reply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Write2Reply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Write2Reply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Write2Reply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Write2Reply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Write2Reply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Write2Reply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Write2Reply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Write2Reply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Write2Reply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Write2Reply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Write2Reply.Msg, ⌜Write2Reply.wf m⌝ ∗
          Write2Reply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Write2Reply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Write2Reply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Write2Reply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*PreAccept).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem PreAccept.wp_Marshal (t : Loc) (dq : DFrac) (m : PreAccept.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAccept.enc m) ∗
        PreAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAccept.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAccept.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAccept.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAccept.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact PreAccept.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*PreAccept).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem PreAccept.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.PreAccept) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAccept.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAccept.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAccept.Msg, ⌜PreAccept.wf m⌝ ∗
          PreAccept.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAccept.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PreAccept) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact PreAccept.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*PreAcceptReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem PreAcceptReply.wp_Marshal (t : Loc) (dq : DFrac) (m : PreAcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAcceptReply.enc m) ∗
        PreAcceptReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAcceptReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAcceptReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAcceptReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAcceptReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact PreAcceptReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*PreAcceptReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem PreAcceptReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.PreAcceptReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAcceptReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAcceptReply.Msg, ⌜PreAcceptReply.wf m⌝ ∗
          PreAcceptReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAcceptReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PreAcceptReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact PreAcceptReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*EAccept).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem EAccept.wp_Marshal (t : Loc) (dq : DFrac) (m : EAccept.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ EAccept.enc m) ∗
        EAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.EAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (EAccept.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (EAccept.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (EAccept.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        EAccept.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact EAccept.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*EAccept).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem EAccept.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.EAccept) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R EAccept.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.EAccept.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : EAccept.Msg, ⌜EAccept.wf m⌝ ∗
          EAccept.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ EAccept.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.EAccept) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact EAccept.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*ECommit).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem ECommit.wp_Marshal (t : Loc) (dq : DFrac) (m : ECommit.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ECommit.enc m) ∗
        ECommit.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ECommit.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ECommit.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ECommit.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ECommit.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ECommit.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact ECommit.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*ECommit).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem ECommit.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.ECommit) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ECommit.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.ECommit.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ECommit.Msg, ⌜ECommit.wf m⌝ ∗
          ECommit.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ECommit.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.ECommit) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact ECommit.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*TryPreAccept).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem TryPreAccept.wp_Marshal (t : Loc) (dq : DFrac) (m : TryPreAccept.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ TryPreAccept.enc m) ∗
        TryPreAccept.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.TryPreAccept.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (TryPreAccept.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (TryPreAccept.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (TryPreAccept.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        TryPreAccept.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact TryPreAccept.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*TryPreAccept).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem TryPreAccept.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.TryPreAccept) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R TryPreAccept.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.TryPreAccept.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : TryPreAccept.Msg, ⌜TryPreAccept.wf m⌝ ∗
          TryPreAccept.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ TryPreAccept.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.TryPreAccept) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact TryPreAccept.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*PrepareReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem PrepareReply.wp_Marshal (t : Loc) (dq : DFrac) (m : PrepareReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PrepareReply.enc m) ∗
        PrepareReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PrepareReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PrepareReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PrepareReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PrepareReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PrepareReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact PrepareReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*PrepareReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem PrepareReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.PrepareReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PrepareReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PrepareReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PrepareReply.Msg, ⌜PrepareReply.wf m⌝ ∗
          PrepareReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PrepareReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PrepareReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact PrepareReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*Executed).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Executed.wp_Marshal (t : Loc) (dq : DFrac) (m : Executed.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Executed.enc m) ∗
        Executed.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Executed.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Executed.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Executed.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Executed.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Executed.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Executed.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Executed).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Executed.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.Executed) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Executed.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.Executed.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Executed.Msg, ⌜Executed.wf m⌝ ∗
          Executed.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Executed.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.Executed) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Executed.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*PreAcceptOKReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem PreAcceptOKReply.wp_Marshal (t : Loc) (dq : DFrac) (m : PreAcceptOKReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAcceptOKReply.enc m) ∗
        PreAcceptOKReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptOKReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAcceptOKReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAcceptOKReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAcceptOKReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAcceptOKReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact PreAcceptOKReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*PreAcceptOKReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem PreAcceptOKReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.PreAcceptOKReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAcceptOKReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.PreAcceptOKReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAcceptOKReply.Msg, ⌜PreAcceptOKReply.wf m⌝ ∗
          PreAcceptOKReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAcceptOKReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.PreAcceptOKReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact PreAcceptOKReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace gryffproto

/-- `(*AcceptOKReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem AcceptOKReply.wp_Marshal (t : Loc) (dq : DFrac) (m : AcceptOKReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ AcceptOKReply.enc m) ∗
        AcceptOKReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.AcceptOKReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (AcceptOKReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (AcceptOKReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (AcceptOKReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        AcceptOKReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact AcceptOKReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*AcceptOKReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem AcceptOKReply.wp_Unmarshal (t : Loc) (v0 : src.gryffproto.AcceptOKReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R AcceptOKReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.gryffproto.AcceptOKReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : AcceptOKReply.Msg, ⌜AcceptOKReply.wf m⌝ ∗
          AcceptOKReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ AcceptOKReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.gryffproto.AcceptOKReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact AcceptOKReply.wp_Unmarshal_proof t v0 br rd I R

end gryffproto

namespace epaxosproto

/-- `(*Prepare).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Prepare.wp_Marshal (t : Loc) (dq : DFrac) (m : Prepare.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Prepare.enc m) ∗
        Prepare.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.Prepare.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Prepare.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Prepare.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Prepare.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Prepare.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Prepare.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Prepare).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Prepare.wp_Unmarshal (t : Loc) (v0 : src.epaxosproto.Prepare) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Prepare.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.Prepare.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Prepare.Msg, ⌜Prepare.wf m⌝ ∗
          Prepare.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Prepare.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.Prepare) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Prepare.wp_Unmarshal_proof t v0 br rd I R

end epaxosproto

namespace epaxosproto

/-- `(*PreAcceptOK).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem PreAcceptOK.wp_Marshal (t : Loc) (dq : DFrac) (m : PreAcceptOK.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PreAcceptOK.enc m) ∗
        PreAcceptOK.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PreAcceptOK.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PreAcceptOK.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PreAcceptOK.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PreAcceptOK.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact PreAcceptOK.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*PreAcceptOK).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem PreAcceptOK.wp_Unmarshal (t : Loc) (v0 : src.epaxosproto.PreAcceptOK) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PreAcceptOK.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PreAcceptOK.Msg, ⌜PreAcceptOK.wf m⌝ ∗
          PreAcceptOK.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PreAcceptOK.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.PreAcceptOK) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact PreAcceptOK.wp_Unmarshal_proof t v0 br rd I R

end epaxosproto

namespace epaxosproto

/-- `(*AcceptReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem AcceptReply.wp_Marshal (t : Loc) (dq : DFrac) (m : AcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ AcceptReply.enc m) ∗
        AcceptReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.AcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (AcceptReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (AcceptReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (AcceptReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        AcceptReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact AcceptReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*AcceptReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem AcceptReply.wp_Unmarshal (t : Loc) (v0 : src.epaxosproto.AcceptReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R AcceptReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.AcceptReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : AcceptReply.Msg, ⌜AcceptReply.wf m⌝ ∗
          AcceptReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ AcceptReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.AcceptReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact AcceptReply.wp_Unmarshal_proof t v0 br rd I R

end epaxosproto

namespace epaxosproto

/-- `(*CommitShort).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem CommitShort.wp_Marshal (t : Loc) (dq : DFrac) (m : CommitShort.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ CommitShort.enc m) ∗
        CommitShort.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.CommitShort.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (CommitShort.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (CommitShort.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (CommitShort.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        CommitShort.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact CommitShort.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*CommitShort).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem CommitShort.wp_Unmarshal (t : Loc) (v0 : src.epaxosproto.CommitShort) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R CommitShort.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.CommitShort.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : CommitShort.Msg, ⌜CommitShort.wf m⌝ ∗
          CommitShort.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ CommitShort.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.CommitShort) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact CommitShort.wp_Unmarshal_proof t v0 br rd I R

end epaxosproto

namespace epaxosproto

/-- `(*TryPreAcceptReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem TryPreAcceptReply.wp_Marshal (t : Loc) (dq : DFrac) (m : TryPreAcceptReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ TryPreAcceptReply.enc m) ∗
        TryPreAcceptReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.TryPreAcceptReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (TryPreAcceptReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (TryPreAcceptReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (TryPreAcceptReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        TryPreAcceptReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact TryPreAcceptReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*TryPreAcceptReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem TryPreAcceptReply.wp_Unmarshal (t : Loc) (v0 : src.epaxosproto.TryPreAcceptReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R TryPreAcceptReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.epaxosproto.TryPreAcceptReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : TryPreAcceptReply.Msg, ⌜TryPreAcceptReply.wf m⌝ ∗
          TryPreAcceptReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ TryPreAcceptReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.epaxosproto.TryPreAcceptReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact TryPreAcceptReply.wp_Unmarshal_proof t v0 br rd I R

end epaxosproto

namespace clientproto

/-- `(*Ping).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Ping.wp_Marshal (t : Loc) (dq : DFrac) (m : Ping.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Ping.enc m) ∗
        Ping.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.Ping.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Ping.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Ping.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Ping.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Ping.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Ping.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Ping).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Ping.wp_Unmarshal (t : Loc) (v0 : src.clientproto.Ping) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Ping.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.Ping.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Ping.Msg, ⌜Ping.wf m⌝ ∗
          Ping.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Ping.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.clientproto.Ping) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Ping.wp_Unmarshal_proof t v0 br rd I R

end clientproto

namespace clientproto

/-- `(*PingReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem PingReply.wp_Marshal (t : Loc) (dq : DFrac) (m : PingReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ PingReply.enc m) ∗
        PingReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.PingReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (PingReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (PingReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (PingReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        PingReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact PingReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*PingReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem PingReply.wp_Unmarshal (t : Loc) (v0 : src.clientproto.PingReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.clientproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R PingReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.clientproto.PingReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : PingReply.Msg, ⌜PingReply.wf m⌝ ∗
          PingReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ PingReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.clientproto.PingReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact PingReply.wp_Unmarshal_proof t v0 br rd I R

end clientproto

namespace genericsmrproto

/-- `(*Beacon).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Beacon.wp_Marshal (t : Loc) (dq : DFrac) (m : Beacon.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Beacon.enc m) ∗
        Beacon.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Beacon.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Beacon.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Beacon.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Beacon.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Beacon.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Beacon.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Beacon).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Beacon.wp_Unmarshal (t : Loc) (v0 : src.genericsmrproto.Beacon) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Beacon.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Beacon.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Beacon.Msg, ⌜Beacon.wf m⌝ ∗
          Beacon.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Beacon.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.Beacon) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Beacon.wp_Unmarshal_proof t v0 br rd I R

end genericsmrproto

namespace genericsmrproto

/-- `(*BeaconReply).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem BeaconReply.wp_Marshal (t : Loc) (dq : DFrac) (m : BeaconReply.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ BeaconReply.enc m) ∗
        BeaconReply.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.BeaconReply.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (BeaconReply.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (BeaconReply.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (BeaconReply.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        BeaconReply.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact BeaconReply.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*BeaconReply).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem BeaconReply.wp_Unmarshal (t : Loc) (v0 : src.genericsmrproto.BeaconReply) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R BeaconReply.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.BeaconReply.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : BeaconReply.Msg, ⌜BeaconReply.wf m⌝ ∗
          BeaconReply.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ BeaconReply.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.BeaconReply) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact BeaconReply.wp_Unmarshal_proof t v0 br rd I R

end genericsmrproto

namespace genericsmrproto

/-- `(*Propose).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem Propose.wp_Marshal (t : Loc) (dq : DFrac) (m : Propose.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ Propose.enc m) ∗
        Propose.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Propose.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (Propose.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (Propose.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (Propose.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        Propose.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact Propose.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*Propose).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem Propose.wp_Unmarshal (t : Loc) (v0 : src.genericsmrproto.Propose) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R Propose.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.Propose.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : Propose.Msg, ⌜Propose.wf m⌝ ∗
          Propose.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ Propose.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.Propose) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact Propose.wp_Unmarshal_proof t v0 br rd I R

end genericsmrproto

namespace genericsmrproto

/-- `(*ProposeReplyTS).Marshal(wire)` on a `*bufio.Writer`: see the file header. -/
theorem ProposeReplyTS.wp_Marshal (t : Loc) (dq : DFrac) (m : ProposeReplyTS.Msg) (bw : Loc) (wr : WSt GF)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ProposeReplyTS.enc m) ∗
        ProposeReplyTS.own t dq m }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.ProposeReplyTS.ty @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
    {{ RET #(); ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
        ⌜k ≤ (ProposeReplyTS.enc m).length ∧ sent' ++ pend' = sent ++ pend ++ (ProposeReplyTS.enc m).take k ∧
          sent <+: sent' ∧ (err' = interface.nil → k = (ProposeReplyTS.enc m).length) ∧
          (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
        ProposeReplyTS.own t dq m ∗ ownWriter bw wr J Q sent' pend' err' }} := by
  exact ProposeReplyTS.wp_Marshal_proof t dq m bw wr J Q sent pend err

/-- `(*ProposeReplyTS).Unmarshal(rr)` on a `*bufio.Reader`: see the file header. -/
theorem ProposeReplyTS.wp_Unmarshal (t : Loc) (v0 : src.genericsmrproto.ProposeReplyTS) (br : Loc) (rd : RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmrproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        readerOk rd I ∗ readNext br rd I R ProposeReplyTS.nextOk ∗
        ownReader br rd I R ∗ t ↦ v0 }}
      (App (Val (t @!! go.GoType.PointerType src.genericsmrproto.ProposeReplyTS.ty @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ m : ProposeReplyTS.Msg, ⌜ProposeReplyTS.wf m⌝ ∗
          ProposeReplyTS.own t (DFrac.own 1) m ∗ ownReader br rd I (R ++ ProposeReplyTS.enc m)) ∨
        (⌜err ≠ interface.nil⌝ ∗ rdErr rd err ∗ ∃ (v : src.genericsmrproto.ProposeReplyTS) (R' : List w8),
          t ↦ v ∗ ownReader br rd I (R ++ R')) }} := by
  exact ProposeReplyTS.wp_Unmarshal_proof t v0 br rd I R

end genericsmrproto
end specs

end Perennial.gryff.wire
