/-
# writerCodec's spec over remote's generalized wire (draft; `notes/etcd-dist-plan.md` §28.6)

Draft for N10a's owner (statements only, no proof; not part of any `lean_lib`). It typechecks with
`lake env lean notes/remote-wire/WriterCodec.lean` (on the VM: `vmlake env lean ...`) at branch
`etcd-safe-rwire/2026-11-26`. Adopted, `writerWire` and `writerCodec.spec` go to
`Spec/.../dist/client/writerCodec.lean` (and `writerWire` to the client's defs), `writerCall` is
`remote.Report.spec` instantiated (`remoteWriters`' per-node call), and `writerOp`'s spec becomes a
`remote.reportOp (writerWire N) P Q tok writerOp` (its owned `[]PutRec` persisted, `ownSlice_persist`).

- **The wire** `writerWire N`: an input is `(n, ps)`, `n : N` a ghost component (the orchestrator's
  adapter names, which the slot records with the input) and `ps` the Puts; a Go value `x` describes
  it when `x` is a `[]KV` interface whose slice holds `ps` read-only (`↦*□`) and whose encoding fits;
  an output `rs` (the log) likewise as a `[]PutRec`. The bytes are `enc`'s: `Int(len)`, then each
  element's fields (`Str`, `I64`).
- **The codec** `writerCodec.spec`: `writerCodec()` returns a codec meeting `wireOk` of the report
  service at that wire, for any precondition `P` and postcondition `Q`.
-/
import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs
import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Report
import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Defs

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace RWireDraft

open Iris Iris.BI Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section pure
variable [GooseExts]

abbrev wkv := github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.KV
abbrev wrec := github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.PutRec

/-- `EncIn`'s bytes: `Int(len(ps))`, then each Put's key and value. -/
def kvsBytes (ps : List wkv) : List w8 :=
  encU64 (W64 ps.length) ++ ps.flatMap (fun p => encStr p.Key' ++ encStr p.Val')

/-- `EncOut`'s bytes: `Int(len(rs))`, then each record's revision, key and value. -/
def recsBytes (rs : List wrec) : List w8 :=
  encU64 (W64 rs.length) ++ rs.flatMap (fun r => encU64 r.Rev' ++ encStr r.Key' ++ encStr r.Val')

/-- The bytes, total (a value describes only a model value whose bytes fit, `writerWire`). -/
def capped (l : List w8) : List w8 := if l.length < 2 ^ 63 then l else []

theorem capped_len (l : List w8) : (capped l).length < 2 ^ 63 := by
  unfold capped; split <;> simp_all

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [etc_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- **The writer's wire** (see the file header). -/
def writerWire (N : Type) : RWire GF (N × List wkv) (List wrec) where
  ivAt x i := iprop(∃ sl : GoSlice,
    ⌜x = interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.KV.ty) #sl ∧
      (kvsBytes i.2).length < 2 ^ 63⌝ ∗ sl ↦*□ i.2)
  ovAt v o := iprop(∃ sl : GoSlice,
    ⌜v = interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.PutRec.ty) #sl ∧
      (recsBytes o).length < 2 ^ 63⌝ ∗ sl ↦*□ o)
  ivAt_persistent _ _ := by infer_instance
  ovAt_persistent _ _ := by infer_instance
  encIn i := capped (kvsBytes i.2)
  encOut o := capped (recsBytes o)
  encIn_len _ := capped_len _
  encOut_len _ := capped_len _

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [etc_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {N : Type} [Pos.Countable (N × List wkv)] [Pos.Countable (List wrec)]

/-- **writerCodec's spec**: its codec meets the writer's wire, for any report `P`, `Q`. -/
abbrev writerCodec.spec : Prop :=
  ∀ (P : N × List wkv → IProp GF) (Q : N × List wkv → List wrec → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerCodec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd; wireOk (reportSvc (writerWire (GF := GF) N) P Q) cd }}

/-- **One writer's call** (`remoteWriters`' per node): `Report` at the writer's wire, with the Puts
`ps` of the slice `sl` (read-only) and the ghost component `n`; an answer is a `[]PutRec` slice
holding a log `rs` with `Q (n, ps) rs`. -/
abbrev writerCall.spec : Prop :=
  ∀ (P : N × List wkv → IProp GF) (Q : N × List wkv → List wrec → IProp GF) (a : GoString) (n : N)
    (sl : GoSlice) (ps : List wkv) (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec) (d : w64),
  (kvsBytes ps).length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗
      mapCtx (Gg := hG.goose_globalGS) (I := N × List wkv) ∗
      svcAddr (Gg := hG.goose_globalGS) (reportSvc (writerWire (GF := GF) N) P Q) a ∗
      wireOk (reportSvc (writerWire (GF := GF) N) P Q) cd ∗ sl ↦*□ ps ∗ P (n, ps) ∗
      budUnit (Gg := hG.goose_globalGS) a }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.Report)) (Val #a))
      (Val #(interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.KV.ty) #sl)))
      (Val #cd)) (Val #d))
  {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok); ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗
      ∃ (osl : GoSlice) (rs : List wrec),
        ⌜v = interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.PutRec.ty) #osl⌝ ∗
        osl ↦*□ rs ∗ Q (n, ps) rs) }}

end spec

end RWireDraft
end Perennial
