/-
**`io.CopyFiles.spec`** (`Spec/io/CopyFiles.lean`): `io.Copy(bf, lf)` of an `*os.File` destination and a
`*fileutil.LockedFile` source, proved over Perennial's `io.Copy`/`copyBuffer`, this repository's `os`
(translated: `File.WriteTo`, `writeTo`, `genericWriteTo`, `File.ReadFrom`, ...; trusted: `readFrom`,
`copyFileRange`, `spliceToFile`, `model.copyFileRangeRound`, `TrustedCode/os.lean`) and the extension's
read and write: the source's promoted `WriteTo` finds no `sendfile` destination (`bf`'s `rawConn` has no
poll descriptor), `genericWriteTo` copies into `bf`'s `ReadFrom` (`os.wp_ReadFrom_cp`: `copy_file_range`
rounds, then `genericReadFrom`'s loop). Takes `File.WriteAt`'s spec of any length (the loop's `File.Write`).
Lean-first.
-/
module

public import Spec.io.CopyFiles
public import Proof.io.CopyFrom

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- The new destination (`O_TRUNC`'s `trFile i True`) is the copy's at `0`. -/
theorem io.trFile_copyDst (i : Ino) :
    trFile (GF := GF) i True ⊢ io.copyDst i (· = []) := by
  unfold trFile
  iintro ⟨%m, %xs, Hm, Hb, -, %h⟩
  obtain ⟨hl, h0, hmaps, hcut, hlo, hz, -⟩ := h
  have hx : xs = [] := List.eq_nil_of_length_eq_zero (by rw [hl, h0 trivial])
  iapply (io.copyDst_intro i _ m xs ⟨hmaps, hcut, hlo, hz⟩ hl (by rw [hx]; rfl)) $$ [Hm Hb]
  iframe

theorem io.CopyFiles.wp_proof (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG)) :
    io.CopyFiles.spec (GF := GF) (hG := hG) := by
  intro bf fdd nd dd lf f fds ns ds o qm qb m bs hwr hrd hfdd hfds ho0 hob hbs hm
  wp_start as ⟨#Hinv, #Hos, Hbf, Hfdd, Hbo, Htr, #Hlf, Hf, Hfds, Hfo, Hm, Hbs⟩
  iunfold os.ownFile at Hbf Hf
  icases Hbf with ⟨%ind, #Hbfp, Hdfd, #Hdn⟩
  icases Hf with ⟨%ins, #Hfp, Hsfd, #Hsn⟩
  ihave %hbfn := typedPointsto_not_null bf _ _ $$ Hbfp
  ihave %hfn := typedPointsto_not_null f _ _ $$ Hfp
  iunfold fileutil.lockedFile at Hlf
  ihave #Hlf2 := Hlf
  iStructNamed Hlf2
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  have hwt : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty)
      _root_.Perennial.io.WriterTo.ty = true := by
    go_type_set
  simp only [hwt, ↓reduceIte]
  wp_auto
  wp_method_call
  wp_call
  try wp_auto
  -- `File.WriteTo`: `checkValid`, then `writeTo`
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  rw [decide_eq_false hfn]
  wp_auto
  wp_method_call
  wp_call
  try wp_auto
  -- `getPollFDAndNetwork(bf)`: `bf`'s `rawConn` has no poll descriptor
  wp_func_call
  wp_call
  try wp_auto
  have hsc : go.typeSetContains (go.GoType.PointerType os.File.ty) _root_.Perennial.syscall.Conn.ty = true := by
    go_type_set
  simp only [hsc, ↓reduceIte]
  wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  rw [decide_eq_false hbfn]
  wp_auto
  wp_func_call
  wp_call
  try wp_auto
  have hpfd : go.typeSetContains (go.GoType.PointerType os.rawConn.ty)
      (go.GoType.InterfaceType [go.InterfaceElem.MethodElem go!"Network"
          (go.signature.Signature [] false [_root_.Perennial.internal.poll.String.ty]),
        go.InterfaceElem.MethodElem go!"PollFD"
          (go.signature.Signature [] false [go.GoType.PointerType _root_.Perennial.internal.poll.FD.ty])]) =
      false := by
    go_type_set
  simp only [hpfd]
  wp_auto
  rw [show (zero_val Bool) = false from rfl]
  wp_auto
  -- `genericWriteTo(f, bf)`: `io.Copy(bf, fileWithoutWriteTo{f})`, which calls `bf.ReadFrom`
  wp_func_call
  wp_call
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  have hwt2 : go.typeSetContains os.fileWithoutWriteTo.ty _root_.Perennial.io.WriterTo.ty = false := by
    go_type_set
  have hrf : go.typeSetContains (go.GoType.PointerType os.File.ty) _root_.Perennial.io.ReaderFrom.ty = true := by
    go_type_set
  simp only [hwt2]
  wp_auto
  simp only [hrf, ↓reduceIte]
  wp_auto
  rw [show (zeroValDef : os.noWriteTo) = os.noWriteTo.mk from rfl]
  have hoN : W64 ((o.toNat : Int) + ((0 : Nat) : Int)) = o := by
    rw [show ((0 : Nat) : Int) = 0 from rfl, Int.add_zero]; word
  ihave HS : io.cpS bf f dd.ino o.toNat bs 0 $$ [Hbo Hfo Htr]
  · iunfold io.cpS
    rw [hoN]
    ihave Hd := io.trFile_copyDst dd.ino $$ Htr
    unfold named
    rw [show ((0 : Nat) : Int) = 0 from rfl]
    iframe
    ipureintro; omega
  wp_apply (os.wp_ReadFrom_cp wp_WriteAt bf f fdd fds nd ns dd ds m qm qb bs o.toNat 0 hfdd hfds hwr hrd
    hbs hm) $$ [Hdfd Hsfd Hfdd Hfds Hm Hbs HS] as %n %err ⟨Hbf, Hfdd, Hf, Hfds, Hm, Hbs, HF⟩
  · iunfold os.ownFile
    iframe; iframe #
  iapply HΦ
  iunfold io.cpFin at HF
  iframe

end proof

end EtcdGrove
end Perennial
