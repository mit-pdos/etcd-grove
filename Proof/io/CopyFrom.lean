/-
**`bf.ReadFrom(fileWithoutWriteTo{f})`** in `io.CopyFiles.spec`'s copy (`File.ReadFrom`, translated; `readFrom`,
`copyFileRange`, `spliceToFile`, trusted, `TrustedCode/os.lean`): `copy_file_range` rounds (`os.wp_pollCFR`);
when they did not handle the copy, `spliceToFile` finds no poll descriptor in the source's `rawConn` and
`genericReadFrom`'s loop goes on from where they stopped (`io.wp_copyGeneric`). From the copy's state at `j`
(`io.cpS`) to its end (`io.cpFin`). Lean-first.
-/
module

public import Proof.io.CopyGeneric

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The copy's state over the `*File`s (`io.cpS`) is its state over their inner `file`s (`io.cpG`). -/
theorem io.cpS_cpG (bf f ind ins : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (j : Nat) :
    bf ↦□ os.File.mk ind ∗ f ↦□ os.File.mk ins ∗ io.cpS (GF := GF) bf f i o bs j ⊢
      io.cpG ind ins i o bs j := by
  iintro ⟨#Hb, #Hf, HS⟩
  iunfold io.cpS at HS
  icases HS with ⟨%hj, Hod, Hos, Hdst⟩
  iunfold os.ownOff at Hod Hos
  icases Hod with ⟨%ind', #Hb', Hod⟩
  icases Hos with ⟨%ins', #Hf', Hos⟩
  icombine Hb Hb' gives %h1
  icombine Hf Hf' gives %h2
  cases h1; cases h2
  iunfold io.cpG
  iframe
  ipureintro; exact hj

theorem io.cpG_cpS (bf f ind ins : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (j : Nat) :
    bf ↦□ os.File.mk ind ∗ f ↦□ os.File.mk ins ∗ io.cpG (GF := GF) ind ins i o bs j ⊢
      io.cpS bf f i o bs j := by
  iintro ⟨#Hb, #Hf, HG⟩
  iunfold io.cpG at HG
  icases HG with ⟨%hj, Hod, Hos, Hdst⟩
  iunfold io.cpS
  iunfold os.ownOff
  isplitr
  · ipureintro; exact hj
  isplitl [Hod]
  · iexists ind; iframe; iexact Hb
  isplitl [Hos]
  · iexists ins; iframe; iexact Hf
  iexact Hdst

/-- **`bf.ReadFrom(fileWithoutWriteTo{f})`** (see the file header). -/
theorem os.wp_ReadFrom_cp (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (bf f : Loc) (fdd fds : w64) (nd ns : GoString) (dd ds : OsFd) (m : OsMeta) (qm qb : DFrac)
    (bs : List ByteG) (o j : Nat)
    (hfdd : 0 ≤ fdd.toInt) (hfds : 0 ≤ fds.toInt) (hwr : dd.writable = true) (hrd : ds.readable = true)
    (hbs : bs.length = m.size) (hm : m.size < 2 ^ 61) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.os ∗
        os.ownFile bf fdd nd (DFrac.own 1) ∗ osFd fdd (DFrac.own 1) dd ∗
        os.ownFile f fds ns (DFrac.own 1) ∗ osFd fds (DFrac.own 1) ds ∗
        osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗ io.cpS bf f dd.ino o bs j }}
      (App (Val (bf @!! go.GoType.PointerType os.File.ty @!! go!"ReadFrom"))
        (Val #(interface.mkOk os.fileWithoutWriteTo.ty #(os.fileWithoutWriteTo.mk os.noWriteTo.mk f))))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile bf fdd nd (DFrac.own 1) ∗ osFd fdd (DFrac.own 1) dd ∗
        os.ownFile f fds ns (DFrac.own 1) ∗ osFd fds (DFrac.own 1) ds ∗
        osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗ io.cpFin bf f dd.ino o bs err }} := by
  wp_start as ⟨#Hinv, #Hos, Hbf, Hfdd, Hf, Hfds, Hm, Hbs, HS⟩
  iunfold os.ownFile at Hbf Hf
  icases Hbf with ⟨%ind, #Hbfp, Hdfd, #Hdn, #Hdsys⟩
  icases Hf with ⟨%ins, #Hfp, Hsfd, #Hsn, #Hssys⟩
  ihave %hbfn := typedPointsto_not_null bf _ _ $$ Hbfp
  ihave %hfn := typedPointsto_not_null f _ _ $$ Hfp
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  rw [decide_eq_false hbfn]
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  have hfwt : go.GoType.Named go!"os.fileWithoutWriteTo" [] = os.fileWithoutWriteTo.ty := by
    unfold os.fileWithoutWriteTo.ty; rfl
  rw [show (go!"os.tryLimitedReader" : GoString) = os.tryLimitedReader from rfl, os.File_ty_eq, hfwt]
  wp_func_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  rw [decide_eq_false hfn]
  try wp_auto
  ihave HG := io.cpS_cpG bf f ind ins dd.ino o bs j $$ [HS]
  · iframe; iframe #
  ihave #Hbf2 := Hbfp
  iStructNamed Hbf2
  ihave #Hf2 := Hfp
  iStructNamed Hf2
  try wp_auto
  wp_apply (os.wp_pollCFR ind ins fdd fds (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) dd ds m
    qm qb bs o j hfdd hfds hwr hrd hbs hm) $$ [Hdfd Hsfd Hfdd Hfds Hm Hbs HG]
    as %wr %h %e ⟨Hdfd, Hsfd, Hfdd, Hfds, Hm, Hbs, %j', HG, %hpost⟩
  · iframe; iframe #
  ihave HS := io.cpG_cpS bf f ind ins dd.ino o bs j' $$ [HG]
  · iframe; iframe #
  cases h
  · -- not handled: `spliceToFile`, then `genericReadFrom`
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    rw [show (go!"os.tryLimitedReader" : GoString) = os.tryLimitedReader from rfl]
    wp_func_call
    wp_call
    try wp_auto
    rw [show (go!"os.getPollFDAndNetwork" : GoString) = os.getPollFDAndNetwork from rfl]
    wp_func_call
    wp_call
    try wp_auto
    have hsc : go.typeSetContains os.fileWithoutWriteTo.ty _root_.Perennial.syscall.Conn.ty = true := by
      go_type_set
    simp only [hsc, ↓reduceIte]
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    rw [decide_eq_false hfn]
    try wp_auto
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
    try wp_auto
    wp_func_call
    wp_call
    try wp_auto
    ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
    · iPkgInit
    wp_apply (io.wp_copyGeneric wp_WriteAt bf f fdd fds nd ns dd ds m qm qb bs o j' hfdd hfds hwr hrd hbs hm)
      $$ [Hdfd Hdn Hsfd Hsn Hfdd Hfds Hm Hbs HS] as %n %err ⟨Hbf, Hfdd, Hf, Hfds, Hm, Hbs, HF⟩
    · iunfold os.ownFile
      iframe; iframe #
    iapply HΦ
    iframe
  · -- handled: `wrapErr`
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    obtain ⟨hend, he | ⟨l, rfl⟩⟩ := hpost
    · -- `nil`: the copy reached the source's end
      subst he
      try wp_auto
      iapply HΦ
      iunfold os.ownFile
      iframe; iframe #
      iapply (io.cpS_fin_end bf f dd.ino o bs j' _ (hend rfl rfl)) $$ HS
    · -- a `*SyscallError`: wrapped in a `*PathError`
      ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
      · iPkgInit
      ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
      · iPkgInit
      ihave HEOF := _root_.Perennial.io.eof_of_init $$ Hio
      iunfold errors.newVar at HEOF
      icases HEOF with ⟨%xeof, #HEOF, -⟩
      ihave ⟨%xfc, #Hefc⟩ := internal.poll.errFileClosing_of_pkgInit $$ Hpoll
      ihave ⟨%ecl, -, #Hecl⟩ := os.errClosed_of_pkgInit $$ Hos
      ihave #Hcwe := os.checkWrapErr_of_pkgInit $$ Hos
      simp only [interface.mkOk]
      try wp_auto
      wp_alloc pe as Hpe
      try wp_auto
      iapply HΦ
      iunfold os.ownFile
      iframe; iframe #
      iapply (io.cpS_fin_err bf f dd.ino o bs j' _ (by intro h; cases h)) $$ HS

end proof

end EtcdGrove
end Perennial
