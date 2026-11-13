/-
**The `os.File`-reader bridge** (W3/W5 of `notes/wal-fsext-plan.md`, branch `wal-read5`): a
`*fileutil.fileReader{f}` (what `openWALFiles` makes of each segment it opens), with the stream
state `walFileS f fd name fl g` (`ReadDefs.lean`: the file, the fd, its offset, the program's halves
of the segment `g`'s `OsMeta` and bytes), satisfies the decoder's file contract `decFile`
(`DecDefs.lean`) for the segment's bytes, given:
* the errors `IoE` the decoder may see hold of every pointer error (`Read`'s `*PathError`, `Stat`'s
  error);
* the segment at rest: its size its bytes' length (`g.om.size = |g.bs|`), and the bound of `decFile`;
* the fd readable, of the segment's inode, non-negative;
* `os.File.Stat`'s, `fileStat.Size`'s and `fileStat.Name`'s specs (the last a hypothesis the model
  cannot discharge: `LinuxFs/Spec/os/fileStat__Name.lean`).
`Read` is `os.File.Read.wp_eof` (`LinuxFs/Proof/os/ReadEof.lean`): what it delivers is the bytes
from the offset on, and `io.EOF` comes only at the end.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.os.ReadEof
public import LinuxFs.Spec.os.File__Stat
public import LinuxFs.Spec.os.fileStat__Size
public import LinuxFs.Spec.os.fileStat__Name

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem os.ownFileStat_persist (fs : Loc) (sz : w64) :
    os.ownFileStat (GF := GF) fs sz ⊢ □ os.ownFileStat (GF := GF) fs sz := by
  unfold os.ownFileStat
  iintro ⟨#H1, ⟨%m, #H2⟩, %nm, #H3⟩
  imodintro
  iframe H1
  isplitl []
  · iexists m; iexact H2
  iexists nm
  iexact H3

/-- The decoder's file of a segment `g` read through the `*fileReader` at `rl`. -/
def walDecFile (rl f : Loc) (fd : w64) (name : GoString) (fl : OsFd) (g : SegG) : DecFile GF :=
  ⟨⟨go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty, #rl⟩,
    g.bs.map Prod.fst, walFileS f fd name fl g⟩

/-- See the file header. -/
theorem walDecFile_ok
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_Name : os.fileStat.Name.spec (GF := GF) (hG := hG))
    (IoE : GoInterface → Prop) (hIo : ∀ ii, _root_.Perennial.errors.IsPointerError ii → IoE (GoInterface.ok ii))
    (eof : GoInterface) (rl f : Loc) (fd : w64) (name : GoString) (fl : OsFd) (g : SegG)
    (hfd : 0 ≤ fd.toInt) (hino : fl.ino = g.ino) (hrd : fl.readable = true)
    (hsz : g.om.size = g.bs.length) (hlen : g.bs.length + 2 ^ 12 < 2 ^ 62) :
    osInv (GF := GF) ∗ globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
      rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ⊢
      decFile IoE eof (walDecFile rl f fd name fl g) := by
  iintro ⟨#Hinv, #Heof, #Hrl⟩
  iunfold decFile
  simp only [walDecFile]
  isplitr
  · iunfold io.readerStream
    imodintro
    iintro %r %p %xs
    imodintro
    iintro %Φ ⟨%Hrx, HS, Hp⟩ HΦ
    iunfold walFileS at HS
    icases HS with ⟨%Hpre, Hf, Hfd, Ho, Hm, Hbs⟩
    ihave #Hrl2 := Hrl
    iStructNamed Hrl2
    wp_method_call
    wp_call
    try wp_auto
    rw [← hino]
    have hrl : r.length ≤ g.bs.length := by
      have := Hpre.length_le; simp only [List.length_map] at this; exact this
    have hor : (W64 (r.length : Int)).toNat = r.length := by
      simp only [BitVec.toNat_ofInt]; omega
    have hoi : (W64 (r.length : Int)).toInt = r.length := by
      rw [BitVec.toInt_eq_toNat_cond, hor]; split <;> omega
    wp_apply os.File.Read.wp_eof f fd name (DFrac.own 1) p xs (W64 (r.length : Int)) (DFrac.own 1)
        (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) fl g.om g.bs eof hfd hrd
        (by rw [hoi]; omega) hsz.symm (by rw [hoi]; omega)
      $$ [Hf Hfd Hm Hbs Ho Hp] as %n %err ⟨Hf, Hfd, Hm, Hbs, %k, %Hk, Hp, Ho, Hcase⟩
    · iframe; isplitl [] <;> iassumption
    rw [hor] at Hk; rw [hor]
    obtain ⟨hn, hkx, hkb⟩ := Hk
    subst hn
    have hyl : (((g.bs.map Prod.fst).drop r.length).take k).length = k := by
      simp only [List.length_take, List.length_drop, List.length_map]; omega
    have hrys : r ++ ((g.bs.map Prod.fst).drop r.length).take k = (g.bs.map Prod.fst).take (r.length + k) := by
      rw [List.take_add, ← List.prefix_iff_eq_take.1 Hpre]
    have hoff : W64 (r.length : Int) + W64 (k : Int) =
        W64 ((r ++ ((g.bs.map Prod.fst).drop r.length).take k).length : Int) := by
      rw [List.length_append, hyl]; push_cast; word
    have hpure : sint.Z (W64 (k : Int)) = (k : Int) := by
      simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
    ihave %Hc : ⌜err = GoInterface.nil ∨ (k = 0 ∧ g.bs.length ≤ r.length ∧ err = eof) ∨
        (∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)⌝ $$ [Hcase]
    · icases Hcase with (%h | %h | ⟨-, %pe, %hpe, -⟩)
      · ipureintro; exact .inl h.1
      · ipureintro; exact .inr (.inl ⟨h.1, h.2.2.1, h.2.2.2⟩)
      · ipureintro; exact .inr (.inr ⟨pe, hpe⟩)
    iapply HΦ
    iexists ((g.bs.map Prod.fst).drop r.length).take k
    rw [hyl, hoff]
    iframe Hp
    isplitr
    · ipureintro
      refine ⟨hpure, hkx, ?_⟩
      intro hne
      rcases Hc with h | ⟨rfl, hle, rfl⟩ | ⟨pe, rfl⟩
      · exact absurd h hne
      · left
        refine ⟨?_, rfl⟩
        simp only [List.take_zero, List.append_nil]
        exact Hpre.eq_of_length (by simp only [List.length_map]; omega)
      · right
        unfold interface.mkOk
        exact hIo _ ⟨_, pe, rfl, rfl⟩
    iunfold walFileS
    rw [← hino]
    iframe
    ipureintro
    rw [hrys]; exact List.take_prefix _ _
  isplitr
  · imodintro
    iintro %r HS
    iunfold walFileS at HS
    icases HS with ⟨%Hpre, -⟩
    ipureintro; exact Hpre
  isplitr
  · imodintro
    iintro %r
    imodintro
    iintro %Φ HS HΦ
    iunfold walFileS at HS
    icases HS with ⟨%Hpre, Hf, Hfd, Ho, Hm, Hbs⟩
    ihave #Hrl2 := Hrl
    iStructNamed Hrl2
    wp_method_call
    wp_call
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    rw [← hino]
    wp_apply wp_Stat f fd name (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half) fl g.om
      $$ [Hf Hfd Hm] as %fi %err ⟨Hf, Hfd, Hm, Hres, -, %Hptr⟩
    · iframe; iexact Hinv
    try wp_auto
    iapply HΦ
    isplitl [Hf Hfd Ho Hm Hbs]
    · iunfold walFileS; rw [← hino]; iframe; ipureintro; exact Hpre
    icases Hres with (⟨%fs, %Hok, Hfs⟩ | %Herr)
    · obtain ⟨rfl, rfl⟩ := Hok
      ihave #Hfs := os.ownFileStat_persist fs _ $$ Hfs
      isplitr
      · ipureintro; intro h; exact absurd rfl h
      iintro -
      iunfold fileInfoOk
      iexists _
      isplitr
      · ipureintro; rfl
      isplitr
      · imodintro
        iintro %Φ'
        imodintro
        iintro - HΦ'
        wp_apply wp_Size $$ Hfs as -
        rw [hsz, ← List.length_map (f := Prod.fst)]
        iapply HΦ'
        ipureintro; trivial
      · imodintro
        iintro %Φ'
        imodintro
        iintro - HΦ'
        wp_apply wp_Name $$ Hfs as %s -
        iapply HΦ'
        ipureintro; trivial
    · obtain ⟨hne, rfl⟩ := Herr
      isplitr
      · ipureintro
        intro _
        cases err with
        | nil => exact absurd rfl hne
        | ok ii => exact hIo ii (Hptr ii rfl)
      iintro %h
      exact absurd h hne
  ipureintro
  refine ⟨?_, by simp only [List.length_map]; exact hlen⟩
  intro h
  injection h with h
  unfold go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty _root_.Perennial.bufio.Reader.ty at h
  injection h with h
  revert h; decide

end bridge

end WalFs
end EtcdGrove
end Perennial
