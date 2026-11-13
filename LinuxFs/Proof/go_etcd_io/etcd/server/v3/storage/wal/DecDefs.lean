/- Lean-first (no Rocq counterpart).
# The WAL decoder's vocabulary (W3a of `notes/wal-fsext-plan.md`)

The specs of `decoder.go` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`) are stated over a
decoder that reads a list of files, each through a `fileutil.FileBufReader` over a
`fileutil.FileReader` read as a stream (`io.readerStream`): the file system enters only through
each file's contract (`decFile`), which the client proves of its `*os.File` readers. The decoder's
ghost state is the pure model's (`WalEncDecoder.lean`, `goDecode`): the files left (their bytes),
`lastValidOff` and the CRC.

* `decRdErr bs eof IoE r e`: the errors a file's reader may return after delivering `r`: `io.EOF`
  at the end of the bytes `bs` only, or an I/O error of the client's set `IoE` (which the decoder
  passes on as it is).
* `fileInfoOk fi n`: the `fs.FileInfo` `fi`'s `Size()` returns `n` and its `Name()` some string.
* `decFile IoE eof F` (persistent): `F.fr` (a `fileutil.FileReader`) reads `F.bs` as the stream
  `F.S` (each state a prefix of the bytes), its `FileInfo()` returns an `IoE` error or a file info
  of size `|F.bs|`; `|F.bs| < 2^62`.
* `ownFbr fbr IoE eof F r`: the `*FileBufReader` at `fbr` over `F`, having delivered `r`.
* `ownDecoder d IoE eof fs off c live`: the `*decoder` at `d` over the files `fs` left (its
  `brs`), `lastValidOff = off`, its CRC digest at `c` (over the WAL's Castagnoli table), the mutex
  `d.mu` (guarding nothing: the decoder is owned). When `live`, the first file's reader has
  delivered exactly its first `off` bytes and the others nothing (what `Decode` needs to step as
  `goDecode`); after an error that consumed bytes (a short read, a bad frame) it is not.
* `isEofOk IoE eof ueof` (persistent): `errors.Is(e, io.EOF)` answers `e == io.EOF` on `nil` and the
  errors a reader returns here (`io.EOF`, `io.ErrUnexpectedEOF`, `IoE`'s), and `io.EOF` is neither
  `io.ErrUnexpectedEOF` nor an `IoE` error: a client obligation, from `errors.Is`'s spec, the two
  `errors.New` allocations and the error trees of `IoE`'s errors. (Without `¬ IoE io.EOF` a reader
  could end a file early with `io.EOF`, and the decoder would go on in the next file.)
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.bufio.Defs
public import Perennial.Proof.sync.Base
public import LinuxFs.Spec.fmt.ErrorfErrs
public import Perennial.Proof.encoding.binary.Base
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Write
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open WalEnc

section pure
variable [GooseExts]

/-- See the file header. -/
def decRdErr (bs : List w8) (eof : GoInterface) (IoE : GoInterface → Prop) (r : List w8)
    (e : GoInterface) : Prop :=
  (r = bs ∧ e = eof) ∨ IoE e

end pure

/-- A file the decoder reads: its `fileutil.FileReader` (an interface value), its bytes, and the
stream state of its reader (`io.readerStream`'s `S`). -/
structure DecFile [GooseExts] (GF : BundledGFunctors) where
  fr : GoInterfaceOk
  bs : List w8
  S : List w8 → IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def fileInfoOk (fi : GoInterface) (n : Nat) : IProp GF :=
  iprop(∃ fii : GoInterfaceOk, ⌜fi = GoInterface.ok fii⌝ ∗
    (□ {{ (True : IProp GF) }} (App (Val #(methods fii.ty go!"Size" fii.v)) (Val #()))
        {{ RET #(W64 n); True }}) ∗
    (□ {{ (True : IProp GF) }} (App (Val #(methods fii.ty go!"Name" fii.v)) (Val #()))
        {{ (s : GoString), RET #s; True }}))

instance fileInfoOk_persistent (fi : GoInterface) (n : Nat) :
    Persistent (fileInfoOk (GF := GF) fi n) := by
  unfold fileInfoOk; infer_instance

/-- See the file header. -/
def decFile (IoE : GoInterface → Prop) (eof : GoInterface) (F : DecFile GF) : IProp GF :=
  iprop(io.readerStream F.fr F.S (decRdErr F.bs eof IoE) ∗
    (□ ∀ r, F.S r -∗ ⌜r <+: F.bs⌝) ∗
    (□ {{ (True : IProp GF) }} (App (Val #(methods F.fr.ty go!"FileInfo" F.fr.v)) (Val #()))
        {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
            ⌜err ≠ GoInterface.nil → IoE err⌝ ∗
            (⌜err = GoInterface.nil⌝ -∗ fileInfoOk fi F.bs.length) }}) ∗
    ⌜F.fr.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty ∧ F.bs.length < 2 ^ 62⌝)

instance decFile_persistent (IoE : GoInterface → Prop) (eof : GoInterface) (F : DecFile GF) :
    Persistent (decFile IoE eof F) := by
  unfold decFile; infer_instance

variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
def ownFbr (fbr : Loc) (IoE : GoInterface → Prop) (eof : GoInterface) (F : DecFile GF)
    (r : List w8) : IProp GF :=
  iprop(∃ (b : Loc) (fi err : GoInterface),
    fbr ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err ∗
    decFile IoE eof F ∗
    bufio.ownReader b F.fr F.S (decRdErr F.bs eof IoE) r ∗
    ⌜err ≠ GoInterface.nil → IoE err⌝ ∗
    (⌜err = GoInterface.nil⌝ -∗ fileInfoOk fi F.bs.length))

/-- The CRC digest the decoder holds (`d.crc`, `crc.New(prev, crcTable)`), at `c`. -/
def ownDecCrc (h : GoInterface) (c : w32) : IProp GF :=
  iprop(∃ (l tab : Loc),
    ⌜h = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.crc.digest.ty) #l⌝ ∗
    l ↦ go_etcd_io.etcd.pkg.v3.crc.digest.mk c tab ∗ tab ↦□ hash.crc32.castagnoliTableArr)

/-- The files' readers: each at its delivered bytes (`rs`). -/
def ownFbrs (IoE : GoInterface → Prop) (eof : GoInterface) :
    List Loc → List (DecFile GF) → List (List w8) → IProp GF
  | [], [], [] => iprop(True)
  | fbr :: fbrs, F :: fs, r :: rs => iprop(ownFbr fbr IoE eof F r ∗ ownFbrs IoE eof fbrs fs rs)
  | _, _, _ => iprop(False)

theorem ownFbrs_snoc (IoE : GoInterface → Prop) (eof : GoInterface) (x : Loc) (F : DecFile GF)
    (r : List w8) :
    ∀ (fbrs : List Loc) (fs : List (DecFile GF)) (rs : List (List w8)),
    fbrs.length = fs.length → fs.length = rs.length →
    ownFbrs IoE eof fbrs fs rs ∗ ownFbr x IoE eof F r ⊢
      ownFbrs IoE eof (fbrs ++ [x]) (fs ++ [F]) (rs ++ [r])
  | [], [], [], _, _ => by
    simp only [ownFbrs, List.nil_append]
    iintro ⟨-, H⟩
    iframe
  | b :: bs, G :: gs, q :: qs, h1, h2 => by
    simp only [List.cons_append, ownFbrs]
    iintro ⟨⟨Hb, Hbs⟩, H⟩
    iframe
    iapply ownFbrs_snoc IoE eof x F r bs gs qs (by simpa using h1) (by simpa using h2)
    iframe
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | _, [], _ :: _, _, h2 => by simp at h2
  | _, _ :: _, [], _, h2 => by simp at h2

/-- What the files' readers have delivered when the decoder is live at `off`. -/
def liveRs : List (DecFile GF) → Nat → List (List w8)
  | [], _ => []
  | F :: fs, off => F.bs.take off :: fs.map (fun _ => [])

/-- See the file header. -/
def ownDecoder (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface) (fs : List (DecFile GF))
    (off : Nat) (c : w32) (live : Bool) : IProp GF :=
  iprop(∃ (sl : GoSlice) (fbrs : List Loc) (h : GoInterface) (rs : List (List w8)),
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"mu" d) (BI.pure True : IProp GF) ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"brs" d ↦ sl ∗
    sl ↦*□ fbrs ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"lastValidOff" d ↦ W64 off ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"crc" d ↦ h ∗
    structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"continueOnCrcError" d ↦ false ∗
    ownDecCrc h c ∗
    ownFbrs IoE eof fbrs fs rs ∗
    ⌜off < 2 ^ 62 ∧ (live → rs = liveRs fs off)⌝)

/-- The WAL's CRC table (`crcTable = crc32.MakeTable(crc32.Castagnoli)`, decoder.go's package
variable, wal.go:69): the Castagnoli table, read-only. -/
def walCrcTable : IProp GF :=
  iprop(∃ tab : Loc,
    globalAddr go_etcd_io.etcd.server.v3.storage.wal.crcTable ↦□ tab ∗
    tab ↦□ hash.crc32.castagnoliTableArr)

instance walCrcTable_persistent : Persistent (walCrcTable (GF := GF)) := by
  unfold walCrcTable; infer_instance

/-- See the file header. -/
def isEofOk (IoE : GoInterface → Prop) (eof ueof : GoInterface) : IProp GF :=
  iprop(⌜eof ≠ ueof ∧ ¬ IoE eof⌝ ∗
    □ ∀ e : GoInterface, ⌜e = GoInterface.nil ∨ e = eof ∨ e = ueof ∨ IoE e⌝ →
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #e)) (Val #eof))
    {{ (b : Bool), RET #b; ⌜b = decide (e = eof)⌝ }})

instance isEofOk_persistent (IoE : GoInterface → Prop) (eof ueof : GoInterface) :
    Persistent (isEofOk (GF := GF) IoE eof ueof) := by
  unfold isEofOk; infer_instance

end defs

/-! ## The errors `Decode` returns -/

section pure
variable [GooseExts]

/-- **The error `Decode` returns for a stop** (`decodeRecord`, decoder.go:88-158): `io.EOF` at the
end; `io.ErrUnexpectedEOF` itself for a short length word or frame and a torn bad record; some
non-nil error otherwise (a `fmt.Errorf` wrapping `io.ErrUnexpectedEOF` or `ErrCRCMismatch`, whose
wrapping Perennial's `Errorf` model does not keep; `proto.Unmarshal`'s error). -/
def stopErr (eof ueof : GoInterface) : WalStop → GoInterface → Prop
  | .eof, e => e = eof
  | .shortLen, e | .shortData, e | .badRec true, e => e = ueof
  | _, e => e ≠ GoInterface.nil

end pure

/-! ## What `Decode` needs and gives -/

section post
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **The decoder's environment** (persistent): the packages it calls initialized, `io.EOF` and
`io.ErrUnexpectedEOF` at `eof`/`ueof`, `errors.Is(_, io.EOF)` on the readers' errors
(`isEofOk`), the WAL's CRC table, `walpb.ErrCRCMismatch` (read by `Record.Validate`) and
protobuf's `proto` initialized (`proto.Unmarshal`). -/
def decEnv (IoE : GoInterface → Prop) (eof ueof : GoInterface) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
    isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
    globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
    globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗
    isEofOk IoE eof ueof ∗ walCrcTable ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.storage.wal.walpb.ErrCRCMismatch ↦□ GoInterface.ok e ∗
      errOk e) ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto)

instance decEnv_persistent (IoE : GoInterface → Prop) (eof ueof : GoInterface) :
    Persistent (decEnv (GF := GF) IoE eof ueof) := by
  unfold decEnv; infer_instance

/-- **What `Decode` (and `decodeRecord`) returns from the live decoder `(fs, off, c)`**: what
`goDecode` says (a record in `*rp` and the decoder live at the next frame; or the stop's error,
the decoder live only at the end), with the files left a suffix of `fs`; or an I/O error of `IoE`
(a failed `FileInfo` of the file reached, or a failed read), the decoder no longer live; or
`proto.Unmarshal` failed on a frame (`GoFail`: bytes that are no record's encoding), the decoder
no longer live and the record not given back. -/
def decPost (C : WalCodec) (d rp : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32) (err : GoInterface) : IProp GF :=
  iprop((∃ k : Nat, match goDecode C (fs.map (·.bs)) off c with
      | .ok r fs' off' c' =>
        ⌜err = GoInterface.nil ∧ (fs.drop k).map (·.bs) = fs'⌝ ∗ ownRec rp r ∗
          ownDecoder d IoE eof (fs.drop k) off' c' true
      | .stop s fs' off' c' =>
        ⌜stopErr eof ueof s err ∧ (fs.drop k).map (·.bs) = fs'⌝ ∗ ownRecAny rp ∗
          ownDecoder d IoE eof (fs.drop k) off' c' (decide (s = .eof))) ∨
    (⌜IoE err⌝ ∗ ownRecAny rp ∗
      ∃ (fs' : List (DecFile GF)) (off' : Nat) (c' : w32), ownDecoder d IoE eof fs' off' c' false) ∨
    (∃ (k : Nat) (s : WalStop) (off' : Nat) (c' : w32),
      ⌜GoFail C (fs.map (·.bs)) off c s ((fs.drop k).map (·.bs)) off' c' ∧ stopErr eof ueof s err⌝ ∗
      ownDecoder d IoE eof (fs.drop k) off' c' false))

end post

end WalFs
end EtcdGrove
end Perennial
