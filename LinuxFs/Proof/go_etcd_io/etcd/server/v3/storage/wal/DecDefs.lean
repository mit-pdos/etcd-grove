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
* `isEofOk IoE eof ueof` (persistent): `errors.Is(e, io.EOF)` answers `e == io.EOF` on the errors a
  reader returns here (`io.EOF`, `io.ErrUnexpectedEOF`, `IoE`'s): a client obligation, from
  `errors.Is`'s spec and the error trees of `IoE`'s errors.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.bufio.Defs
public import Perennial.Proof.sync.Base
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Write
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs

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
  iprop(□ ∀ e : GoInterface, ⌜e = eof ∨ e = ueof ∨ IoE e⌝ →
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

end WalFs
end EtcdGrove
end Perennial
