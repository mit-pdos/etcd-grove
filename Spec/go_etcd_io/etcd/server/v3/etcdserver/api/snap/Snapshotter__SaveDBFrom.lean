/-
`ss.SaveDBFrom(r, id)` (`etcdserver/api/snap/db.go:37-90`; names only; rafthttp stage 7b, D42,
2026-10-24, **D22's interface**: settled by the user for the D22 owner, 2026-10-25, D42; until
stage 7 its effect was inside the snapshot handler's axiom). It copies `r` to its end into a
temporary file (`io.Copy`, which reads until a `Read` returns `io.EOF`, then fsyncs), and renames it
to the index's path (`snapDBPath ss id`), or, when a file of that index is already there, keeps
that one (D22's finding 7: both are images of the committed state at `id`). Stated over any reader
of the stream contract (`http.streamReaderOk`: the snapshot handler's body after the envelope,
`http.bodyStream`), from what has been read `r0`, the rest's complete streams images of `D`
(`boltImage`) with the certificate `□ img id D`, and the snapshot directory's invariant
(`snapDirInv`, `Proof/.../rafthttp/Net.lean`, D22 S-i): on success the rest was read to its end
(`Φ`) and the index is saved (`snapSaved`; its ghost steps on the directory: at the rename, the
index added to the files `M` with the file and to the saved `E`; nothing at a kept file). An error
reads some of it. On success the count `n` (`io.Copy`'s) is not negative (2026-10-25, stage 7e: the
handler adds it to a counter). The trust boundary (an axiom since the handler's proof, stage 7e).
Lean-first (no Rocq counterpart).

(Restart S6a, M2, 2026-11-13: the axiom review's M2; the user decided no code change) **Two saves
of one index may both rename.** `db.go` checks `fileutil.Exist(fn)` (`:57`) and renames later
(`:66`) with no lock in between, and `os.Rename` replaces an existing file, so two concurrent
`SaveDBFrom(_, i)` (two snapshot handlers of one transport, or, across a restart, the stopped
incarnation's handler and the restarted one's over one directory) can both pass the check and both
rename (`nonissues/etcd-snap-savedbfrom-concurrent-rename.md`, with the Go test). The second rename
replaces the file at `snapDBPath ss i`: one the invariant holds in `M`, one `snapDir_take`
(`SnapRO.lean`) has already handed to the apply thread to open, or, after `OpenSnapshotBackend` has
renamed that one away, none. Why the ghost steps above stay right: (1) the stored image is a function
of the index: every save at `i` streams a database whose data `D` carries the certificate
`□ img i D`, the image of the cluster's committed state at `i`, so both writers' data are the same
`D`; (2) the file claims are data-level: `fileHolds p D` says the file at `p` holds a database with
the data `D` (`fileOK`), whatever its bytes (two writers' files of the same data differ in page
layout, txid and size, which no claim records). So a rename over a file in `M`, or over the file
`snapDir_take` handed out, leaves a file at the path with the claimed data: the claim stays true
(the ghost step is the one of a kept file: nothing); and a rename after the holder moved its file
away leaves a file at an index already in `E`, which the invariant does not track (`M` lacks it,
`Rm i` holds), and nothing reads: a later save of `i` keeps it, `Release` above `i` removes it with
the files below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.net.http.Boundary
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `ss.SaveDBFrom(rd, id)` (see the file header). -/
abbrev snap.Snapshotter.SaveDBFrom.spec : Prop :=
  ∀ (ss : Loc) (rd : GoInterface) (Src : List w8 → IProp GF) (Pre Φ : List w8 → Prop)
    (e : GoInterface) (r0 : List w8) (id : w64) (D : backend.Data) (γd : GName)
    (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF),
  (∀ t, Φ (r0 ++ t) → backend.boltImage t D) →
  {{ isSnapshotter (GF := GF) ss ∗ inv snapDirN (snapDirInv ss γd img Rm) ∗
      http.streamReaderOk rd Src Pre Φ e ∗ http.ioEOF e ∗ Src r0 ∗ □ img id D }}
    (App (App (Val (ss @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!!
        go!"SaveDBFrom")) (Val #rd)) (Val #id))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); http.errStrOk err ∗
      ∃ t : List w8, Src (r0 ++ t) ∗
        (⌜err = GoInterface.nil⌝ -∗ ⌜Φ (r0 ++ t) ∧ 0 ≤ sint.Z n⌝ ∗ snapSaved γd id) }}

end spec

end EtcdGrove
end Perennial
