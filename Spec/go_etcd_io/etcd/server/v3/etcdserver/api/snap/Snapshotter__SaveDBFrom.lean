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
