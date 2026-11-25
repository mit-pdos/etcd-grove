/-
The package fact of `github.com/google/uuid` (its model, models/uuid; dsv-retire-2, 2026-11-25,
mit-pdos/etcd-grove#49 step 2): `True`. Translated with the bodies of `New`, `NewRandom`, `Must`,
`UUID.ID` and its variable `xvalues`, with its imports `encoding/binary` and goose's `primitive`
(`Dsverify/Code/github_com/google/uuid.toml`), so its dependencies hold their facts (`New`'s
`BigEndian.PutUint64` reads `encoding/binary`'s). Until then names only, its fact `True` written
by hand in `Init.lean`, beside the trust-boundary axiom `wp_initialize'`.
The model rests on its premise (models/README.md, `models/uuid/doc.go`): the program never assigns
`crypto/rand.Reader` and is not built with boringcrypto (then v1.3.1's `NewRandom` reads 16 bytes that
cannot fail, which the model draws from `primitive.RandomUint64`).
-/
module

public import Dsverify.GeneratedProof.github_com.google.uuid
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

/-- Slicing an array through a pointer, `Slice (ArrayType n t)`, as a step tagged `under`, so that
`go.slice_underlying` gives the step of slicing a **named** array type (`uuid[0:4]` on a `UUID`, a
`[16]byte`: `ID`, `NewRandom`). A theorem, not an assumption: the tag is only a label for instance
search, and the step is Perennial's `go.slice_array_step`. Perennial states that step untagged
(where `go.index_ref_array` is tagged `under`), so no named array can be sliced there: the general fix,
tagging it, is in `notes/perennial-changes.md` (2026-11-25). -/
instance slice_array_step_under [GooseExts] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (n : Int) (elem_type : go.GoType) (p : Loc)
    (low high : w64) {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦Slice (go.ArrayType n elem_type), (#p, #low, #high)⟧ ⤳[under]
       (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ n then
          #(slice.mk (arrayIndexRef V (sint.Z low) p) (high - low) (W64 n - low))
        else Panic "slice bounds out of range") :=
  ⟨go.slice_array_step n elem_type p low high⟩

namespace github_com.google.uuid

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.google.uuid :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.google.uuid :=
  build_get_is_pkg_init_wf

end def_

end github_com.google.uuid
end Perennial
