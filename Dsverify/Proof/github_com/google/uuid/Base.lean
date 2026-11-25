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
