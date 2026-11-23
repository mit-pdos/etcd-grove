/-
**A hypothesis**: `github.com/go-redis/redis/v8`'s initializer meets Perennial's initialization spec (notes/dsv-quepaxa.md,
"Hypotheses"; dsv-vr's pattern, `Dsverify/Proof/encoding/json/Init.lean` there). `github.com/go-redis/redis/v8` is
names only in the part (benchmark mode 0: no call reaches it), its variables' initializers untranslated, so its `initialize'` cannot be proved here, and the rule is no new axiom and no trusted code:
the spec is the class `InitHyp` (a `Prop`), which every theorem whose proof initializes `github.com/go-redis/redis/v8` takes
as an instance argument (`etc/gen-init.py`'s `dsv_inits` adds the section variable, `dsv_hyp_fix`),
up to the kit's closed statement. Replace by a proved `wp_initialize'` when the package's
translation or model lands.
-/
module

public import Dsverify.Proof.github_com.go_redis.redis.v8.Base
public import Net.Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace github_com.go_redis.redis.v8

/-- **Hypothesis** (the file header): `github.com/go-redis/redis/v8`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.github_com.go_redis.redis.v8 get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.go_redis.redis.v8 }}

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- Perennial's form of `github.com/go-redis/redis/v8`'s initialization, from the hypothesis. -/
theorem wp_initialize' [h : InitHyp GF] (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.go_redis.redis.v8 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.go_redis.redis.v8 }} :=
  h.wp_init get_is_pkg_init Hinit

end init

end github_com.go_redis.redis.v8
end Perennial
