/-
The simp attribute of `list_seg` (`ListAuto.lean`). Declared in its own file because a
simp attribute cannot be used in the file that declares it.

* `@[seg]`: rewrite rules `list_seg` normalises with (on top of Perennial's
  `@[list_simp]` and `@[len]`). Add your own with `attribute [seg] foo`.
* `@[seg_model]`: definitions `list_seg` unfolds as a last resort (`lookup`, `ascRange`, ...).
-/
import Lean

register_simp_attr seg
register_simp_attr seg_model
